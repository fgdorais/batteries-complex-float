/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import Batteries.Data.Float

/-!
# Scalar helpers for complex floats

Functions on `Float` that the complex functions need and that Lean core does not provide.
They are written in terms of core operations that have a logical model (`Float.Model`):
bit casts, `+`, `-`, `*`, `/`, `fma` and `sqrt`. The exceptions are `mulExpLarge` and `log1p`,
which call `exp` and `log`.

## References

* [IEEE754] *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019.
* [musl] musl libc, `src/math/scalbn.c`.
* [Borges2020] C. F. Borges, *Algorithm 1014: An Improved Algorithm for `hypot(x, y)`*,
  ACM Transactions on Mathematical Software 47 (2020), no. 1, Article 9,
  doi:10.1145/3428446; preprint arXiv:1904.09481.
* [FreeBSD] FreeBSD msun library: `lib/msun/src/k_exp.c` (`__ldexp_cexp`) and
  `lib/msun/src/s_ctanh.c`.
* [Goldberg1991] D. Goldberg, *What Every Computer Scientist Should Know About
  Floating-Point Arithmetic*, ACM Computing Surveys 23 (1991), no. 1, 5–48, Theorem 4.
-/

namespace Float

/-- The sign bit of `x`: `true` for negative numbers and `-0` (`isSignMinus` of [IEEE754, 5.7.2]).
Lean's NaN is canonical, with sign bit clear. -/
@[expose, inline] public def signBit (x : Float) : Bool :=
  x.toBits >>> 63 == 1

/-- The float with the magnitude of `x` and the sign bit of `y` (`copySign` of
[IEEE754, 5.5.1]). -/
@[expose, inline] public def copySign (x y : Float) : Float :=
  .ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))

/-- `2 ^ n` for `-1022 ≤ n ≤ 1023`, built from its bit pattern. -/
@[expose, inline] public def twoPow (n : Int) : Float :=
  .ofBits ((n + 1023).toNat.toUInt64 <<< 52)

/--
The unbiased exponent of `x`, that is the integer `e` with `2 ^ e ≤ |x| < 2 ^ (e + 1)`, or
`none` when `x` is zero, infinite or NaN. Subnormal numbers get their true exponent. This is
`logB` of [IEEE754, 5.3.3] on finite non-zero numbers.
-/
@[expose] public def exponent? (x : Float) : Option Int :=
  let e := (x.toBits >>> 52) &&& 0x7FF
  if e == 0x7FF then none
  else if e == 0 then
    if x == 0 then none
    else some ((((x * twoPow 54).toBits >>> 52) &&& 0x7FF).toNat - 1077)
  else some (e.toNat - 1023)

/--
`x * 2 ^ n`, rounded once: `scaleB` of [IEEE754, 5.3.3] and the C function `scalbn`, written
with model arithmetic only (core's `Float.scaleB` is an opaque external function). The steps
are those of [musl].
-/
@[expose] public def ldexp (x : Float) (n : Int) : Float :=
  -- Same steps as musl's `scalbn`: no step but the last one can round.
  if n > 1023 then
    let x := x * twoPow 1023
    let n := n - 1023
    if n > 1023 then
      x * twoPow 1023 * twoPow (min (n - 1023) 1023)
    else x * twoPow n
  else if n < -1022 then
    -- Scale by `2 ^ (-1022 + 53)` so that the final step lands well inside the subnormal range
    -- and rounds only once.
    let x := x * twoPow (-969)
    let n := n + 969
    if n < -1022 then
      x * twoPow (-969) * twoPow (max (n + 969) (-1022))
    else x * twoPow n
  else x * twoPow n

/--
`sqrt (a * a + b * b)` for `a ≥ b ≥ 0` in a range where the squares neither overflow nor
underflow, with the fused multiply-add correction step of [Borges2020], which makes the result
correctly rounded in almost all cases.
-/
@[expose] public def hypotCore (a b : Float) : Float :=
  let h := sqrt (fma a a (b * b))
  let hh := h * h
  let aa := a * a
  let x := fma (-b) b (hh - aa) + fma h h (-hh) - fma a a (-aa)
  h - x / (2 * h)

/--
`sqrt (x * x + y * y)` without undue overflow or underflow. As in C, the result is `inf` when
either argument is infinite, even if the other one is NaN ([IEEE754, 9.2], C's `hypot`).
The arguments are scaled by powers of two outside `[2⁻⁵⁰⁰, 2⁵⁰⁰]` and the core computation is
`hypotCore`.
-/
@[expose] public def hypot (x y : Float) : Float :=
  if x.isInf || y.isInf then inf
  else if x.isNaN || y.isNaN then nan
  else
    let x := x.abs
    let y := y.abs
    let a := if x < y then y else x
    let b := if x < y then x else y
    if a == 0 then 0
    else if a > twoPow 500 then
      hypotCore (a * twoPow (-600)) (b * twoPow (-600)) * twoPow 600
    else if a < twoPow (-500) then
      hypotCore (a * twoPow 600) (b * twoPow 600) * twoPow (-600)
    else hypotCore a b

/--
`c * exp x * 2 ^ k` for `x > 709`, where `exp x` overflows but the result may not. As in
`__ldexp_cexp` of [FreeBSD], this uses `exp x = exp (x - k₀ * log 2) * 2 ^ k₀` with `k₀ = 1799`, a
value for which `k₀ * log 2` rounds with an unusually small error. Both factors are normalized
to `[1, 2)` before they are multiplied, so that the result is rounded only twice.
-/
public def mulExpLarge (c x : Float) (k : Int := 0) : Float :=
  let m := exp (x - 1246.97177782734161156)
  match m.exponent?, c.exponent? with
  | some e, some e' => ldexp (ldexp c (-e') * ldexp m (-e)) (e + e' + k + 1799)
  | _, _ => c * m

/-- `log (1 + x)`, accurate also when `x` is small, by the method of [Goldberg1991, Theorem 4]
(due to Kahan): `log (1 + x) = x * log u / (u - 1)` with `u = 1 + x` rounded. -/
@[expose] public def log1p (x : Float) : Float :=
  -- The rounding error of `1 + x` cancels out in `x / (u - 1)`.
  let u := 1 + x
  if u == 1 || x.isInf then x
  else log u * (x / (u - 1))

end Float
