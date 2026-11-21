/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import Batteries.Data.Float.Basic
public import Batteries.Data.Float.Bits

/-!
# Scalar helpers for single-precision complex floats

The `Float32` versions of the helpers in `BatteriesComplexFloat.Float`: functions on `Float32`
that the complex functions need and that Lean core does not provide.
They are written in terms of core operations that have a logical model (`Float32.Model`):
bit casts, `+`, `-`, `*`, `/`, `fma` and `sqrt`. The exceptions are `mulExpLarge` and `log1p`,
which call `exp` and `log`.

## References

* [IEEE754] *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019.
* [musl] musl libc, `src/math/scalbnf.c`.
* [Borges2020] C. F. Borges, *Algorithm 1014: An Improved Algorithm for `hypot(x, y)`*,
  ACM Transactions on Mathematical Software 47 (2020), no. 1, Article 9,
  doi:10.1145/3428446; preprint arXiv:1904.09481.
* [FreeBSD] FreeBSD msun library: `lib/msun/src/k_expf.c` (`__ldexp_cexpf`).
* [Goldberg1991] D. Goldberg, *What Every Computer Scientist Should Know About
  Floating-Point Arithmetic*, ACM Computing Surveys 23 (1991), no. 1, 5–48, Theorem 4.
-/

namespace Float32

/-- `2 ^ n` for `-126 ≤ n ≤ 127`, built from its bit pattern. -/
@[expose, inline] public def twoPow (n : Int) : Float32 :=
  .ofBits ((n + 127).toNat.toUInt32 <<< 23)

/--
The unbiased exponent of `x`, that is the integer `e` with `2 ^ e ≤ |x| < 2 ^ (e + 1)`, or
`none` when `x` is zero, infinite or NaN. Subnormal numbers get their true exponent. This is
`logB` of [IEEE754, 5.3.3] on finite non-zero numbers.
-/
@[expose] public def exponent? (x : Float32) : Option Int :=
  let e := (x.toBits >>> 23) &&& 0xFF
  if e == 0xFF then none
  else if e == 0 then
    if x == 0 then none
    else some ((((x * twoPow 25).toBits >>> 23) &&& 0xFF).toNat - 152)
  else some (e.toNat - 127)

/--
`x * 2 ^ n`, rounded once: `scaleB` of [IEEE754, 5.3.3] and the C function `scalbn`, written
with model arithmetic only (core's `Float32.scaleB` is an opaque external function). The steps
are those of [musl].
-/
@[expose] public def ldexp (x : Float32) (n : Int) : Float32 :=
  -- Same steps as musl's `scalbn`: no step but the last one can round.
  if n > 127 then
    let x := x * twoPow 127
    let n := n - 127
    if n > 127 then
      x * twoPow 127 * twoPow (min (n - 127) 127)
    else x * twoPow n
  else if n < -126 then
    -- Scale by `2 ^ (-126 + 24)` so that the final step lands well inside the subnormal range
    -- and rounds only once.
    let x := x * twoPow (-102)
    let n := n + 102
    if n < -126 then
      x * twoPow (-102) * twoPow (max (n + 102) (-126))
    else x * twoPow n
  else x * twoPow n

/--
The rounding error `p q - fl(p q)` of a product, computed exactly with a fused multiply-add when
`p q` neither underflows nor overflows. It is infinite or NaN when `p q` overflows.
-/
@[expose] public def mulErr (p q : Float32) : Float32 := fma p q (-(p * q))

/--
`sqrt (a * a + b * b)` for `a ≥ b ≥ 0` in a range where the squares neither overflow nor
underflow, with the fused multiply-add correction step of [Borges2020], which makes the result
correctly rounded in almost all cases.
-/
@[expose] public def hypotCore (a b : Float32) : Float32 :=
  let h := sqrt (fma a a (b * b))
  let hh := h * h
  let aa := a * a
  let x := fma (-b) b (hh - aa) + mulErr h h - mulErr a a
  h - x / (2 * h)

/--
`sqrt (x * x + y * y)` without undue overflow or underflow. As in C, the result is `inf` when
either argument is infinite, even if the other one is NaN ([IEEE754, 9.2], C's `hypot`).
The arguments are scaled by powers of two outside `[2⁻⁵⁰, 2⁵⁰]` and the core computation
is `hypotCore`.
-/
@[expose] public def hypot (x y : Float32) : Float32 :=
  if x.isInf || y.isInf then inf
  else if x.isNaN || y.isNaN then nan
  else
    let x := x.abs
    let y := y.abs
    let a := if x < y then y else x
    let b := if x < y then x else y
    if a == 0 then 0
    else if a > twoPow 50 then
      hypotCore (a * twoPow (-90)) (b * twoPow (-90)) * twoPow 90
    else if a < twoPow (-50) then
      hypotCore (a * twoPow 90) (b * twoPow 90) * twoPow (-90)
    else hypotCore a b

/--
`c * exp x * 2 ^ k` for `x > 88.7`, where `exp x` overflows but the result may not. As in
`__ldexp_cexpf` of [FreeBSD], this uses `exp x = exp (x - k₀ * log 2) * 2 ^ k₀` with
`k₀ = 235`, a value for which `k₀ * log 2` rounds with an unusually small error. Both factors
are normalized to `[1, 2)` before they are multiplied, so that the result is rounded only twice.
-/
public def mulExpLarge (c x : Float32) (k : Int := 0) : Float32 :=
  let m := exp (x - 162.88958740)
  match m.exponent?, c.exponent? with
  | some e, some e' => ldexp (ldexp c (-e') * ldexp m (-e)) (e + e' + k + 235)
  | _, _ => c * m

/-- `log (1 + x)`, accurate also when `x` is small, by the method of [Goldberg1991, Theorem 4]
(due to Kahan): `log (1 + x) = x * log u / (u - 1)` with `u = 1 + x` rounded. -/
@[expose] public def log1p (x : Float32) : Float32 :=
  -- The rounding error of `1 + x` cancels out in `x / (u - 1)`.
  let u := 1 + x
  if u == 1 || x.isInf then x
  else log u * (x / (u - 1))

end Float32
