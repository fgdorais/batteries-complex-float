/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.ComplexFloat32.Basic

/-!
# Hyperbolic and trigonometric functions

The hyperbolic functions follow the special values of Annex G of the C standard (G.6.2), and
the trigonometric functions are defined from them as in G.6:
`sin z = -I * sinh (I * z)`, `cos z = cosh (I * z)` and `tan z = -I * tanh (I * z)`.

## References

* [C17] ISO/IEC 9899:2018, *Information technology — Programming languages — C*,
  Annex G, *IEC 60559-compatible complex arithmetic*. Section numbers G.x refer to this annex.
* [C23] ISO/IEC 9899:2024, *Information technology — Programming languages — C*, Annex G.
* [Kahan1987] W. Kahan, *Branch Cuts for Complex Elementary Functions, or Much Ado About
  Nothing's Sign Bit*, in A. Iserles and M. J. D. Powell (eds.), *The State of the Art in
  Numerical Analysis*, Clarendon Press, Oxford, 1987.
* [FreeBSD] FreeBSD msun library: `lib/msun/src/k_expf.c` (`__ldexp_cexpf`) and
  `lib/msun/src/s_ctanhf.c`.
-/

namespace ComplexFloat32

/-- The complex hyperbolic sine `sinh x cos y + cosh x sin y I`, with the special values of
[C17, G.6.2.5], and `Float32.mulExpLarge` for `|x| > 88.7` as in [FreeBSD]. -/
public protected def sinh (z : ComplexFloat32) : ComplexFloat32 :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float32.sinh x, y⟩
  else if !y.isFinite then
    if x == 0 || x.isInf then ⟨x, y - y⟩
    else ⟨y - y, y - y⟩
  else if x.isNaN then ⟨x, x⟩
  else if x.abs > 88.7 then
    -- `sinh x` and `cosh x` overflow but the result may not.
    ⟨Float32.copySign 1 x * Float32.mulExpLarge (Float32.cos y) x.abs (-1),
      Float32.mulExpLarge (Float32.sin y) x.abs (-1)⟩
  else ⟨Float32.sinh x * Float32.cos y, Float32.cosh x * Float32.sin y⟩

/-- The complex hyperbolic cosine `cosh x cos y + sinh x sin y I`, with the special values of
[C17, G.6.2.4], and `Float32.mulExpLarge` for `|x| > 88.7` as in [FreeBSD]. -/
public protected def cosh (z : ComplexFloat32) : ComplexFloat32 :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float32.cosh x, y * Float32.copySign 1 x⟩
  else if !y.isFinite then
    if x == 0 then ⟨y - y, 0⟩
    else if x.isInf then ⟨Float32.inf, y - y⟩
    else ⟨y - y, y - y⟩
  else if x.isNaN then ⟨x, x⟩
  else if x.abs > 88.7 then
    ⟨Float32.mulExpLarge (Float32.cos y) x.abs (-1),
      Float32.copySign 1 x * Float32.mulExpLarge (Float32.sin y) x.abs (-1)⟩
  else ⟨Float32.cosh x * Float32.cos y, Float32.sinh x * Float32.sin y⟩

/--
The complex hyperbolic tangent, with the special values of [C17, G.6.2.6], except that
`tanh (±0 + ∞ I) = ±0 + NaN I` as revised in [C23] (and as in glibc), where C17 gives
`NaN + NaN I`. Finite arguments use Kahan's formula [Kahan1987]: with `t = tan y`,
`β = 1 + t²`, `s = sinh x` and `ρ = √(1 + s²)`, the result is
`(β ρ s + t I) / (1 + β s²)`. For `|x| > 9` it uses the asymptotic form of `ctanh` in
[FreeBSD]: `±1 + 4 sin y cos y exp (-2|x|) I`.
-/
public protected def tanh (z : ComplexFloat32) : ComplexFloat32 :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float32.tanh x, y⟩
  else if x.isNaN then ⟨x, x⟩
  else if x.isInf then
    ⟨Float32.copySign 1 x,
      Float32.copySign 0 (if y.isFinite then Float32.sin y * Float32.cos y else y)⟩
  else if x == 0 then ⟨x, Float32.tan y⟩
  else if !y.isFinite then ⟨y - y, y - y⟩
  else if x.abs > 9 then
    -- `tanh x` is `±1` to single precision; the imaginary part is `4 sin y cos y exp (-2|x|)`.
    let e := Float32.exp (-x.abs)
    ⟨Float32.copySign 1 x, 4 * Float32.sin y * Float32.cos y * e * e⟩
  else
    -- Kahan's formula [Kahan1987].
    let t := Float32.tan y
    let β := 1 + t * t
    let s := Float32.sinh x
    let ρ := Float32.sqrt (1 + s * s)
    let d := 1 + β * s * s
    ⟨β * ρ * s / d, t / d⟩

/-- The complex sine. -/
public protected def sin (z : ComplexFloat32) : ComplexFloat32 :=
  let w := ComplexFloat32.sinh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- The complex cosine. -/
public protected def cos (z : ComplexFloat32) : ComplexFloat32 :=
  ComplexFloat32.cosh ⟨-z.im, z.re⟩

/-- The complex tangent. -/
public protected def tan (z : ComplexFloat32) : ComplexFloat32 :=
  let w := ComplexFloat32.tanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

end ComplexFloat32
