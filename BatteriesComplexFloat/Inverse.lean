/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.Exp

/-!
# Inverse hyperbolic and trigonometric functions

The finite cases use the formulas of W. Kahan, *Branch Cuts for Complex Elementary Functions,
or Much Ado About Nothing's Sign Bit* (1987), which put the branch cuts where Annex G of the
C standard does and respect signed zeros on them. The non-finite cases follow Annex G
(G.6.1, G.6.2), and `asin z = -I * asinh (I * z)`, `atan z = -I * atanh (I * z)` as in G.6.
-/

namespace ComplexFloat

/-- `π / 2`. -/
private def halfPi : Float := 1.5707963267948966

/-- `π / 4`. -/
private def quarterPi : Float := 0.7853981633974483

/-- `3π / 4`. -/
private def threeQuarterPi : Float := 2.356194490192345

/-- Kahan's `arcsin` on finite inputs. -/
private def asinFinite (z : ComplexFloat) : ComplexFloat :=
  let a := ComplexFloat.sqrt ⟨1 - z.re, -z.im⟩
  let b := ComplexFloat.sqrt ⟨1 + z.re, z.im⟩
  ⟨Float.atan (z.re / (a.re * b.re - a.im * b.im)), Float.asinh (a.re * b.im - a.im * b.re)⟩

/-- The complex inverse hyperbolic sine, with branch cuts along the imaginary axis outside
`[-I, I]`. -/
public protected def asinh (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if x.abs < Float.twoPow (-27) && y.abs < Float.twoPow (-27) then
    -- `asinh z = z - z³ / 6 + ⋯`, and the correction is below half an ulp in each part.
    z
  else if z.isFinite then
    let w := asinFinite ⟨-y, x⟩
    ⟨w.im, -w.re⟩
  else if x.isInf then
    ⟨x, if y.isNaN then y else Float.copySign (if y.isInf then quarterPi else 0) y⟩
  else if y.isInf then
    if x.isNaN then ⟨Float.inf, x⟩ else ⟨Float.copySign Float.inf x, Float.copySign halfPi y⟩
  else if x.isNaN && y == 0 then ⟨x, y⟩
  else ⟨Float.nan, Float.nan⟩

/-- The complex inverse sine, with branch cuts along the real axis outside `[-1, 1]`. -/
public protected def asin (z : ComplexFloat) : ComplexFloat :=
  let w := ComplexFloat.asinh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- The complex inverse cosine, with branch cuts along the real axis outside `[-1, 1]`. -/
public protected def acos (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if z.isFinite then
    let a := ComplexFloat.sqrt ⟨1 - z.re, -z.im⟩
    let b := ComplexFloat.sqrt ⟨1 + z.re, z.im⟩
    ⟨2 * Float.atan (a.re / b.re), Float.asinh (b.re * a.im - b.im * a.re)⟩
  else if y.isInf then
    let re :=
      if x.isNaN then x
      else if x.isInf then if x > 0 then quarterPi else threeQuarterPi
      else halfPi
    ⟨re, -y⟩
  else if x.isInf then
    if y.isNaN then ⟨y, Float.inf⟩
    else ⟨if x > 0 then 0 else Float.pi, Float.copySign Float.inf (-y)⟩
  else if x == 0 then ⟨halfPi, y⟩
  else ⟨Float.nan, Float.nan⟩

/-- The complex inverse hyperbolic cosine, with branch cut along the real axis left of `1`. -/
public protected def acosh (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if z.isFinite then
    let a := ComplexFloat.sqrt ⟨z.re - 1, z.im⟩
    let b := ComplexFloat.sqrt ⟨z.re + 1, z.im⟩
    ⟨Float.asinh (a.re * b.re + a.im * b.im), 2 * Float.atan (a.im / b.re)⟩
  else if y.isInf then
    if x.isNaN then ⟨Float.inf, x⟩
    else
      let im := if x.isInf then if x > 0 then quarterPi else threeQuarterPi else halfPi
      ⟨Float.inf, Float.copySign im y⟩
  else if x.isInf then
    if y.isNaN then ⟨Float.inf, y⟩
    else ⟨Float.inf, Float.copySign (if x > 0 then 0 else Float.pi) y⟩
  else if x == 0 then ⟨Float.nan, halfPi⟩
  else ⟨Float.nan, Float.nan⟩

/-- `√(max float) / 4`, above which `atanh` uses its asymptotic form. -/
private def atanhBig : Float := 3.3519519824856493e153

/-- The complex inverse hyperbolic tangent, with branch cuts along the real axis outside
`[-1, 1]`. -/
public protected def atanh (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if x.isNaN then
    if y.isInf then ⟨0, Float.copySign halfPi y⟩ else ⟨x, x⟩
  else if y.isNaN then
    if x.isInf then ⟨Float.copySign 0 x, y⟩
    else if x == 0 then ⟨x, y⟩
    else ⟨y, y⟩
  else
    -- Kahan: work with `β * conj z` in the right half plane, then map back.
    let β := Float.copySign 1 x
    let x := β * x
    let y := -β * y
    let (ξ, η) :=
      if x > atanhBig || y.abs > atanhBig then
        let ξ :=
          if x.isInf || y.isInf then 0
          else if x ≥ y.abs then 1 / (x + y * (y / x))
          else let r := x / y; r / (y + x * r)
        (ξ, Float.copySign halfPi y)
      else if x == 1 && y == 0 then (Float.inf, y)
      else if x == 1 && y.abs < Float.twoPow (-500) then
        -- `y * y` underflows: the real part is `log (4 / y²) / 4 = (log 2 - log |y|) / 2`.
        ((0.6931471805599453 - Float.log y.abs) / 2,
          Float.copySign (halfPi + Float.atan (y.abs / 2)) y / 2)
      else
        (Float.log1p (4 * x / ((1 - x) * (1 - x) + y * y)) / 4,
          Float.atan2 (2 * y) ((1 - x) * (1 + x) - y * y) / 2)
    ⟨β * ξ, -β * η⟩

/-- The complex inverse tangent, with branch cuts along the imaginary axis outside `[-I, I]`. -/
public protected def atan (z : ComplexFloat) : ComplexFloat :=
  -- Annex G leaves the sign of the zero unspecified here; this one matches glibc, which can
  -- see the sign of the NaN that `-z.im` produces (Lean's NaNs carry no sign).
  if z.re.isInf && z.im.isNaN then ⟨Float.copySign halfPi z.re, 0⟩
  else
    let w := ComplexFloat.atanh ⟨-z.im, z.re⟩
    ⟨w.im, -w.re⟩

end ComplexFloat
