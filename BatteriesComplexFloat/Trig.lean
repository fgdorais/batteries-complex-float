/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.Basic

/-!
# Hyperbolic and trigonometric functions

The hyperbolic functions follow the special values of Annex G of the C standard (G.6.2), and
the trigonometric functions are defined from them as in G.6:
`sin z = -I * sinh (I * z)`, `cos z = cosh (I * z)` and `tan z = -I * tanh (I * z)`.
-/

namespace ComplexFloat

/-- The complex hyperbolic sine. -/
public protected def sinh (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float.sinh x, y⟩
  else if !y.isFinite then
    if x == 0 || x.isInf then ⟨x, y - y⟩
    else ⟨y - y, y - y⟩
  else if x.isNaN then ⟨x, x⟩
  else if x.abs > 709 then
    -- `sinh x` and `cosh x` overflow but the result may not.
    ⟨Float.copySign 1 x * Float.mulExpLarge (Float.cos y) x.abs (-1),
      Float.mulExpLarge (Float.sin y) x.abs (-1)⟩
  else ⟨Float.sinh x * Float.cos y, Float.cosh x * Float.sin y⟩

/-- The complex hyperbolic cosine. -/
public protected def cosh (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float.cosh x, y * Float.copySign 1 x⟩
  else if !y.isFinite then
    if x == 0 then ⟨y - y, 0⟩
    else if x.isInf then ⟨Float.inf, y - y⟩
    else ⟨y - y, y - y⟩
  else if x.isNaN then ⟨x, x⟩
  else if x.abs > 709 then
    ⟨Float.mulExpLarge (Float.cos y) x.abs (-1),
      Float.copySign 1 x * Float.mulExpLarge (Float.sin y) x.abs (-1)⟩
  else ⟨Float.cosh x * Float.cos y, Float.sinh x * Float.sin y⟩

/-- The complex hyperbolic tangent. -/
public protected def tanh (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float.tanh x, y⟩
  else if x.isNaN then ⟨x, x⟩
  else if x.isInf then
    ⟨Float.copySign 1 x, Float.copySign 0 (if y.isFinite then Float.sin y * Float.cos y else y)⟩
  else if x == 0 then ⟨x, Float.tan y⟩
  else if !y.isFinite then ⟨y - y, y - y⟩
  else if x.abs > 22 then
    -- `tanh x` is `±1` to double precision; the imaginary part is `4 sin y cos y exp (-2|x|)`.
    let e := Float.exp (-x.abs)
    ⟨Float.copySign 1 x, 4 * Float.sin y * Float.cos y * e * e⟩
  else
    -- Kahan's formula.
    let t := Float.tan y
    let β := 1 + t * t
    let s := Float.sinh x
    let ρ := Float.sqrt (1 + s * s)
    let d := 1 + β * s * s
    ⟨β * ρ * s / d, t / d⟩

/-- The complex sine. -/
public protected def sin (z : ComplexFloat) : ComplexFloat :=
  let w := ComplexFloat.sinh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

/-- The complex cosine. -/
public protected def cos (z : ComplexFloat) : ComplexFloat :=
  ComplexFloat.cosh ⟨-z.im, z.re⟩

/-- The complex tangent. -/
public protected def tan (z : ComplexFloat) : ComplexFloat :=
  let w := ComplexFloat.tanh ⟨-z.im, z.re⟩
  ⟨w.im, -w.re⟩

end ComplexFloat
