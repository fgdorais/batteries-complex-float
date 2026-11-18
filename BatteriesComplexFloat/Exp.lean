/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.Basic

/-!
# Exponential, logarithm, square root and powers

The special values follow Annex G of the C standard (G.6.3, G.6.4).
-/

namespace ComplexFloat

/-- The complex exponential. -/
public protected def exp (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if y == 0 then ⟨Float.exp x, y⟩
  else if x.isInf then
    if y.isFinite then
      if x > 0 then ⟨Float.inf * Float.cos y, Float.inf * Float.sin y⟩
      else ⟨0 * Float.cos y, 0 * Float.sin y⟩
    else if x > 0 then ⟨x, Float.nan⟩
    else ⟨0, Float.copySign 0 y⟩
  else if x > 709 then
    -- `exp x` overflows but the result may not.
    ⟨Float.mulExpLarge (Float.cos y) x, Float.mulExpLarge (Float.sin y) x⟩
  else
    let r := Float.exp x
    ⟨r * Float.cos y, r * Float.sin y⟩

/-- The principal logarithm, with branch cut along the negative real axis. -/
public protected def log (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  let re :=
    if x.isInf || y.isInf then Float.inf
    else if x.isNaN || y.isNaN then Float.nan
    else
      let ax := x.abs; let ay := y.abs
      let a := if ax < ay then ay else ax
      let b := if ax < ay then ax else ay
      if a == 0 then -Float.inf
      else if 0.5 ≤ a && a ≤ 2 then
        -- Near the unit circle, `log (a² + b²) / 2` loses accuracy.
        0.5 * Float.log1p ((a - 1) * (a + 1) + b * b)
      else if a < Float.twoPow (-500) then
        -- Scale up so that `hypot a b` is not subnormal.
        Float.log (Float.hypot (a * Float.twoPow 600) (b * Float.twoPow 600))
          - 415.88830833596717
      else Float.log (Float.hypot a b)
  ⟨re, Float.atan2 y x⟩

/-- The principal square root, with branch cut along the negative real axis. -/
public protected def sqrt (z : ComplexFloat) : ComplexFloat :=
  let x := z.re; let y := z.im
  if y.isInf then ⟨Float.inf, y⟩
  else if x.isNaN then ⟨x, Float.nan⟩
  else if x.isInf then
    if x > 0 then ⟨x, if y.isNaN then y else Float.copySign 0 y⟩
    else if y.isNaN then ⟨y, Float.inf⟩
    else ⟨0, Float.copySign Float.inf y⟩
  else if y.isNaN then ⟨y, y⟩
  else if x == 0 && y == 0 then ⟨0, y⟩
  else
    -- Scale so that `|x| + hypot x y` neither overflows nor loses bits to underflow.
    let ax := x.abs; let ay := y.abs
    let (s, x, y) :=
      if ax > Float.twoPow 1020 || ay > Float.twoPow 1020 then (2, x * 0.25, y * 0.25)
      else if ax < Float.twoPow (-1020) && ay < Float.twoPow (-1020) then
        (Float.twoPow (-54), x * Float.twoPow 108, y * Float.twoPow 108)
      else (1, x, y)
    let t := Float.sqrt ((x.abs + Float.hypot x y) * 0.5)
    if x ≥ 0 then ⟨t * s, y / (2 * t) * s⟩
    else ⟨y.abs / (2 * t) * s, Float.copySign (t * s) y⟩

/-- The principal value of `z ^ w = exp (w * log z)`, with `z ^ 0 = 1` and `0 ^ w = 0` when
`w` is real and positive. -/
public protected def pow (z w : ComplexFloat) : ComplexFloat :=
  if w.re == 0 && w.im == 0 then 1
  else if z.re == 0 && z.im == 0 && w.im == 0 && w.re > 0 then 0
  else ComplexFloat.exp (w * ComplexFloat.log z)

/-- `z ^ n` for a natural number `n`, by repeated squaring. -/
public def npow (z : ComplexFloat) (n : Nat) : ComplexFloat :=
  loop z n 1
where
  /-- `loop b n acc = acc * b ^ n`. -/
  loop (b : ComplexFloat) (n : Nat) (acc : ComplexFloat) : ComplexFloat :=
    if _ : n = 0 then acc
    else loop (b * b) (n / 2) (if n % 2 = 1 then acc * b else acc)
  termination_by n
  decreasing_by omega

public instance : HPow ComplexFloat Nat ComplexFloat := ⟨npow⟩
public instance : HPow ComplexFloat ComplexFloat ComplexFloat := ⟨ComplexFloat.pow⟩
public instance : HPow ComplexFloat Float ComplexFloat := ⟨fun z x => ComplexFloat.pow z ⟨x, 0⟩⟩

end ComplexFloat
