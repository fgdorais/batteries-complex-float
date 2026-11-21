/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.ComplexFloat.Scalar

/-!
# Complex floating-point numbers

`ComplexFloat` is a pair of `Float`s with the arithmetic of C's `double complex` as specified by
Annex G of the C standard (IEC 60559-compatible complex arithmetic):

* operations mixing `Float` and `ComplexFloat` treat the real operand as having no imaginary
  part at all, rather than an imaginary part `+0`, so that signs of zeros are preserved. For
  this reason there is no coercion from `Float` to `ComplexFloat`, and a numeric literal in a
  complex expression should be given type `Float`: `(1 : Float) - z`, not `1 - z`, since the
  literal `1 : ComplexFloat` has imaginary part `+0` and `0 - (+0) = +0`;
* multiplication and division recover infinities: a product or quotient involving an infinite
  operand is infinite even when the textbook formula gives NaN in both parts;
* multiplication recovers the rounding errors of its products with fused multiply-adds, so that
  each part of a product is accurate to a few units in the last place;
* division scales its operands so that it neither overflows nor underflows prematurely, and
  computes its numerators with fused multiply-adds so that each part of the quotient is
  accurate to a few units in the last place.

## Accuracy

The errors below are the largest measured, in ulps of each part of the result, by the
`accuracy` executable of `native/` on random inputs of several magnitudes and on inputs near the
unit circle and the branch points: multiplication and division against the exact result in
`Rat`, and the elementary functions against the C library's `long double complex` functions
(which have 11 more bits). The tests in `BatteriesComplexFloatTest` check smaller samples in CI.

* `*`: 1 ulp, whereas the textbook formula (and the C library) can lose every digit
  of a part to cancellation.
* `/`: 4 ulps.
* `abs`: 1 ulp; `arg`: that of `Float.atan2`.
* `exp`, `sqrt`: 2.5 ulps; `log`, `sin`, `cos`, `sinh`, `cosh`: 3 ulps; `tan`, `tanh`: 6 ulps;
  `asin`, `acos`, `atan`, `asinh`, `acosh`, `atanh`: 4.5 ulps.

## References

* [C17] ISO/IEC 9899:2018, *Information technology — Programming languages — C*,
  Annex G, *IEC 60559-compatible complex arithmetic*. Section numbers G.x refer to this annex.
* [IEEE754] *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019.
* [JeannerodLouvetMuller2013a] C.-P. Jeannerod, N. Louvet and J.-M. Muller, *Further analysis
  of Kahan's algorithm for the accurate computation of 2 × 2 determinants*, Mathematics of
  Computation 82 (2013), no. 284, 2245–2264.
* [JeannerodLouvetMuller2013b] C.-P. Jeannerod, N. Louvet and J.-M. Muller, *On the
  componentwise accuracy of complex floating-point division with an FMA*, in 21st IEEE
  Symposium on Computer Arithmetic (ARITH 2013), IEEE, 2013.
-/

/-- Complex numbers with `Float` real and imaginary parts. -/
public structure ComplexFloat where
  /-- The real part. -/
  re : Float
  /-- The imaginary part. -/
  im : Float
deriving Inhabited, Repr

namespace ComplexFloat

/-- The complex number with real part `x` and imaginary part `+0`. -/
@[expose, inline] public def ofReal (x : Float) : ComplexFloat := ⟨x, 0⟩

/-- The imaginary unit. -/
@[expose] public def I : ComplexFloat := ⟨0, 1⟩

/-- The complex number `x * I`, with real part `+0`. -/
@[expose, inline] public def ofImag (y : Float) : ComplexFloat := ⟨0, y⟩

public instance : OfNat ComplexFloat n := ⟨ofReal (OfNat.ofNat n)⟩

public instance : OfScientific ComplexFloat where
  ofScientific m s e := ofReal (OfScientific.ofScientific m s e)

/-- Decidable equality of both parts, where all NaNs are equal and `+0 ≠ -0`. -/
public instance : DecidableEq ComplexFloat := fun z w =>
  if h : z.re = w.re ∧ z.im = w.im then
    isTrue (by cases z; cases w; simp_all)
  else
    isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/-- Componentwise IEEE equality: NaN parts are never equal, `+0` and `-0` are equal. -/
public instance : BEq ComplexFloat where
  beq z w := z.re == w.re && z.im == w.im

/-- Whether either part is NaN. -/
@[expose, inline] public def isNaN (z : ComplexFloat) : Bool := z.re.isNaN || z.im.isNaN

/-- Whether either part is infinite. Such a number is infinite even if the other part is NaN. -/
@[expose, inline] public def isInf (z : ComplexFloat) : Bool := z.re.isInf || z.im.isInf

/-- Whether both parts are finite. -/
@[expose, inline] public def isFinite (z : ComplexFloat) : Bool := z.re.isFinite && z.im.isFinite

/-! ## Arithmetic -/

/-- Complex conjugate. -/
@[expose, inline] public def conj (z : ComplexFloat) : ComplexFloat := ⟨z.re, -z.im⟩

/-- Negation. -/
@[expose, inline] public protected def neg (z : ComplexFloat) : ComplexFloat := ⟨-z.re, -z.im⟩

/-- Addition. -/
@[expose, inline] public protected def add (z w : ComplexFloat) : ComplexFloat :=
  ⟨z.re + w.re, z.im + w.im⟩

/-- Subtraction. -/
@[expose, inline] public protected def sub (z w : ComplexFloat) : ComplexFloat :=
  ⟨z.re - w.re, z.im - w.im⟩

/--
The operand recovery step of Annex G multiplication [C17, G.5.1, Example 1]: if `z` is infinite,
its infinite parts become `±1` and its other parts `±0`; otherwise its NaN parts become `±0`.
Signs are kept throughout.
-/
@[expose] public def recoverInf (z : ComplexFloat) : ComplexFloat :=
  if z.isInf then
    let box (u : Float) := Float.copySign (if u.isInf then 1 else 0) u
    ⟨box z.re, box z.im⟩
  else
    let zero (u : Float) := if u.isNaN then Float.copySign 0 u else u
    ⟨zero z.re, zero z.im⟩

/--
`p * q + r * s` with an error of at most two units in the last place, by Kahan's algorithm with
fused multiply-adds [JeannerodLouvetMuller2013a]: the rounding error of `r * s` is recovered
exactly with an `fma` and subtracted at the end. Unlike `p * q + r * s`, it stays accurate when
the two products nearly cancel.
-/
@[expose] public def dotFma (p q r s : Float) : Float :=
  let w := r * s
  let e := Float.fma (-r) s w
  Float.fma p q w - e

/--
Multiplication, as in the reference implementation `_Cmultd` of [C17, G.5.1, Example 1]: the
textbook formula, then recovery of infinite results when both parts come out NaN. Unlike
`_Cmultd`, the rounding errors of the four products are recovered with `Float.mulErr` and added
back, which keeps each part of the result within a few units in the last place of the exact
product even when the two products in it nearly cancel. This is the idea of Kahan's algorithm in
`dotFma`, with both errors recovered so that multiplication stays commutative. When an
operand is infinite or an intermediate product overflows, both operands go through `recoverInf`
and the textbook formula is applied again and multiplied by `inf`. This is a symmetric
rearrangement of the case analysis in `_Cmultd`, which gives the same results.
-/
@[expose] public protected def mul (z w : ComplexFloat) : ComplexFloat :=
  let a := z.re; let b := z.im; let c := w.re; let d := w.im
  -- The rounding errors of the four products are added back. An error is infinite or NaN when
  -- its product overflows, and then the textbook formula stands, as in C. A zero error is
  -- skipped, so that signs of zeros are as in the textbook formula.
  let fix (u e : Float) : Float := if e.isFinite && e != 0 then u + e else u
  let x := fix (a * c - b * d) (Float.mulErr a c - Float.mulErr b d)
  let y := fix (a * d + b * c) (Float.mulErr a d + Float.mulErr b c)
  if x.isNaN && y.isNaN then
    let overflow := (z.re * w.re).isInf || (z.im * w.im).isInf || (z.re * w.im).isInf
      || (z.im * w.re).isInf
    if z.isInf || w.isInf || overflow then
      let z := z.recoverInf; let w := w.recoverInf
      ⟨Float.inf * (z.re * w.re - z.im * w.im), Float.inf * (z.re * w.im + z.im * w.re)⟩
    else ⟨x, y⟩
  else ⟨x, y⟩

/--
`n / d * 2 ^ s`, rounded once (when `n` and `d` are normal): both are first scaled to `[1, 2)`, so
that the quotient does not underflow or overflow before the final scaling.
-/
@[expose] public def divScaled (n d : Float) (s : Int) : Float :=
  match n.exponent?, d.exponent? with
  | some en, some ed => Float.ldexp (Float.ldexp n (-en) / Float.ldexp d (-ed)) (en - ed + s)
  | _, _ => Float.ldexp (n / d) s

/--
Division, following the reference implementation `_Cdivd` of [C17, G.5.1, Example 2] with two
changes. Both operands are scaled by powers of two (with `exponent?` and `ldexp` in place of
C's `logb` and `scalbn`), the dividend as well as the divisor, so that nothing overflows or
underflows before the final scaling. The numerators `a c + b d` and `b c - a d` are computed with
`dotFma`, which keeps each part of the result within a few units in the last place of the
exact quotient [JeannerodLouvetMuller2013b], whereas the textbook formula can lose all digits of
a part to cancellation. Infinite and zero results are recovered as in `_Cdivd` when both parts
come out NaN.
-/
@[expose] public protected def div (z w : ComplexFloat) : ComplexFloat :=
  let a := z.re; let b := z.im; let c := w.re; let d := w.im
  -- Both operands are scaled so that their larger part is in `[2 ^ 509, 2 ^ 510)`: the products
  -- and `denom` then stay below `2 ^ 1021`, a part up to `2 ^ 1531` times smaller than the other
  -- stays a normal number, and `divScaled` rescales before the only rounding that can underflow.
  let scale (u v : Float) (e : Int) : Float × Float × Int :=
    match (Float.maximum u.abs v.abs).exponent? with
    | some k => (Float.ldexp u (e - k), Float.ldexp v (e - k), k - e)
    | none => (u, v, 0)
  let (a', b', j) := scale a b 509
  let (c', d', k) := scale c d 509
  let denom := c' * c' + d' * d'
  -- A real or imaginary divisor needs no formula: `(a + b I) / c = a / c + (b / c) I`, which is
  -- correctly rounded. A zero part keeps the sign that the formula would give it.
  let part (u v : Float) (n : Float) : Float := if u == 0 then n else v
  let (x, y) :=
    if z.isFinite && d == 0 && c != 0 && c.isFinite then
      (part a (a / c) (a * c + b * d), part b (b / c) (b * c - a * d))
    else if z.isFinite && c == 0 && d != 0 && d.isFinite then
      (part b (b / d) (a * c + b * d), part a (-a / d) (b * c - a * d))
    else
      (divScaled (dotFma a' c' b' d') denom (j - k),
        divScaled (dotFma b' c' (-a') d') denom (j - k))
  if x.isNaN && y.isNaN then
    let box (u : Float) := Float.copySign (if u.isInf then 1 else 0) u
    if denom == 0 && (!a.isNaN || !b.isNaN) then
      let s := Float.copySign Float.inf c
      ⟨s * a, s * b⟩
    else if (a.isInf || b.isInf) && c.isFinite && d.isFinite then
      let a := box a; let b := box b
      ⟨Float.inf * (a * c + b * d), Float.inf * (b * c - a * d)⟩
    else if (c.isInf || d.isInf) && a.isFinite && b.isFinite then
      let c := box c; let d := box d
      ⟨0 * (a * c + b * d), 0 * (b * c - a * d)⟩
    else ⟨x, y⟩
  else ⟨x, y⟩

/-- Multiplicative inverse. -/
@[expose, inline] public def inv (z : ComplexFloat) : ComplexFloat := ComplexFloat.div 1 z

public instance : Neg ComplexFloat := ⟨ComplexFloat.neg⟩
public instance : Add ComplexFloat := ⟨ComplexFloat.add⟩
public instance : Sub ComplexFloat := ⟨ComplexFloat.sub⟩
public instance : Mul ComplexFloat := ⟨ComplexFloat.mul⟩
public instance : Div ComplexFloat := ⟨ComplexFloat.div⟩

/-! ## Mixed real and complex arithmetic -/

public instance : HAdd ComplexFloat Float ComplexFloat := ⟨fun z x => ⟨z.re + x, z.im⟩⟩
public instance : HAdd Float ComplexFloat ComplexFloat := ⟨fun x z => ⟨x + z.re, z.im⟩⟩
public instance : HSub ComplexFloat Float ComplexFloat := ⟨fun z x => ⟨z.re - x, z.im⟩⟩
public instance : HSub Float ComplexFloat ComplexFloat := ⟨fun x z => ⟨x - z.re, -z.im⟩⟩
public instance : HMul ComplexFloat Float ComplexFloat := ⟨fun z x => ⟨z.re * x, z.im * x⟩⟩
public instance : HMul Float ComplexFloat ComplexFloat := ⟨fun x z => ⟨x * z.re, x * z.im⟩⟩
public instance : HDiv ComplexFloat Float ComplexFloat := ⟨fun z x => ⟨z.re / x, z.im / x⟩⟩
public instance : HDiv Float ComplexFloat ComplexFloat := ⟨fun x z => ComplexFloat.div ⟨x, 0⟩ z⟩

/-! ## Absolute value and argument -/

/-- The absolute value (modulus), without undue overflow or underflow (C's `cabs`, via
`Float.hypot`). -/
@[expose, inline] public def abs (z : ComplexFloat) : Float := Float.hypot z.re z.im

/-- The squared absolute value `re * re + im * im`, which can overflow. -/
@[expose, inline] public def normSq (z : ComplexFloat) : Float := z.re * z.re + z.im * z.im

/-- The argument (phase angle), in `[-π, π]`, with the signs of zeros of `atan2`. -/
@[expose, inline] public def arg (z : ComplexFloat) : Float := Float.atan2 z.im z.re

/--
Projection onto the Riemann sphere (C's `cproj`, [C17, 7.3.9.5]): every infinite number goes to
`inf + I * (±0)`, keeping the sign of the imaginary part; other numbers are unchanged.
-/
@[expose] public def proj (z : ComplexFloat) : ComplexFloat :=
  if z.isInf then ⟨Float.inf, Float.copySign 0 z.im⟩ else z

/-- The complex number with absolute value `r` and argument `θ`. -/
@[expose] public def polar (r θ : Float) : ComplexFloat := ⟨r * Float.cos θ, r * Float.sin θ⟩

/-! ## Printing -/

/-- Prints `x+yi` or `x-yi`, using the sign bit of `y`. -/
public instance : ToString ComplexFloat where
  toString z :=
    if z.im.signBit && !z.im.isNaN then s!"{z.re}-{-z.im}i" else s!"{z.re}+{z.im}i"

end ComplexFloat
