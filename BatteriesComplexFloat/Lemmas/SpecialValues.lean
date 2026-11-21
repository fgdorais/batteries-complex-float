/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.Lemmas.Basic

/-!
# Special values of the arithmetic

Theorems about specific values of `*`, `/`, `abs` and `proj`, checked by evaluating the
logical model `Float.Model` in the kernel. The cases are those singled out by Annex G
[C17, G.5.1]: infinite operands give infinite results, division by zero of a non-zero number is
infinite, division of a finite number by an infinite one is zero, and scaling avoids premature
overflow and underflow.

## References

* [C17] ISO/IEC 9899:2018, *Information technology — Programming languages — C*,
  Annex G, *IEC 60559-compatible complex arithmetic*.
-/

namespace ComplexFloat

/-! ## Multiplication -/

public theorem inf_nan_mul_two : ((⟨Float.inf, Float.nan⟩ : ComplexFloat) * ⟨2, 0⟩).isInf := by
  decide +kernel

public theorem inf_mul_nan_one : ((⟨Float.inf, 0⟩ : ComplexFloat) * ⟨Float.nan, 1⟩).isInf := by
  decide +kernel

public theorem mul_overflow_isInf :
    ((⟨1e300, 1e300⟩ : ComplexFloat) * ⟨1e300, 1e300⟩).isInf := by
  decide +kernel

public theorem mul_example : (⟨1, 2⟩ : ComplexFloat) * ⟨3, 4⟩ = ⟨-5, 10⟩ := by
  decide +kernel

/-- The real part of `(1 + 2⁻³⁰ + I) (1 - 2⁻³⁰ + I)` is `-2⁻⁶⁰` exactly, which the textbook
formula loses because `(1 + 2⁻³⁰) * (1 - 2⁻³⁰)` rounds to `1`. -/
public theorem mul_cancel_re :
    ((⟨1 + Float.twoPow (-30), 1⟩ : ComplexFloat) * ⟨1 - Float.twoPow (-30), 1⟩).re =
      -Float.twoPow (-60) := by
  decide +kernel

/-! ## Division -/

public theorem div_zero_isInf : ((⟨1, 1⟩ : ComplexFloat) / ⟨0, 0⟩).isInf := by
  decide +kernel

public theorem inf_nan_div_isInf : ((⟨Float.inf, Float.nan⟩ : ComplexFloat) / ⟨2, 1⟩).isInf := by
  decide +kernel

public theorem div_inf_nan : (⟨1, 1⟩ : ComplexFloat) / ⟨Float.inf, Float.nan⟩ = ⟨0, 0⟩ := by
  decide +kernel

public theorem div_self_huge : (⟨1e300, 1e300⟩ : ComplexFloat) / ⟨1e300, 1e300⟩ = ⟨1, 0⟩ := by
  decide +kernel

public theorem div_self_tiny : (⟨1e-300, 1e-300⟩ : ComplexFloat) / ⟨1e-300, 1e-300⟩ = ⟨1, 0⟩ := by
  decide +kernel

/-- Dividing by a real number divides each part. -/
public theorem div_real : (⟨3, 1⟩ : ComplexFloat) / ⟨2, 0⟩ = ⟨1.5, 0.5⟩ := by
  decide +kernel

/-- The imaginary part of `(1 + 3 I) / ((3 + 2⁻⁵⁰) + 9 I)` has numerator `3 * 2⁻⁵⁰` exactly, which
the textbook formula gets a third too large because `3 * (3 + 2⁻⁵⁰)` rounds. -/
public theorem div_cancel_im :
    ((⟨1, 3⟩ : ComplexFloat) / ⟨3 + Float.twoPow (-50), 9⟩).im =
      3 * Float.twoPow (-50) / ((3 + Float.twoPow (-50)) * (3 + Float.twoPow (-50)) + 81) := by
  decide +kernel

/-! ## Absolute value and projection -/

public theorem abs_huge : (⟨3e300, 4e300⟩ : ComplexFloat).abs = 5e300 := by
  decide +kernel

public theorem abs_tiny : (⟨3e-300, 4e-300⟩ : ComplexFloat).abs = 5e-300 := by
  decide +kernel

public theorem abs_inf_nan : (⟨Float.inf, Float.nan⟩ : ComplexFloat).abs = Float.inf := by
  decide +kernel

public theorem proj_nan_neg_inf :
    (⟨Float.nan, -Float.inf⟩ : ComplexFloat).proj = ⟨Float.inf, -0⟩ := by
  decide +kernel

/-! ## Conjugation does not distribute over multiplication

`conj (z * w) = conj z * conj w` fails on signs of zeros: with `z = 1 + I` and `w = 1 - I`, the
imaginary part of `z * w` is `1 + (-1) = +0`, so `conj (z * w)` has imaginary part `-0`, while
`conj z * conj w` has imaginary part `-1 + 1 = +0`.
-/

public theorem exists_conj_mul_ne : ∃ z w : ComplexFloat, (z * w).conj ≠ z.conj * w.conj :=
  ⟨⟨1, 1⟩, ⟨1, -1⟩, by decide +kernel⟩

end ComplexFloat
