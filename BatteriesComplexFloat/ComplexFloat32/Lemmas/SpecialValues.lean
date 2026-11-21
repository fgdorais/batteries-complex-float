/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.ComplexFloat32.Lemmas.Basic

/-!
# Special values of the arithmetic

Theorems about specific values of `*`, `/`, `abs` and `proj`, checked by evaluating the
logical model `Float32.Model` in the kernel. The cases are those singled out by Annex G
[C17, G.5.1]: infinite operands give infinite results, division by zero of a non-zero number is
infinite, division of a finite number by an infinite one is zero, and scaling avoids premature
overflow and underflow.

## References

* [C17] ISO/IEC 9899:2018, *Information technology — Programming languages — C*,
  Annex G, *IEC 60559-compatible complex arithmetic*.
-/

namespace ComplexFloat32

/-! ## Multiplication -/

public theorem inf_nan_mul_two :
    ((⟨Float32.inf, Float32.nan⟩ : ComplexFloat32) * ⟨2, 0⟩).isInf := by
  decide +kernel

public theorem inf_mul_nan_one :
    ((⟨Float32.inf, 0⟩ : ComplexFloat32) * ⟨Float32.nan, 1⟩).isInf := by
  decide +kernel

public theorem mul_overflow_isInf :
    ((⟨1e30, 1e30⟩ : ComplexFloat32) * ⟨1e30, 1e30⟩).isInf := by
  decide +kernel

public theorem mul_example : (⟨1, 2⟩ : ComplexFloat32) * ⟨3, 4⟩ = ⟨-5, 10⟩ := by
  decide +kernel

/-- The real part of `(1 + 2⁻¹⁵ + I) (1 - 2⁻¹⁵ + I)` is `-2⁻³⁰` exactly, which the
textbook formula loses because `(1 + 2⁻¹⁵) * (1 - 2⁻¹⁵)` rounds to `1`. -/
public theorem mul_cancel_re :
    ((⟨1 + Float32.twoPow (-15), 1⟩ : ComplexFloat32) * ⟨1 - Float32.twoPow (-15), 1⟩).re =
      -Float32.twoPow (-30) := by
  decide +kernel

/-! ## Division -/

public theorem div_zero_isInf : ((⟨1, 1⟩ : ComplexFloat32) / ⟨0, 0⟩).isInf := by
  decide +kernel

public theorem inf_nan_div_isInf :
    ((⟨Float32.inf, Float32.nan⟩ : ComplexFloat32) / ⟨2, 1⟩).isInf := by
  decide +kernel

public theorem div_inf_nan : (⟨1, 1⟩ : ComplexFloat32) / ⟨Float32.inf, Float32.nan⟩ = ⟨0, 0⟩ := by
  decide +kernel

public theorem div_self_huge : (⟨1e30, 1e30⟩ : ComplexFloat32) / ⟨1e30, 1e30⟩ = ⟨1, 0⟩ := by
  decide +kernel

public theorem div_self_tiny : (⟨1e-30, 1e-30⟩ : ComplexFloat32) / ⟨1e-30, 1e-30⟩ = ⟨1, 0⟩ := by
  decide +kernel

/-- Dividing by a real number divides each part. -/
public theorem div_real : (⟨3, 1⟩ : ComplexFloat32) / ⟨2, 0⟩ = ⟨1.5, 0.5⟩ := by
  decide +kernel

/-- The imaginary part of `(1 + 3 I) / ((3 + 2⁻²¹) + 9 I)` has numerator `3 * 2⁻²¹` exactly,
which the textbook formula gets a third too large because `3 * (3 + 2⁻²¹)` rounds. -/
public theorem div_cancel_im :
    ((⟨1, 3⟩ : ComplexFloat32) / ⟨3 + Float32.twoPow (-21), 9⟩).im =
      3 * Float32.twoPow (-21) /
        ((3 + Float32.twoPow (-21)) * (3 + Float32.twoPow (-21)) + 81) := by
  decide +kernel

/-! ## Absolute value and projection -/

public theorem abs_huge : (⟨3e30, 4e30⟩ : ComplexFloat32).abs = 5e30 := by
  decide +kernel

public theorem abs_tiny : (⟨3e-30, 4e-30⟩ : ComplexFloat32).abs = 5e-30 := by
  decide +kernel

public theorem abs_inf_nan : (⟨Float32.inf, Float32.nan⟩ : ComplexFloat32).abs = Float32.inf := by
  decide +kernel

public theorem proj_nan_neg_inf :
    (⟨Float32.nan, -Float32.inf⟩ : ComplexFloat32).proj = ⟨Float32.inf, -0⟩ := by
  decide +kernel

/-! ## Conjugation does not distribute over multiplication

`conj (z * w) = conj z * conj w` fails on signs of zeros: with `z = 1 + I` and `w = 1 - I`, the
imaginary part of `z * w` is `1 + (-1) = +0`, so `conj (z * w)` has imaginary part `-0`, while
`conj z * conj w` has imaginary part `-1 + 1 = +0`.
-/

public theorem exists_conj_mul_ne : ∃ z w : ComplexFloat32, (z * w).conj ≠ z.conj * w.conj :=
  ⟨⟨1, 1⟩, ⟨1, -1⟩, by decide +kernel⟩

end ComplexFloat32
