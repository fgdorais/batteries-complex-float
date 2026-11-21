import BatteriesComplexFloat

/-!
# Special values from Annex G of the C standard, in single precision

`z ≈ w` holds when each part of `z` and `w` is NaN in both, or is the same float with the same
sign (so `+0` and `-0` differ). Finite non-zero results are compared exactly only where Annex G
fixes them; other cases are left to the comparison with the C library in the `native` package.
-/

open ComplexFloat32

local notation "∞" => Float32.inf
local notation "NaN" => Float32.nan

/-- Same kind and sign in each part, NaNs equal. -/
def Float32.same (x y : Float32) : Bool :=
  x.isNaN && y.isNaN || x == y && x.signBit == y.signBit

/-- `Float32.same` in both parts. -/
def ComplexFloat32.same (z w : ComplexFloat32) : Bool := z.re.same w.re && z.im.same w.im

local infix:50 " ≈ " => ComplexFloat32.same

/-- Whether `z` is within `2⁻²¹` of `w` relative to `|w|`. -/
def ComplexFloat32.near (z w : ComplexFloat32) : Bool := (z - w).abs ≤ w.abs * 4.76837158203125e-7

/-- `π / 2`. -/
def halfPi : Float32 := 1.5707963267948966

/-! ## Arithmetic -/

-- Infinity recovery in products (G.5.1).
#guard (⟨∞, NaN⟩ : ComplexFloat32) * ⟨2, 0⟩ |>.isInf
#guard (⟨∞, 0⟩ : ComplexFloat32) * ⟨NaN, 1⟩ |>.isInf
#guard (⟨1e30, 1e30⟩ : ComplexFloat32) * ⟨1e30, 1e30⟩ |>.isInf
#guard ((⟨1, 2⟩ : ComplexFloat32) * ⟨3, 4⟩) ≈ ⟨-5, 10⟩
-- Cancellation: the real part of `(1 + 2⁻¹⁵ + I) (1 - 2⁻¹⁵ + I)` is `-2⁻³⁰` exactly,
-- but `(1 + 2⁻¹⁵) * (1 - 2⁻¹⁵)` rounds to `1`, so the textbook formula gives `0`.
#guard
  ((⟨1 + Float32.twoPow (-15), 1⟩ : ComplexFloat32) * ⟨1 - Float32.twoPow (-15), 1⟩) ≈
    ⟨-Float32.twoPow (-30), 2⟩

-- Division: infinite and zero results, no premature overflow or underflow (G.5.2), and
-- accuracy under cancellation.
#guard (⟨1, 1⟩ : ComplexFloat32) / ⟨0, 0⟩ |>.isInf
#guard (⟨∞, NaN⟩ : ComplexFloat32) / ⟨2, 1⟩ |>.isInf
#guard ((⟨1, 1⟩ : ComplexFloat32) / ⟨∞, NaN⟩) ≈ ⟨0, 0⟩
#guard ((⟨1e30, 1e30⟩ : ComplexFloat32) / ⟨1e30, 1e30⟩) ≈ ⟨1, 0⟩
#guard ((⟨1e-30, 1e-30⟩ : ComplexFloat32) / ⟨1e-30, 1e-30⟩) ≈ ⟨1, 0⟩
#guard ((⟨1, 2⟩ : ComplexFloat32) / ⟨1, 2⟩) ≈ ⟨1, 0⟩
#guard ((⟨3.3e38, 3.3e38⟩ : ComplexFloat32) / ⟨1.5, 1.5⟩).near ⟨3.3e38 / 1.5, 0⟩
#guard ((⟨1e-40, 1e-40⟩ : ComplexFloat32) / ⟨0.75, 0.75⟩).near ⟨1e-40 / 0.75, 0⟩
#guard ((⟨3, 1⟩ : ComplexFloat32) / ⟨2, 0⟩) ≈ ⟨1.5, 0.5⟩
#guard ((⟨3, 1⟩ : ComplexFloat32) / ⟨0, 2⟩) ≈ ⟨0.5, -1.5⟩
-- Cancellation: `b c - a d = 3 * 2⁻²¹` exactly, but `b * c` rounds to `9 + 2⁻¹⁹`, so the
-- textbook formula gives an imaginary part a third too large.
#guard ((⟨1, 3⟩ : ComplexFloat32) / ⟨3 + Float32.twoPow (-21), 9⟩).im ==
  3 * Float32.twoPow (-21) / ((3 + Float32.twoPow (-21)) * (3 + Float32.twoPow (-21)) + 81)

-- Mixed real and complex operands keep signs of zeros.
#guard ((1 : Float32) + (⟨-2, -0.0⟩ : ComplexFloat32)) ≈ ⟨-1, -0.0⟩
#guard ((⟨-2, -0.0⟩ : ComplexFloat32) * (2 : Float32)) ≈ ⟨-4, -0.0⟩

-- `abs` does not overflow or underflow.
#guard (⟨3e30, 4e30⟩ : ComplexFloat32).abs == 5e30
#guard (⟨3e-30, 4e-30⟩ : ComplexFloat32).abs == 5e-30
#guard (⟨∞, NaN⟩ : ComplexFloat32).abs == ∞
#guard (⟨NaN, -∞⟩ : ComplexFloat32).abs == ∞

-- `proj`.
#guard (⟨NaN, -∞⟩ : ComplexFloat32).proj ≈ ⟨∞, -0.0⟩
#guard (⟨1, 2⟩ : ComplexFloat32).proj ≈ ⟨1, 2⟩

/-! ## Exponential and logarithm (G.6.3) -/

#guard ComplexFloat32.exp ⟨0, 0⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat32.exp ⟨-0.0, -0.0⟩ ≈ ⟨1, -0.0⟩
#guard ComplexFloat32.exp ⟨∞, 0⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat32.exp ⟨-∞, 1⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.exp ⟨-∞, 3⟩ ≈ ⟨-0.0, 0⟩
#guard (ComplexFloat32.exp ⟨∞, ∞⟩).re.isInf && (ComplexFloat32.exp ⟨∞, ∞⟩).im.isNaN
#guard ComplexFloat32.exp ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat32.exp ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.exp ⟨1, ∞⟩ ≈ ⟨NaN, NaN⟩
-- No premature overflow: `exp 89` overflows, `exp 89 * cos 3` does not either, but
-- `exp 89 * sin 1e-30` is finite.
#guard (ComplexFloat32.exp ⟨89, 1e-30⟩).im.isFinite

#guard ComplexFloat32.log ⟨-0.0, 0⟩ ≈ ⟨-∞, Float32.pi⟩
#guard ComplexFloat32.log ⟨0, 0⟩ ≈ ⟨-∞, 0⟩
#guard ComplexFloat32.log ⟨-1, 0⟩ ≈ ⟨0, Float32.pi⟩
#guard ComplexFloat32.log ⟨-1, -0.0⟩ ≈ ⟨0, -Float32.pi⟩
#guard ComplexFloat32.log ⟨1, ∞⟩ ≈ ⟨∞, halfPi⟩
#guard ComplexFloat32.log ⟨∞, NaN⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat32.log ⟨NaN, -∞⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat32.log ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.log ⟨1, 0⟩ ≈ ⟨0, 0⟩

/-! ## Square root (G.6.4.2) -/

#guard ComplexFloat32.sqrt ⟨-0.0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.sqrt ⟨0, -0.0⟩ ≈ ⟨0, -0.0⟩
#guard ComplexFloat32.sqrt ⟨NaN, ∞⟩ ≈ ⟨∞, ∞⟩
#guard ComplexFloat32.sqrt ⟨1, -∞⟩ ≈ ⟨∞, -∞⟩
#guard ComplexFloat32.sqrt ⟨-∞, 1⟩ ≈ ⟨0, ∞⟩
#guard ComplexFloat32.sqrt ⟨∞, -1⟩ ≈ ⟨∞, -0.0⟩
#guard ComplexFloat32.sqrt ⟨∞, NaN⟩ ≈ ⟨∞, NaN⟩
#guard (ComplexFloat32.sqrt ⟨-∞, NaN⟩).im.isInf
#guard ComplexFloat32.sqrt ⟨-4, 0⟩ ≈ ⟨0, 2⟩
#guard ComplexFloat32.sqrt ⟨-4, -0.0⟩ ≈ ⟨0, -2⟩
#guard ComplexFloat32.sqrt ⟨3e38, 3e38⟩ |>.isFinite
#guard ComplexFloat32.sqrt ⟨4e-44, 0⟩ ≈ ⟨Float32.sqrt 4e-44, 0⟩

/-! ## Hyperbolic functions (G.6.2) -/

#guard ComplexFloat32.sinh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.sinh ⟨-0.0, -0.0⟩ ≈ ⟨-0.0, -0.0⟩
#guard (ComplexFloat32.sinh ⟨0, ∞⟩).im.isNaN && (ComplexFloat32.sinh ⟨0, ∞⟩).re == 0
#guard ComplexFloat32.sinh ⟨1, ∞⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.sinh ⟨∞, 0⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat32.sinh ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat32.sinh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩

#guard ComplexFloat32.cosh ⟨0, 0⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat32.cosh ⟨-0.0, 0⟩ ≈ ⟨1, -0.0⟩
#guard (ComplexFloat32.cosh ⟨0, ∞⟩).re.isNaN && (ComplexFloat32.cosh ⟨0, ∞⟩).im == 0
#guard ComplexFloat32.cosh ⟨∞, 0⟩ ≈ ⟨∞, 0⟩
#guard (ComplexFloat32.cosh ⟨NaN, 0⟩).im == 0

#guard ComplexFloat32.tanh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.tanh ⟨∞, 1⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat32.tanh ⟨∞, 2⟩ ≈ ⟨1, -0.0⟩
#guard (ComplexFloat32.tanh ⟨∞, ∞⟩).re == 1
#guard ComplexFloat32.tanh ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat32.tanh ⟨1, ∞⟩ ≈ ⟨NaN, NaN⟩
-- No overflow in the intermediate quantities.
#guard ComplexFloat32.tanh ⟨400, 1⟩ ≈ ⟨1, 0⟩
#guard (ComplexFloat32.tanh ⟨20, 1⟩).im > 0

/-! ## Inverse hyperbolic functions (G.6.2) -/

#guard ComplexFloat32.acosh ⟨0, 0⟩ ≈ ⟨0, halfPi⟩
#guard ComplexFloat32.acosh ⟨1, ∞⟩ ≈ ⟨∞, halfPi⟩
#guard ComplexFloat32.acosh ⟨-∞, 1⟩ ≈ ⟨∞, Float32.pi⟩
#guard ComplexFloat32.acosh ⟨∞, -1⟩ ≈ ⟨∞, -0.0⟩
#guard ComplexFloat32.acosh ⟨∞, NaN⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat32.acosh ⟨NaN, ∞⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat32.acosh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
-- On the branch cut, the sign of the imaginary part picks the side.
#guard (ComplexFloat32.acosh ⟨-2, 0⟩).im == Float32.pi
#guard (ComplexFloat32.acosh ⟨-2, -0.0⟩).im == -Float32.pi

#guard ComplexFloat32.asinh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.asinh ⟨1, ∞⟩ ≈ ⟨∞, halfPi⟩
#guard ComplexFloat32.asinh ⟨∞, 1⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat32.asinh ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat32.asinh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard (ComplexFloat32.asinh ⟨0, 2⟩).re > 0
#guard (ComplexFloat32.asinh ⟨-0.0, 2⟩).re < 0

#guard ComplexFloat32.atanh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.atanh ⟨0, NaN⟩ ≈ ⟨0, NaN⟩
#guard ComplexFloat32.atanh ⟨1, 0⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat32.atanh ⟨1, ∞⟩ ≈ ⟨0, halfPi⟩
#guard ComplexFloat32.atanh ⟨1, NaN⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.atanh ⟨∞, 1⟩ ≈ ⟨0, halfPi⟩
#guard ComplexFloat32.atanh ⟨∞, NaN⟩ ≈ ⟨0, NaN⟩
#guard ComplexFloat32.atanh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard (ComplexFloat32.atanh ⟨NaN, ∞⟩).im == halfPi
#guard (ComplexFloat32.atanh ⟨2, 0⟩).im == halfPi
#guard (ComplexFloat32.atanh ⟨2, -0.0⟩).im == -halfPi

/-! ## Trigonometric functions and their inverses (G.6) -/

-- `sin z = -I * sinh (I * z)`, `cos z = cosh (I * z)` and `tan z = -I * tanh (I * z)`, so these
-- rows are the rows of G.6.2.4 to G.6.2.6 turned by a quarter.
#guard ComplexFloat32.sin ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.sin ⟨-0.0, -0.0⟩ ≈ ⟨-0.0, -0.0⟩
#guard ComplexFloat32.sin ⟨0, ∞⟩ ≈ ⟨0, ∞⟩
#guard ComplexFloat32.sin ⟨1, ∞⟩ ≈ ⟨∞, ∞⟩
#guard ComplexFloat32.sin ⟨-1, ∞⟩ ≈ ⟨-∞, ∞⟩
#guard (ComplexFloat32.sin ⟨∞, 0⟩).re.isNaN && (ComplexFloat32.sin ⟨∞, 0⟩).im == 0
#guard ComplexFloat32.sin ⟨∞, 1⟩ ≈ ⟨NaN, NaN⟩
#guard (ComplexFloat32.sin ⟨NaN, 0⟩).re.isNaN && (ComplexFloat32.sin ⟨NaN, 0⟩).im == 0
#guard ComplexFloat32.sin ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.cos ⟨0, 0⟩ ≈ ⟨1, -0.0⟩
#guard ComplexFloat32.cos ⟨-0.0, 0⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat32.cos ⟨0, ∞⟩ ≈ ⟨∞, -0.0⟩
#guard ComplexFloat32.cos ⟨1, ∞⟩ ≈ ⟨∞, -∞⟩
#guard ComplexFloat32.cos ⟨-1, ∞⟩ ≈ ⟨∞, ∞⟩
#guard (ComplexFloat32.cos ⟨∞, 0⟩).re.isNaN && (ComplexFloat32.cos ⟨∞, 0⟩).im == 0
#guard ComplexFloat32.cos ⟨∞, 1⟩ ≈ ⟨NaN, NaN⟩
#guard (ComplexFloat32.cos ⟨NaN, 0⟩).re.isNaN && (ComplexFloat32.cos ⟨NaN, 0⟩).im == 0
#guard ComplexFloat32.tan ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.tan ⟨-0.0, -0.0⟩ ≈ ⟨-0.0, -0.0⟩
#guard ComplexFloat32.tan ⟨0, ∞⟩ ≈ ⟨0, 1⟩
#guard ComplexFloat32.tan ⟨1, ∞⟩ ≈ ⟨0, 1⟩
#guard ComplexFloat32.tan ⟨-1, -∞⟩ ≈ ⟨-0.0, -1⟩
#guard ComplexFloat32.tan ⟨∞, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.tan ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.acos ⟨0, 0⟩ ≈ ⟨halfPi, -0.0⟩
#guard ComplexFloat32.acos ⟨∞, 1⟩ ≈ ⟨0, -∞⟩
#guard ComplexFloat32.acos ⟨-∞, 1⟩ ≈ ⟨Float32.pi, -∞⟩
#guard ComplexFloat32.acos ⟨1, ∞⟩ ≈ ⟨halfPi, -∞⟩
#guard ComplexFloat32.acos ⟨NaN, ∞⟩ ≈ ⟨NaN, -∞⟩
-- `asin z = -I * asinh (I * z)` and `atan z = -I * atanh (I * z)`: the rows of G.6.2.2 and
-- G.6.2.3 turned by a quarter.
#guard ComplexFloat32.asin ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.asin ⟨-0.0, -0.0⟩ ≈ ⟨-0.0, -0.0⟩
#guard (ComplexFloat32.asin ⟨2, 0⟩).im > 0
#guard (ComplexFloat32.asin ⟨2, -0.0⟩).im < 0
#guard ComplexFloat32.asin ⟨1, ∞⟩ ≈ ⟨0, ∞⟩
#guard ComplexFloat32.asin ⟨-1, -∞⟩ ≈ ⟨-0.0, -∞⟩
#guard ComplexFloat32.asin ⟨∞, 1⟩ ≈ ⟨halfPi, ∞⟩
#guard ComplexFloat32.asin ⟨-∞, -1⟩ ≈ ⟨-halfPi, -∞⟩
#guard ComplexFloat32.asin ⟨∞, ∞⟩ ≈ ⟨halfPi / 2, ∞⟩
#guard ComplexFloat32.asin ⟨0, NaN⟩ ≈ ⟨0, NaN⟩
#guard (ComplexFloat32.asin ⟨NaN, ∞⟩).re.isNaN &&
  (ComplexFloat32.asin ⟨NaN, ∞⟩).im.isInf
#guard ComplexFloat32.asin ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat32.atan ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.atan ⟨-0.0, -0.0⟩ ≈ ⟨-0.0, -0.0⟩
#guard (ComplexFloat32.atan ⟨0, 2⟩).re == halfPi
#guard (ComplexFloat32.atan ⟨-0.0, 2⟩).re == -halfPi
#guard ComplexFloat32.atan ⟨0, 1⟩ ≈ ⟨0, ∞⟩
#guard ComplexFloat32.atan ⟨∞, 1⟩ ≈ ⟨halfPi, 0⟩
#guard ComplexFloat32.atan ⟨-∞, 1⟩ ≈ ⟨-halfPi, 0⟩
#guard ComplexFloat32.atan ⟨1, ∞⟩ ≈ ⟨halfPi, 0⟩
#guard ComplexFloat32.atan ⟨∞, ∞⟩ ≈ ⟨halfPi, 0⟩
#guard ComplexFloat32.atan ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard (ComplexFloat32.atan ⟨NaN, ∞⟩).re.isNaN && (ComplexFloat32.atan ⟨NaN, ∞⟩).im == 0
#guard ComplexFloat32.atan ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩

/-! ## Powers -/

-- Annex G only says that `cpow` may be computed as `exp (w * log z)` (G.6.4.1), so most rows
-- check closeness to the exact value.

#guard ComplexFloat32.pow ⟨NaN, NaN⟩ 0 ≈ ⟨1, 0⟩
#guard ComplexFloat32.pow ⟨∞, 1⟩ 0 ≈ ⟨1, 0⟩
#guard ComplexFloat32.pow 0 ⟨2, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat32.pow 0 ⟨0.5, 0⟩ ≈ ⟨0, 0⟩
#guard (ComplexFloat32.pow ⟨2, 0⟩ ⟨3, 0⟩).near ⟨8, 0⟩
#guard (ComplexFloat32.pow ⟨-1, 0⟩ ⟨0.5, 0⟩).near ⟨0, 1⟩
#guard (ComplexFloat32.pow ⟨-1, -0.0⟩ ⟨0.5, 0⟩).near ⟨0, -1⟩
#guard (ComplexFloat32.pow ⟨0, 1⟩ ⟨0, 1⟩).near ⟨0.20787957635076193, 0⟩
#guard (ComplexFloat32.pow ⟨1, 1⟩ ⟨2, 0⟩).near ⟨0, 2⟩
#guard (ComplexFloat32.pow ⟨3, 4⟩ ⟨0.5, 0⟩).near ⟨2, 1⟩
#guard (⟨0, 1⟩ : ComplexFloat32) ^ (4 : Nat) ≈ ⟨1, 0⟩
#guard (⟨1, 1⟩ : ComplexFloat32) ^ (10 : Nat) ≈ ⟨0, 32⟩
