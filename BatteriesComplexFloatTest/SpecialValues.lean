import BatteriesComplexFloat

/-!
# Special values from Annex G of the C standard

`z ≈ w` holds when each part of `z` and `w` is NaN in both, or is the same float with the same
sign (so `+0` and `-0` differ). Finite non-zero results are compared exactly only where Annex G
fixes them; other cases are left to the comparison with the C library in the `native` package.
-/

open ComplexFloat

local notation "∞" => Float.inf
local notation "NaN" => Float.nan

/-- Same kind and sign in each part, NaNs equal. -/
def Float.same (x y : Float) : Bool :=
  x.isNaN && y.isNaN || x == y && x.signBit == y.signBit

/-- `Float.same` in both parts. -/
def ComplexFloat.same (z w : ComplexFloat) : Bool := z.re.same w.re && z.im.same w.im

local infix:50 " ≈ " => ComplexFloat.same

/-- `π / 2`. -/
def halfPi : Float := 1.5707963267948966

/-! ## Arithmetic -/

-- Infinity recovery in products (G.5.1).
#guard (⟨∞, NaN⟩ : ComplexFloat) * ⟨2, 0⟩ |>.isInf
#guard (⟨∞, 0⟩ : ComplexFloat) * ⟨NaN, 1⟩ |>.isInf
#guard (⟨1e300, 1e300⟩ : ComplexFloat) * ⟨1e300, 1e300⟩ |>.isInf
#guard ((⟨1, 2⟩ : ComplexFloat) * ⟨3, 4⟩) ≈ ⟨-5, 10⟩

-- Division: infinite and zero results, no premature overflow (G.5.2).
#guard (⟨1, 1⟩ : ComplexFloat) / ⟨0, 0⟩ |>.isInf
#guard (⟨∞, NaN⟩ : ComplexFloat) / ⟨2, 1⟩ |>.isInf
#guard ((⟨1, 1⟩ : ComplexFloat) / ⟨∞, NaN⟩) ≈ ⟨0, 0⟩
#guard ((⟨1e300, 1e300⟩ : ComplexFloat) / ⟨1e300, 1e300⟩) ≈ ⟨1, 0⟩
#guard ((⟨1e-300, 1e-300⟩ : ComplexFloat) / ⟨1e-300, 1e-300⟩) ≈ ⟨1, 0⟩
#guard ((⟨1, 2⟩ : ComplexFloat) / ⟨1, 2⟩) ≈ ⟨1, 0⟩

-- Mixed real and complex operands keep signs of zeros.
#guard ((1 : Float) + (⟨-2, -0.0⟩ : ComplexFloat)) ≈ ⟨-1, -0.0⟩
#guard ((⟨-2, -0.0⟩ : ComplexFloat) * (2 : Float)) ≈ ⟨-4, -0.0⟩

-- `abs` does not overflow or underflow.
#guard (⟨3e300, 4e300⟩ : ComplexFloat).abs == 5e300
#guard (⟨3e-300, 4e-300⟩ : ComplexFloat).abs == 5e-300
#guard (⟨∞, NaN⟩ : ComplexFloat).abs == ∞
#guard (⟨NaN, -∞⟩ : ComplexFloat).abs == ∞

-- `proj`.
#guard (⟨NaN, -∞⟩ : ComplexFloat).proj ≈ ⟨∞, -0.0⟩
#guard (⟨1, 2⟩ : ComplexFloat).proj ≈ ⟨1, 2⟩

/-! ## Exponential and logarithm (G.6.3) -/

#guard ComplexFloat.exp ⟨0, 0⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat.exp ⟨-0.0, -0.0⟩ ≈ ⟨1, -0.0⟩
#guard ComplexFloat.exp ⟨∞, 0⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat.exp ⟨-∞, 1⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.exp ⟨-∞, 3⟩ ≈ ⟨-0.0, 0⟩
#guard (ComplexFloat.exp ⟨∞, ∞⟩).re.isInf && (ComplexFloat.exp ⟨∞, ∞⟩).im.isNaN
#guard ComplexFloat.exp ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat.exp ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat.exp ⟨1, ∞⟩ ≈ ⟨NaN, NaN⟩
-- No premature overflow: `exp 710` overflows, `exp 710 * cos 3` does not either, but
-- `exp 710 * sin 1e-300` is finite.
#guard (ComplexFloat.exp ⟨710, 1e-300⟩).im.isFinite

#guard ComplexFloat.log ⟨-0.0, 0⟩ ≈ ⟨-∞, Float.pi⟩
#guard ComplexFloat.log ⟨0, 0⟩ ≈ ⟨-∞, 0⟩
#guard ComplexFloat.log ⟨-1, 0⟩ ≈ ⟨0, Float.pi⟩
#guard ComplexFloat.log ⟨-1, -0.0⟩ ≈ ⟨0, -Float.pi⟩
#guard ComplexFloat.log ⟨1, ∞⟩ ≈ ⟨∞, halfPi⟩
#guard ComplexFloat.log ⟨∞, NaN⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat.log ⟨NaN, -∞⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat.log ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat.log ⟨1, 0⟩ ≈ ⟨0, 0⟩

/-! ## Square root (G.6.4.2) -/

#guard ComplexFloat.sqrt ⟨-0.0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.sqrt ⟨0, -0.0⟩ ≈ ⟨0, -0.0⟩
#guard ComplexFloat.sqrt ⟨NaN, ∞⟩ ≈ ⟨∞, ∞⟩
#guard ComplexFloat.sqrt ⟨1, -∞⟩ ≈ ⟨∞, -∞⟩
#guard ComplexFloat.sqrt ⟨-∞, 1⟩ ≈ ⟨0, ∞⟩
#guard ComplexFloat.sqrt ⟨∞, -1⟩ ≈ ⟨∞, -0.0⟩
#guard ComplexFloat.sqrt ⟨∞, NaN⟩ ≈ ⟨∞, NaN⟩
#guard (ComplexFloat.sqrt ⟨-∞, NaN⟩).im.isInf
#guard ComplexFloat.sqrt ⟨-4, 0⟩ ≈ ⟨0, 2⟩
#guard ComplexFloat.sqrt ⟨-4, -0.0⟩ ≈ ⟨0, -2⟩
#guard ComplexFloat.sqrt ⟨1e308, 1e308⟩ |>.isFinite
#guard ComplexFloat.sqrt ⟨4e-320, 0⟩ ≈ ⟨Float.sqrt 4e-320, 0⟩

/-! ## Hyperbolic functions (G.6.2) -/

#guard ComplexFloat.sinh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.sinh ⟨-0.0, -0.0⟩ ≈ ⟨-0.0, -0.0⟩
#guard (ComplexFloat.sinh ⟨0, ∞⟩).im.isNaN && (ComplexFloat.sinh ⟨0, ∞⟩).re == 0
#guard ComplexFloat.sinh ⟨1, ∞⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat.sinh ⟨∞, 0⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat.sinh ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat.sinh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩

#guard ComplexFloat.cosh ⟨0, 0⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat.cosh ⟨-0.0, 0⟩ ≈ ⟨1, -0.0⟩
#guard (ComplexFloat.cosh ⟨0, ∞⟩).re.isNaN && (ComplexFloat.cosh ⟨0, ∞⟩).im == 0
#guard ComplexFloat.cosh ⟨∞, 0⟩ ≈ ⟨∞, 0⟩
#guard (ComplexFloat.cosh ⟨NaN, 0⟩).im == 0

#guard ComplexFloat.tanh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.tanh ⟨∞, 1⟩ ≈ ⟨1, 0⟩
#guard ComplexFloat.tanh ⟨∞, 2⟩ ≈ ⟨1, -0.0⟩
#guard (ComplexFloat.tanh ⟨∞, ∞⟩).re == 1
#guard ComplexFloat.tanh ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat.tanh ⟨1, ∞⟩ ≈ ⟨NaN, NaN⟩
-- No overflow in the intermediate quantities.
#guard ComplexFloat.tanh ⟨400, 1⟩ ≈ ⟨1, 0⟩
#guard (ComplexFloat.tanh ⟨20, 1⟩).im > 0

/-! ## Inverse hyperbolic functions (G.6.2) -/

#guard ComplexFloat.acosh ⟨0, 0⟩ ≈ ⟨0, halfPi⟩
#guard ComplexFloat.acosh ⟨1, ∞⟩ ≈ ⟨∞, halfPi⟩
#guard ComplexFloat.acosh ⟨-∞, 1⟩ ≈ ⟨∞, Float.pi⟩
#guard ComplexFloat.acosh ⟨∞, -1⟩ ≈ ⟨∞, -0.0⟩
#guard ComplexFloat.acosh ⟨∞, NaN⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat.acosh ⟨NaN, ∞⟩ ≈ ⟨∞, NaN⟩
#guard ComplexFloat.acosh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
-- On the branch cut, the sign of the imaginary part picks the side.
#guard (ComplexFloat.acosh ⟨-2, 0⟩).im == Float.pi
#guard (ComplexFloat.acosh ⟨-2, -0.0⟩).im == -Float.pi

#guard ComplexFloat.asinh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.asinh ⟨1, ∞⟩ ≈ ⟨∞, halfPi⟩
#guard ComplexFloat.asinh ⟨∞, 1⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat.asinh ⟨NaN, 0⟩ ≈ ⟨NaN, 0⟩
#guard ComplexFloat.asinh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard (ComplexFloat.asinh ⟨0, 2⟩).re > 0
#guard (ComplexFloat.asinh ⟨-0.0, 2⟩).re < 0

#guard ComplexFloat.atanh ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.atanh ⟨0, NaN⟩ ≈ ⟨0, NaN⟩
#guard ComplexFloat.atanh ⟨1, 0⟩ ≈ ⟨∞, 0⟩
#guard ComplexFloat.atanh ⟨1, ∞⟩ ≈ ⟨0, halfPi⟩
#guard ComplexFloat.atanh ⟨1, NaN⟩ ≈ ⟨NaN, NaN⟩
#guard ComplexFloat.atanh ⟨∞, 1⟩ ≈ ⟨0, halfPi⟩
#guard ComplexFloat.atanh ⟨∞, NaN⟩ ≈ ⟨0, NaN⟩
#guard ComplexFloat.atanh ⟨NaN, 1⟩ ≈ ⟨NaN, NaN⟩
#guard (ComplexFloat.atanh ⟨NaN, ∞⟩).im == halfPi
#guard (ComplexFloat.atanh ⟨2, 0⟩).im == halfPi
#guard (ComplexFloat.atanh ⟨2, -0.0⟩).im == -halfPi

/-! ## Trigonometric functions and their inverses (G.6) -/

#guard ComplexFloat.sin ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.cos ⟨0, 0⟩ ≈ ⟨1, -0.0⟩
#guard ComplexFloat.tan ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard ComplexFloat.acos ⟨0, 0⟩ ≈ ⟨halfPi, -0.0⟩
#guard ComplexFloat.acos ⟨∞, 1⟩ ≈ ⟨0, -∞⟩
#guard ComplexFloat.acos ⟨-∞, 1⟩ ≈ ⟨Float.pi, -∞⟩
#guard ComplexFloat.acos ⟨1, ∞⟩ ≈ ⟨halfPi, -∞⟩
#guard ComplexFloat.acos ⟨NaN, ∞⟩ ≈ ⟨NaN, -∞⟩
#guard ComplexFloat.asin ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard (ComplexFloat.asin ⟨2, 0⟩).im > 0
#guard (ComplexFloat.asin ⟨2, -0.0⟩).im < 0
#guard ComplexFloat.atan ⟨0, 0⟩ ≈ ⟨0, 0⟩
#guard (ComplexFloat.atan ⟨0, 2⟩).re == halfPi
#guard (ComplexFloat.atan ⟨-0.0, 2⟩).re == -halfPi

/-! ## Powers -/

#guard ComplexFloat.pow ⟨NaN, NaN⟩ 0 ≈ ⟨1, 0⟩
#guard ComplexFloat.pow 0 ⟨2, 0⟩ ≈ ⟨0, 0⟩
#guard (⟨0, 1⟩ : ComplexFloat) ^ (4 : Nat) ≈ ⟨1, 0⟩
#guard (⟨1, 1⟩ : ComplexFloat) ^ (10 : Nat) ≈ ⟨0, 32⟩
