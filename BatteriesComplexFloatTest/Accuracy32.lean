import BatteriesComplexFloat
import Batteries.Data.Float.Rat

/-!
# Accuracy of single-precision multiplication and division

Products and quotients are compared with the exact result, computed in `Rat` and then rounded
to `Float32`. Each part must be within 1 ulp of it for multiplication and within 3 ulps for
division, on random inputs over several exponent ranges, on inputs where the two products in a
part nearly cancel, and where the parts of an operand differ greatly in size.
-/

namespace ComplexFloat32.Accuracy

/-- A xorshift64 step. -/
def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A random float of either sign with exponent uniform in `[lo, hi)`, and the next seed. -/
def randomFloat (s : UInt64) (lo hi : Int) : Float32 × UInt64 :=
  let s₁ := next s
  let s₂ := next s₁
  let e := lo + ((s₁ >>> 11).toNat % (hi - lo).toNat : Nat)
  let m : Float32 := (1 : Float32) + (s₂ >>> 40).toFloat32 / (16777216 : Float32)
  (if s₂ &&& 1 == 1 then -Float32.ldexp m e else Float32.ldexp m e, s₂)

/-- `n` pairs of random complex numbers with parts of exponent in `[lo, hi)`. When `cancel` is
set, the imaginary part of the second number is adjusted so that the real part of the product
nearly cancels. -/
def randomPairs (n : Nat) (lo hi : Int) (seed : UInt64) (cancel := false) :
    Array (ComplexFloat32 × ComplexFloat32) := Id.run do
  let mut out := #[]
  let mut s := seed
  for _ in [0:n] do
    let (a, s₁) := randomFloat s lo hi
    let (b, s₂) := randomFloat s₁ lo hi
    let (c, s₃) := randomFloat s₂ lo hi
    let (d, s₄) := randomFloat s₃ lo hi
    s := s₄
    let d := if cancel then a * c / b * (1 + Float32.copySign (Float32.twoPow (-18)) d) else d
    out := out.push (⟨a, b⟩, ⟨c, d⟩)
  return out

/-- The exact value of a finite `Float32`. -/
def toRat? (x : Float32) : Option Rat :=
  x.toRatParts.map fun (m, e) =>
    if e ≥ 0 then (m * 2 ^ e.toNat : Int) else m / (2 ^ (-e).toNat : Nat)

/-- The `Float32` nearest to `r`: the rounding of `r` to `Float` and then to `Float32` is off by
at most one step, so the nearest of it and its neighbours is taken. -/
def roundRat (r : Rat) : Float32 := Id.run do
  let f := r.toFloat.toFloat32
  let dist (x : Float32) : Option Rat := (toRat? x).map fun q => (q - r).abs
  let mut best := f
  for g in [f.nextUp, f.nextDown] do
    match dist g, dist best with
    | some dg, some db => if dg < db then best := g
    | _, _ => pure ()
  return best

/-- The distance in ulps from `x` to the rounding of the exact value `r`, or `none` when the
rounding is not finite (and so says nothing about accuracy). -/
def err (x : Float32) (r : Rat) : Option Nat :=
  let f := roundRat r
  if f.isFinite then x.ulpDistance? f else none

/-- The largest error in ulps of `f` against the exact `g`, over the pairs where all inputs are
finite. -/
def maxErr (f : ComplexFloat32 → ComplexFloat32 → ComplexFloat32)
    (g : Rat → Rat → Rat → Rat → Option (Rat × Rat))
    (zs : Array (ComplexFloat32 × ComplexFloat32)) :
    Nat := Id.run do
  let mut m := 0
  for (z, w) in zs do
    match toRat? z.re, toRat? z.im, toRat? w.re, toRat? w.im with
    | some a, some b, some c, some d =>
      match g a b c d with
      | some (x, y) =>
        let v := f z w
        m := max m (max ((err v.re x).getD 0) ((err v.im y).getD 0))
      | none => pure ()
    | _, _, _, _ => pure ()
  return m

/-- The exact product. -/
def exactMul (a b c d : Rat) : Option (Rat × Rat) := some (a * c - b * d, a * d + b * c)

/-- The exact quotient. -/
def exactDiv (a b c d : Rat) : Option (Rat × Rat) :=
  let n := c * c + d * d
  if n == 0 then none else some ((a * c + b * d) / n, (b * c - a * d) / n)

/-- The test inputs. -/
def inputs : Array (ComplexFloat32 × ComplexFloat32) :=
  randomPairs 300 (-8) 8 1 ++
  randomPairs 300 (-8) 8 2 (cancel := true) ++
  randomPairs 300 (-60) 60 3 ++
  randomPairs 200 (-75) (-60) 4 ++
  randomPairs 200 (-75) (-60) 5 (cancel := true) ++
  randomPairs 200 50 63 6 ++
  randomPairs 200 (-149) 127 7

#guard maxErr (· * ·) exactMul inputs ≤ 1
#guard maxErr (· / ·) exactDiv inputs ≤ 3

-- The textbook formulas fail these bounds on the same inputs.
#guard maxErr (fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩) exactMul
  inputs > 100

end ComplexFloat32.Accuracy
