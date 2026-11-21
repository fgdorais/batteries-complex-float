import BatteriesComplexFloat

/-!
# Accuracy of the single-precision elementary functions

Each function of `ComplexFloat32` is compared with the same function of `ComplexFloat` on the
same input, which is accurate to a few ulps of `Float` and so to a tiny fraction of an ulp of
`Float32`. The error of a part is in ulps of `Float32` at the reference value of that part. The
bounds hold on random inputs over several exponent ranges and on inputs near the unit circle
and the branch points `±1` and `±I`. The `accuracy` executable in `native/` measures the same
functions on many more inputs, and against the C library.
-/

namespace ComplexFloat32.Functions

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

/-- `n` random complex numbers with parts of exponent in `[lo, hi)`. -/
def randomInputs (n : Nat) (lo hi : Int) (seed : UInt64) : Array ComplexFloat32 := Id.run do
  let mut zs := #[]
  let mut s := seed
  for _ in [0:n] do
    let (x, s₁) := randomFloat s lo hi
    let (y, s₂) := randomFloat s₁ lo hi
    s := s₂
    zs := zs.push ⟨x, y⟩
  return zs

/-- `n` inputs near the unit circle and near `±1` and `±I`: `(1 + δ) e^{iθ}`, `±1 + δ + iδ'` and
`δ' ± I (1 + δ)`, with `δ` and `δ'` of exponent in `[-23, -2)`. -/
def hardInputs (n : Nat) (seed : UInt64) : Array ComplexFloat32 := Id.run do
  let mut zs := #[]
  let mut s := seed
  for i in [0:n] do
    let (d, s₁) := randomFloat s (-23) (-2)
    let (t, s₂) := randomFloat s₁ (-2) 2
    let (d', s₃) := randomFloat s₂ (-23) (-2)
    s := s₃
    zs := zs.push <| match i % 5 with
      | 0 => ⟨(1 + d) * Float32.cos t, (1 + d) * Float32.sin t⟩
      | 1 => ⟨1 + d, d'⟩
      | 2 => ⟨-1 + d, d'⟩
      | 3 => ⟨d', 1 + d⟩
      | _ => ⟨d', -1 + d⟩
  return zs

/-- The test inputs. -/
def inputs : Array ComplexFloat32 :=
  randomInputs 200 (-4) 4 1 ++ randomInputs 200 (-30) 30 2 ++ randomInputs 200 (-149) 128 3 ++
  hardInputs 200 4

/-- The error of a part `x` against the reference `r`, in ulps of `Float32` at `r`, or `none`
when `r` is not finite in `Float32` (and so says nothing about accuracy). -/
def partErr (x : Float32) (r : Float) : Option Float :=
  let u := r.toFloat32.ulp
  if !r.toFloat32.isFinite then none
  else if x.isNaN || x.isInf then some Float.inf
  else some ((x.toFloat - r).abs / u.toFloat)

/-- The largest error in ulps of `f` against `g`, over the inputs where the reference is finite
in `Float32`. -/
def maxErr (f : ComplexFloat32 → ComplexFloat32) (g : ComplexFloat → ComplexFloat) : Float :=
  Id.run do
  let mut m := 0
  for z in inputs do
    let r := g ⟨z.re.toFloat, z.im.toFloat⟩
    let v := f z
    match partErr v.re r.re, partErr v.im r.im with
    | some a, some b => m := max m (max a b)
    | _, _ => pure ()
  return m

#guard maxErr ComplexFloat32.exp ComplexFloat.exp ≤ 2.5
#guard maxErr ComplexFloat32.log ComplexFloat.log ≤ 3
#guard maxErr ComplexFloat32.sqrt ComplexFloat.sqrt ≤ 2.5
#guard maxErr ComplexFloat32.sin ComplexFloat.sin ≤ 3
#guard maxErr ComplexFloat32.cos ComplexFloat.cos ≤ 3
#guard maxErr ComplexFloat32.tan ComplexFloat.tan ≤ 6
#guard maxErr ComplexFloat32.sinh ComplexFloat.sinh ≤ 3
#guard maxErr ComplexFloat32.cosh ComplexFloat.cosh ≤ 3
#guard maxErr ComplexFloat32.tanh ComplexFloat.tanh ≤ 6
#guard maxErr ComplexFloat32.asin ComplexFloat.asin ≤ 4.5
#guard maxErr ComplexFloat32.acos ComplexFloat.acos ≤ 4.5
#guard maxErr ComplexFloat32.atan ComplexFloat.atan ≤ 4.5
#guard maxErr ComplexFloat32.asinh ComplexFloat.asinh ≤ 4.5
#guard maxErr ComplexFloat32.acosh ComplexFloat.acosh ≤ 4.5
#guard maxErr ComplexFloat32.atanh ComplexFloat.atanh ≤ 4.5
#guard maxErr (fun z => ⟨z.abs, 0⟩) (fun z => ⟨z.abs, 0⟩) ≤ 1
#guard maxErr (fun z => ⟨z.arg, 0⟩) (fun z => ⟨z.arg, 0⟩) ≤ 1.5

end ComplexFloat32.Functions
