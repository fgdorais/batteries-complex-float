import BatteriesComplexFloatNative

/-!
Compares the pure Lean `ComplexFloat32` functions with the C library.

* On a grid of special inputs (zeros of both signs, ±1, infinities, NaN, tiny and huge
  numbers, ...), every component must agree in kind: NaN, infinity of the same sign, zero of the
  same sign, or a finite number within a few ulps.
* On random inputs, the relative error `|f z - g z| / |g z|` is reported in units of `2⁻²⁴`.
-/

open ComplexFloat32

/-- Position of `x` in the ordered list of floats (`-0` and `+0` are both `0`). -/
def ord (x : Float32) : Int :=
  let b := x.toBits
  if b >>> 31 == 1 then -(b &&& 0x7FFFFFFF).toNat else b.toNat

/-- Distance in ulps between two finite floats. -/
def ulps (x y : Float32) : Nat := (ord x - ord y).natAbs

/--
How two components disagree, if they do beyond `tol` ulps. When `lax` is set (the other
components are both NaN), signs of infinities and zeros are not compared: Annex G leaves them
unspecified in most such cases.
-/
def compareComponent (tol : Nat) (x y : Float32) (lax := false) : Option String :=
  if x.isNaN && y.isNaN then none
  else if x.isNaN || y.isNaN then some "NaN"
  else if x.isInf || y.isInf then
    if x == y || lax && x.isInf && y.isInf then none else some "inf"
  else if x == 0 && y == 0 then
    if x.signBit == y.signBit || lax then none else some "sign of zero"
  else if ulps x y ≤ tol then none
  else some s!"{ulps x y} ulps"

/-- Prints a float precisely, so that signs of zeros show. -/
def showF (x : Float32) : String :=
  if x == 0 then (if x.signBit then "-0" else "+0")
  else if !x.isFinite || (1e-4 ≤ x.abs && x.abs < 1e6) then toString x
  else
    let (m, e) := x.frExp
    s!"{m}p{e}"

def showC (z : ComplexFloat32) : String := s!"({showF z.re}, {showF z.im})"

def specials : Array Float32 := #[
  0, -0, 1, -1, 0.5, -0.5, 2, -2, 3, -3, 1e-5, -1e-5, 1e-40, -1e-40, 1e-37, -1e37,
  1e37, 1e19, -1e19, 1.5707963267948966, -1.5707963267948966, 3.141592653589793,
  9, -9, 12, -12, 89, -89, 100, -100, Float32.inf, -Float32.inf, Float32.nan]

def specialInputs : Array ComplexFloat32 := Id.run do
  let mut zs := #[]
  for x in specials do
    for y in specials do
      zs := zs.push ⟨x, y⟩
  return zs

/-- A xorshift64 step. -/
def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A random float of either sign with magnitude `2 ^ e` for `e` uniform in `[lo, hi)`. -/
def randomFloat (s : UInt64) (lo hi : Int) : Float32 × UInt64 :=
  let s₁ := next s
  let s₂ := next s₁
  let e := lo + ((s₁ >>> 11).toNat % (hi - lo).toNat : Nat)
  let m : Float32 := (1.0 : Float32) + UInt64.toFloat32 (s₂ >>> 40) / (16777216.0 : Float32)
  let x := Float32.ldexp m e
  (if s₂ &&& 1 == 1 then -x else x, s₂)

def randomInputs (n : Nat) (lo hi : Int) (seed : UInt64) : Array ComplexFloat32 := Id.run do
  let mut zs := #[]
  let mut s := seed
  for _ in [0:n] do
    let (x, s₁) := randomFloat s lo hi
    let (y, s₂) := randomFloat s₁ lo hi
    s := s₂
    zs := zs.push ⟨x, y⟩
  return zs

/-- Relative error of `z` against `ref`, in units of `2⁻²⁴`, computed in double precision. -/
def relErr (z ref : ComplexFloat32) : Float32 :=
  if !z.isFinite || !ref.isFinite then
    if (compareComponent 8 z.re ref.re).isNone && (compareComponent 8 z.im ref.im).isNone then 0
    else Float32.inf
  else
    let a := ref.abs
    if a == 0 then (if z.abs == 0 then 0 else Float32.inf)
    else (Float.hypot (z.re.toFloat - ref.re.toFloat) (z.im.toFloat - ref.im.toFloat) /
      Float.hypot ref.re.toFloat ref.im.toFloat * 16777216.0).toFloat32

structure Report where
  name : String
  specialBad : Array String := #[]
  specialCount : Nat := 0
  maxErr : Float32 := 0
  worst : String := ""
  badRandom : Nat := 0

def check (name : String) (f g : ComplexFloat32 → ComplexFloat32) (tol : Nat := 4)
    (randoms : Array ComplexFloat32) : Report := Id.run do
  let mut r : Report := { name }
  for z in specialInputs do
    let a := f z; let b := g z
    let laxRe := a.im.isNaN && b.im.isNaN
    let laxIm := a.re.isNaN && b.re.isNaN
    match compareComponent tol a.re b.re laxRe, compareComponent tol a.im b.im laxIm with
    | none, none => pure ()
    | p, q =>
      r := { r with specialCount := r.specialCount + 1 }
      if r.specialBad.size < 12 then
        let why := ", ".intercalate ([p.map ("re: " ++ ·), q.map ("im: " ++ ·)].filterMap id)
        let line := s!"{showC z}: lean {showC a}, C {showC b} [{why}]"
        r := { r with specialBad := r.specialBad.push line }
  for z in randoms do
    let e := relErr (f z) (g z)
    if e > 8 then r := { r with badRandom := r.badRandom + 1 }
    if e > r.maxErr || e.isNaN then
      r := { r with maxErr := e, worst := s!"{showC z}: lean {showC (f z)}, C {showC (g z)}" }
  return r

def checkBinary (name : String) (f g : ComplexFloat32 → ComplexFloat32 → ComplexFloat32)
    (randoms : Array ComplexFloat32) : Report := Id.run do
  let mut r : Report := { name }
  let zs := specialInputs
  for z in zs do
    for w in zs do
      let a := f z w; let b := g z w
      -- Annex G requires an infinite result in these cases but does not fix the parts.
      if a.isInf && b.isInf then continue
      let laxRe := a.im.isNaN && b.im.isNaN
      let laxIm := a.re.isNaN && b.re.isNaN
      match compareComponent 2 a.re b.re laxRe, compareComponent 2 a.im b.im laxIm with
      | none, none => pure ()
      | p, q =>
        r := { r with specialCount := r.specialCount + 1 }
        if r.specialBad.size < 12 then
          let why := ", ".intercalate ([p.map ("re: " ++ ·), q.map ("im: " ++ ·)].filterMap id)
          let line := s!"{showC z} {showC w}: lean {showC a}, C {showC b} [{why}]"
          r := { r with specialBad := r.specialBad.push line }
  for i in [0:randoms.size - 1] do
    let z := randoms[i]!; let w := randoms[i+1]!
    let e := relErr (f z w) (g z w)
    if e > 8 then r := { r with badRandom := r.badRandom + 1 }
    if e > r.maxErr || e.isNaN then
      let worst := s!"{showC z} {showC w}: lean {showC (f z w)}, C {showC (g z w)}"
      r := { r with maxErr := e, worst }
  return r

def printReport (r : Report) : IO Unit := do
  IO.println <| s!"== {r.name}: {r.specialCount} special mismatches, " ++
    s!"random max error {r.maxErr} eps, {r.badRandom} above 8 eps"
  for s in r.specialBad do IO.println s!"   {s}"
  if r.maxErr > 8 then IO.println s!"   worst random: {r.worst}"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20000
  -- Moderate inputs, where accuracy matters most, then the full exponent range.
  let randoms := randomInputs n (-8) 8 0x9E3779B97F4A7C15
    ++ randomInputs n (-149) 127 0x2545F4914F6CDD1D
  let reports := #[
    checkBinary "mul" (· * ·) Native.mul randoms,
    checkBinary "div" (· / ·) Native.div randoms,
    check "abs" (fun z => ⟨z.abs, 0⟩) (fun z => ⟨Native.abs z, 0⟩) (randoms := randoms),
    check "arg" (fun z => ⟨z.arg, 0⟩) (fun z => ⟨Native.arg z, 0⟩) (randoms := randoms),
    check "proj" proj Native.proj (randoms := randoms),
    check "exp" ComplexFloat32.exp Native.exp (randoms := randoms),
    check "log" ComplexFloat32.log Native.log (randoms := randoms),
    check "sqrt" ComplexFloat32.sqrt Native.sqrt (randoms := randoms),
    check "sinh" ComplexFloat32.sinh Native.sinh (randoms := randoms),
    check "cosh" ComplexFloat32.cosh Native.cosh (randoms := randoms),
    check "tanh" ComplexFloat32.tanh Native.tanh (randoms := randoms),
    check "sin" ComplexFloat32.sin Native.sin (randoms := randoms),
    check "cos" ComplexFloat32.cos Native.cos (randoms := randoms),
    check "tan" ComplexFloat32.tan Native.tan (randoms := randoms),
    check "asinh" ComplexFloat32.asinh Native.asinh (randoms := randoms),
    check "acosh" ComplexFloat32.acosh Native.acosh (randoms := randoms),
    check "atanh" ComplexFloat32.atanh Native.atanh (randoms := randoms),
    check "asin" ComplexFloat32.asin Native.asin (randoms := randoms),
    check "acos" ComplexFloat32.acos Native.acos (randoms := randoms),
    check "atan" ComplexFloat32.atan Native.atan (randoms := randoms)]
  for r in reports do printReport r
