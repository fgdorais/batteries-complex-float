import BatteriesComplexFloatNative
import Batteries.Data.Float.Rat

/-!
Measures the accuracy of the pure Lean functions and of the C library's, in both precisions,
against higher-precision references: `long double complex` for `ComplexFloat`, `double complex`
for `ComplexFloat32`, and exact rational arithmetic for `*` and `/`.

Errors are in ulps: `comp` is the largest error of a part, in ulps of that part; `norm` is
`|f z - ref| / |ref|` in units of `2⁻⁵³` (or `2⁻²⁴`). Inputs whose reference is not finite are
skipped. Usage: `accuracy [n]`, with `n` random inputs per range; `accuracy worst` and
`accuracy worst32` print the inputs with the largest errors.
-/

open ComplexFloat

/-! ## Random inputs -/

def next (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

def randomFloat (s : UInt64) (lo hi : Int) : Float × UInt64 :=
  let s₁ := next s
  let s₂ := next s₁
  let e := lo + ((s₁ >>> 11).toNat % (hi - lo).toNat : Nat)
  let m : Float := (1.0 : Float) + UInt64.toFloat (s₂ >>> 11) / (9007199254740992.0 : Float)
  let x := Float.ldexp m e
  (if s₂ &&& 1 == 1 then -x else x, s₂)

def randomInputs (n : Nat) (lo hi : Int) (seed : UInt64) : Array ComplexFloat := Id.run do
  let mut zs := #[]
  let mut s := seed
  for _ in [0:n] do
    let (x, s₁) := randomFloat s lo hi
    let (y, s₂) := randomFloat s₁ lo hi
    s := s₂
    zs := zs.push ⟨x, y⟩
  return zs

/-- Inputs near the unit circle and near the branch points `±1` and `±I`: `c (1 + δ) e^{iθ}`
with `δ` of exponent in `[-52, -4)` and `c` one of `1`, `±1 + δ'`, `±I + δ'`. -/
def hardInputs (n : Nat) (seed : UInt64) : Array ComplexFloat := Id.run do
  let mut zs := #[]
  let mut s := seed
  for i in [0:n] do
    let (d, s₁) := randomFloat s (-52) (-4)
    let (t, s₂) := randomFloat s₁ (-2) 2
    let (d', s₃) := randomFloat s₂ (-52) (-4)
    s := s₃
    zs := zs.push <| match i % 5 with
      | 0 => ⟨(1 + d) * Float.cos t, (1 + d) * Float.sin t⟩
      | 1 => ⟨1 + d, d'⟩
      | 2 => ⟨-1 + d, d'⟩
      | 3 => ⟨d', 1 + d⟩
      | _ => ⟨d', -1 + d⟩
  return zs

/-! ## Errors -/

/-- The ulp of a double near `v`. -/
def ulp64 (v : Float) : Float :=
  match v.exponent? with
  | some e => Float.ldexp 1 (max e (-1022) - 52)
  | none => Float.ldexp 1 (-1074)

/-- The ulp of a single near `v`. -/
def ulp32 (v : Float) : Float :=
  match v.toFloat32.toFloat.exponent? with
  | some e => Float.ldexp 1 (max e (-126) - 23)
  | none => Float.ldexp 1 (-149)

/-- Error of a part `x` against `hi + lo`, in ulps of `u`. -/
def partErr (x hi lo u : Float) : Float :=
  if x.isNaN || x.isInf then (if x == hi then 0 else Float.inf)
  else ((x - hi) - lo).abs / u

/-- `(comp, norm)` errors of `z` against the reference `hi + lo`, in units of `ulp` and `eps`.
The norm error is relative to `|ref|` or `tiny`, whichever is larger, so that results that
underflow count by their absolute error. -/
def errs (x y hr hi lr li : Float) (ulp : Float → Float) (eps tiny : Float) : Float × Float :=
  let cr := partErr x hr lr (ulp hr)
  let ci := partErr y hi li (ulp hi)
  let n :=
    if !(x.isFinite && y.isFinite) then Float.inf
    else
      let a := max (Float.hypot hr hi) tiny
      Float.hypot ((x - hr) - lr) ((y - hi) - li) / a / eps
  (max cr ci, n)

/-- Half an ulp of 1, and the smallest positive normal number, in each precision. -/
def eps64 : Float := 1.1102230246251565e-16
def tiny64 : Float := 2.2250738585072014e-308
def eps32 : Float := 5.960464477539063e-8
def tiny32 : Float := 1.1754943508222875e-38

structure Stat where
  lean : Float × Float := (0, 0)
  c : Float × Float := (0, 0)
  /-- Inputs where the C result is off by more than one more ulp than ours, and the reverse. -/
  cWorse : Nat := 0
  leanWorse : Nat := 0
  count : Nat := 0
  /-- The input with the largest `comp` error of ours. -/
  worst : String := ""

def Stat.add (s : Stat) (l c : Float × Float) (input : String := "") : Stat :=
  { worst := if l.1 > s.lean.1 then input else s.worst
    lean := (max s.lean.1 l.1, max s.lean.2 l.2), c := (max s.c.1 c.1, max s.c.2 c.2)
    cWorse := s.cWorse + (if c.1 > l.1 + 1 then 1 else 0),
    leanWorse := s.leanWorse + (if l.1 > c.1 + 1 then 1 else 0), count := s.count + 1 }

def fmt (x : Float) : String :=
  if x.isInf then "inf" else if x ≥ 1e6 then s!"{x.toUInt64.toNat}"
  else toString ((x * 100).round / 100) |>.take 8 |>.toString

def Stat.row (name range : String) (s : Stat) : String :=
  s!"| {name} | {range} | {fmt s.lean.1} | {fmt s.c.1} | {fmt s.lean.2} | {fmt s.c.2} | " ++
    s!"{s.cWorse} | {s.leanWorse} | {s.count} |"

/-! ## Functions -/

def leanFn64 : RefFn → ComplexFloat → ComplexFloat
  | .exp => ComplexFloat.exp | .log => ComplexFloat.log | .sqrt => ComplexFloat.sqrt
  | .sin => ComplexFloat.sin | .cos => ComplexFloat.cos | .tan => ComplexFloat.tan
  | .sinh => ComplexFloat.sinh | .cosh => ComplexFloat.cosh | .tanh => ComplexFloat.tanh
  | .asin => ComplexFloat.asin | .acos => ComplexFloat.acos | .atan => ComplexFloat.atan
  | .asinh => ComplexFloat.asinh | .acosh => ComplexFloat.acosh | .atanh => ComplexFloat.atanh
  | .abs => fun z => ⟨z.abs, 0⟩ | .arg => fun z => ⟨z.arg, 0⟩

def cFn64 : RefFn → ComplexFloat → ComplexFloat
  | .exp => Native.exp | .log => Native.log | .sqrt => Native.sqrt
  | .sin => Native.sin | .cos => Native.cos | .tan => Native.tan
  | .sinh => Native.sinh | .cosh => Native.cosh | .tanh => Native.tanh
  | .asin => Native.asin | .acos => Native.acos | .atan => Native.atan
  | .asinh => Native.asinh | .acosh => Native.acosh | .atanh => Native.atanh
  | .abs => fun z => ⟨Native.abs z, 0⟩ | .arg => fun z => ⟨Native.arg z, 0⟩

def leanFn32 : RefFn → ComplexFloat32 → ComplexFloat32
  | .exp => ComplexFloat32.exp | .log => ComplexFloat32.log | .sqrt => ComplexFloat32.sqrt
  | .sin => ComplexFloat32.sin | .cos => ComplexFloat32.cos | .tan => ComplexFloat32.tan
  | .sinh => ComplexFloat32.sinh | .cosh => ComplexFloat32.cosh | .tanh => ComplexFloat32.tanh
  | .asin => ComplexFloat32.asin | .acos => ComplexFloat32.acos | .atan => ComplexFloat32.atan
  | .asinh => ComplexFloat32.asinh | .acosh => ComplexFloat32.acosh
  | .atanh => ComplexFloat32.atanh
  | .abs => fun z => ⟨z.abs, 0⟩ | .arg => fun z => ⟨z.arg, 0⟩

def cFn32 : RefFn → ComplexFloat32 → ComplexFloat32
  | .exp => ComplexFloat32.Native.exp | .log => ComplexFloat32.Native.log
  | .sqrt => ComplexFloat32.Native.sqrt | .sin => ComplexFloat32.Native.sin
  | .cos => ComplexFloat32.Native.cos | .tan => ComplexFloat32.Native.tan
  | .sinh => ComplexFloat32.Native.sinh | .cosh => ComplexFloat32.Native.cosh
  | .tanh => ComplexFloat32.Native.tanh | .asin => ComplexFloat32.Native.asin
  | .acos => ComplexFloat32.Native.acos | .atan => ComplexFloat32.Native.atan
  | .asinh => ComplexFloat32.Native.asinh | .acosh => ComplexFloat32.Native.acosh
  | .atanh => ComplexFloat32.Native.atanh
  | .abs => fun z => ⟨ComplexFloat32.Native.abs z, 0⟩
  | .arg => fun z => ⟨ComplexFloat32.Native.arg z, 0⟩

def to32 (z : ComplexFloat) : ComplexFloat32 := ⟨z.re.toFloat32, z.im.toFloat32⟩

def stat64 (f : RefFn) (zs : Array ComplexFloat) : Stat := Id.run do
  let mut s : Stat := {}
  for z in zs do
    let r := Native.ref f z
    if !(r.hiRe.isFinite && r.hiIm.isFinite) then continue
    let e (v : ComplexFloat) := errs v.re v.im r.hiRe r.hiIm r.loRe r.loIm ulp64 eps64 tiny64
    let l := leanFn64 f z; let c := cFn64 f z
    s := s.add (e l) (e c) s!"{z.re} {z.im} -> lean {l} c {c} ref {r.hiRe} {r.hiIm}"
  return s

def stat32 (f : RefFn) (zs : Array ComplexFloat32) : Stat := Id.run do
  let mut s : Stat := {}
  for z in zs do
    let r := ComplexFloat32.Native.ref f z
    if !(r.re.toFloat32.isFinite && r.im.toFloat32.isFinite) then continue
    let e (v : ComplexFloat32) := errs v.re.toFloat v.im.toFloat r.re r.im 0 0 ulp32 eps32 tiny32
    let l := leanFn32 f z; let c := cFn32 f z
    s := s.add (e l) (e c) s!"{z.re} {z.im} -> lean {l} c {c} ref {r.re} {r.im}"
  return s

/-- The exact product or quotient of `z` and `w` as `hi + lo`, when it exists. -/
def exactBin (div : Bool) (z w : ComplexFloat) : Option (Float × Float × Float × Float) := do
  let a ← z.re.toRat?; let b ← z.im.toRat?; let c ← w.re.toRat?; let d ← w.im.toRat?
  let (x, y) ← if div then
      let n := c * c + d * d
      if n == 0 then none else some ((a * c + b * d) / n, (b * c - a * d) / n)
    else some (a * c - b * d, a * d + b * c)
  let hx := x.toFloat; let hy := y.toFloat
  if !(hx.isFinite && hy.isFinite) then none
  let lx := (x - (hx.toRat?.getD 0)).toFloat; let ly := (y - (hy.toRat?.getD 0)).toFloat
  pure (hx, hy, lx, ly)

def statBin64 (div : Bool) (zs : Array ComplexFloat) : Stat := Id.run do
  let mut s : Stat := {}
  for i in [0:zs.size - 1] do
    let z := zs[i]!; let w := zs[i+1]!
    match exactBin div z w with
    | none => pure ()
    | some (hr, hi, lr, li) =>
      let e (v : ComplexFloat) := errs v.re v.im hr hi lr li ulp64 eps64 tiny64
      let l := if div then z / w else z * w
      let c := if div then Native.div z w else Native.mul z w
      s := s.add (e l) (e c)
  return s

def statBin32 (div : Bool) (zs : Array ComplexFloat32) : Stat := Id.run do
  let mut s : Stat := {}
  for i in [0:zs.size - 1] do
    let z := zs[i]!; let w := zs[i+1]!
    let up (v : ComplexFloat32) : ComplexFloat := ⟨v.re.toFloat, v.im.toFloat⟩
    match exactBin div (up z) (up w) with
    | none => pure ()
    | some (hr, hi, lr, li) =>
      if !(hr.toFloat32.isFinite && hi.toFloat32.isFinite) then continue
      let e (v : ComplexFloat32) := errs v.re.toFloat v.im.toFloat hr hi lr li ulp32 eps32 tiny32
      let l := if div then z / w else z * w
      let c := if div then ComplexFloat32.Native.div z w else ComplexFloat32.Native.mul z w
      s := s.add (e l) (e c)
        s!"{z.re} {z.im} / {w.re} {w.im} -> lean {l} c {c} ref {hr} {hi} lo {lr} {li} err {e l}"
  return s

def header : String :=
  "| function | exponents | Lean comp | C comp | Lean norm | C norm | C worse | Lean worse " ++
  "| n |\n" ++
  "|---|---|---|---|---|---|---|---|---|"

def main (args : List String) : IO Unit := do
  if args.head? == some "worst32" then
    let zs := (randomInputs 200000 (-149) 128 0x2545F4914F6CDD1D).map to32
    IO.println s!"32 mul: {(statBin32 false zs).worst}"
    IO.println s!"32 div: {(statBin32 true zs).worst}"
    return
  if args.head? == some "worst" then
    for (lo, hi) in [((-4 : Int), (4 : Int)), (-60, 60)] do
      let zs := randomInputs 20000 lo hi (0x9E3779B97F4A7C15 + lo.toNat.toUInt64)
      for f in RefFn.all do IO.println s!"{f.name}: {(stat64 f zs).worst}"
    for (lo, hi) in [((-149 : Int), (128 : Int))] do
      let zs := (randomInputs 200000 lo hi (0x2545F4914F6CDD1D + lo.toNat.toUInt64)).map to32
      for f in RefFn.all do IO.println s!"32 {f.name}: {(stat32 f zs).worst}"
      IO.println s!"32 mul: {(statBin32 false zs).worst}"
      IO.println s!"32 div: {(statBin32 true zs).worst}"
    return
  let n := (args.head? >>= String.toNat?).getD 20000
  let ranges64 : List (String × Int × Int) :=
    [("[-4, 4)", -4, 4), ("[-60, 60)", -60, 60), ("[-1074, 1024)", -1074, 1024),
      ("near 1, I, unit circle", 0, 0)]
  let ranges32 : List (String × Int × Int) :=
    [("[-4, 4)", -4, 4), ("[-30, 30)", -30, 30), ("[-149, 128)", -149, 128),
      ("near 1, I, unit circle", 0, 0)]
  IO.println "## ComplexFloat (reference: long double, exact for * and /)\n"
  IO.println header
  for (rname, lo, hi) in ranges64 do
    let zs := if lo == 0 then hardInputs n 0x51ED2701 else
      randomInputs n lo hi (0x9E3779B97F4A7C15 + lo.toNat.toUInt64)
    IO.println ((statBin64 false zs).row "mul" rname)
    IO.println ((statBin64 true zs).row "div" rname)
    for f in RefFn.all do
      IO.println ((stat64 f zs).row f.name rname)
  IO.println "\n## ComplexFloat32 (reference: double, exact for * and /)\n"
  IO.println header
  for (rname, lo, hi) in ranges32 do
    let zs := if lo == 0 then (hardInputs n 0x51ED2702).map to32 else
      (randomInputs n lo hi (0x2545F4914F6CDD1D + lo.toNat.toUInt64)).map to32
    IO.println ((statBin32 false zs).row "mul" rname)
    IO.println ((statBin32 true zs).row "div" rname)
    for f in RefFn.all do
      IO.println ((stat32 f zs).row f.name rname)
