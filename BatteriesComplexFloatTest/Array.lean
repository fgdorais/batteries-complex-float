import BatteriesComplexFloat

/-! # Tests for `ComplexFloatArray` -/

def zs : Array ComplexFloat := #[⟨1, 2⟩, ⟨-0.0, 3⟩, ⟨Float.inf, Float.nan⟩]

def a : ComplexFloatArray := zs.toComplexFloatArray

#guard a.size == 3
#guard a.data.size == 6
#guard a.data.toList.take 4 == [1, 2, -0.0, 3]
#guard a[0] == ⟨1, 2⟩
#guard a[1]!.re.signBit
#guard a[2]?.map (·.isInf) == some true
#guard a[3]?.isNone
#guard (a.getD 5 7).re == 7
#guard ComplexFloatArray.empty.isEmpty
#guard (a.set 1 ⟨5, 6⟩)[1]! == ⟨5, 6⟩
#guard (a.set 1 ⟨5, 6⟩)[0]! == ⟨1, 2⟩
#guard (a.setD 9 ⟨5, 6⟩).size == 3
#guard (a.push ⟨7, 8⟩).size == 4
#guard (a.push ⟨7, 8⟩)[3]! == ⟨7, 8⟩
#guard (a.map (· * ⟨0, 1⟩))[0]! == ⟨-2, 1⟩
#guard a.foldl (fun n _ => n + 1) 0 == 3
#guard (Id.run do
  let mut s : ComplexFloat := 0
  for z in a do
    if z.isInf then break
    s := s + z
  return s) == ⟨1, 5⟩
#guard a.toList.length == 3
#guard [⟨1, 2⟩, ⟨3, 4⟩].toComplexFloatArray.toArray.size == 2
-- An unpaired trailing float is replaced by the next push.
#guard (ComplexFloatArray.mk ((FloatArray.empty.push 1).push 2 |>.push 9)).size == 1
#guard
  ((ComplexFloatArray.mk ((FloatArray.empty.push 1).push 2 |>.push 9)).push ⟨3, 4⟩).data.size == 4
#guard toString ([⟨1, 2⟩] : List ComplexFloat).toComplexFloatArray == "[1.000000+2.000000i]"
