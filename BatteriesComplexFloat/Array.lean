/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.Basic

/-!
# Arrays of complex floats

`ComplexFloatArray` stores complex numbers unboxed, with real and imaginary parts interleaved in
a `FloatArray`: the number at index `i` has its real part at `2 * i` and its imaginary part at
`2 * i + 1`. This is the layout of C's `double complex` arrays, and of the arrays that FFT and
BLAS libraries take.
-/

/-- An array of complex floats, stored unboxed as interleaved real and imaginary parts. -/
public structure ComplexFloatArray where
  /-- The parts, interleaved: real part at even indices, imaginary part at odd indices. A
  trailing unpaired float, if any, is not part of the array. -/
  data : FloatArray
deriving Inhabited

namespace ComplexFloatArray

/-- The empty array, with room for `c` complex numbers. -/
@[inline] public def emptyWithCapacity (c : Nat) : ComplexFloatArray :=
  ⟨.emptyWithCapacity (2 * c)⟩

/-- The empty array. -/
@[inline] public def empty : ComplexFloatArray := emptyWithCapacity 0

public instance : EmptyCollection ComplexFloatArray := ⟨empty⟩

/-- The number of complex numbers in the array. -/
@[inline] public def size (a : ComplexFloatArray) : Nat := a.data.size / 2

/-- Whether the array is empty. -/
@[inline] public def isEmpty (a : ComplexFloatArray) : Bool := a.size == 0

/-- Adds `z` at the end of the array, in place of an unpaired trailing float if there is one. -/
@[inline] public def push (a : ComplexFloatArray) (z : ComplexFloat) : ComplexFloatArray :=
  ⟨if a.data.size % 2 = 0 then (a.data.push z.re).push z.im
    else ((a.data.set! (a.data.size - 1) z.re).push z.im)⟩

/-- The complex number at index `i`. -/
@[inline] public def get (a : ComplexFloatArray) (i : Nat)
    (h : i < a.size := by get_elem_tactic) : ComplexFloat :=
  have : i < a.data.size / 2 := h
  ⟨a.data[2 * i], a.data[2 * i + 1]⟩

/-- The complex number at index `i`, or `none` if `i` is out of bounds. -/
@[inline] public def get? (a : ComplexFloatArray) (i : Nat) : Option ComplexFloat :=
  if h : i < a.size then some (a.get i h) else none

/-- The complex number at index `i`, or `d` if `i` is out of bounds. -/
@[inline] public def getD (a : ComplexFloatArray) (i : Nat) (d : ComplexFloat) : ComplexFloat :=
  if h : i < a.size then a.get i h else d

/-- The complex number at index `i`. Panics if `i` is out of bounds. -/
@[inline] public def get! (a : ComplexFloatArray) (i : Nat) : ComplexFloat :=
  if h : i < a.size then a.get i h else panic! "index out of bounds"

public instance : GetElem ComplexFloatArray Nat ComplexFloat fun a i => i < a.size where
  getElem a i h := a.get i h

public instance : GetElem? ComplexFloatArray Nat ComplexFloat fun a i => i < a.size where
  getElem? a i := a.get? i
  getElem! a i := a.get! i

/-- Replaces the complex number at index `i` with `z`. -/
@[inline] public def set (a : ComplexFloatArray) (i : Nat) (z : ComplexFloat)
    (_ : i < a.size := by get_elem_tactic) : ComplexFloatArray :=
  ⟨(a.data.set! (2 * i) z.re).set! (2 * i + 1) z.im⟩

/-- Replaces the complex number at index `i` with `z`, or does nothing if `i` is out of
bounds. -/
@[inline] public def setD (a : ComplexFloatArray) (i : Nat) (z : ComplexFloat) :
    ComplexFloatArray :=
  if h : i < a.size then a.set i z h else a

/-- Replaces the complex number at index `i` with `z`. Panics if `i` is out of bounds. -/
@[inline] public def set! (a : ComplexFloatArray) (i : Nat) (z : ComplexFloat) :
    ComplexFloatArray :=
  if h : i < a.size then a.set i z h else panic! "index out of bounds"

/-- Folds `f` over the complex numbers of the array, from the first to the last. -/
@[inline] public def foldl {β : Type u} (f : β → ComplexFloat → β) (init : β)
    (a : ComplexFloatArray) : β :=
  loop 0 init
where
  /-- `loop i b` folds over the numbers from index `i` on, starting from `b`. -/
  loop (i : Nat) (b : β) : β :=
    if h : i < a.size then loop (i + 1) (f b (a.get i h)) else b
  termination_by a.size - i

/-- Runs `f` on the complex numbers of the array in order, as a `for` loop does. -/
@[inline] public protected def forIn {β : Type v} {m : Type v → Type w} [Monad m]
    (a : ComplexFloatArray) (b : β) (f : ComplexFloat → β → m (ForInStep β)) : m β :=
  loop 0 b
where
  /-- `loop i b` runs the loop from index `i` on, starting from `b`. -/
  loop (i : Nat) (b : β) : m β := do
    if h : i < a.size then
      match ← f (a.get i h) b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else pure b
  termination_by a.size - i

public instance [Monad m] : ForIn m ComplexFloatArray ComplexFloat where
  forIn a b f := a.forIn b f

/-- The array with `f` applied to each complex number. -/
@[inline] public def map (f : ComplexFloat → ComplexFloat) (a : ComplexFloatArray) :
    ComplexFloatArray :=
  a.foldl (fun r z => r.push (f z)) (emptyWithCapacity a.size)

/-- The complex numbers of `a`, in order. -/
public def toArray (a : ComplexFloatArray) : Array ComplexFloat :=
  a.foldl (·.push ·) (.emptyWithCapacity a.size)

/-- The complex numbers of `a`, in order. -/
public def toList (a : ComplexFloatArray) : List ComplexFloat := a.toArray.toList

end ComplexFloatArray

/-- The array of the complex numbers of `zs`, in order. -/
public def Array.toComplexFloatArray (zs : Array ComplexFloat) : ComplexFloatArray :=
  zs.foldl (·.push ·) (.emptyWithCapacity zs.size)

/-- The array of the complex numbers of `zs`, in order. -/
public def List.toComplexFloatArray (zs : List ComplexFloat) : ComplexFloatArray :=
  zs.foldl (·.push ·) (.emptyWithCapacity zs.length)

public instance : ToString ComplexFloatArray := ⟨fun a => toString a.toList⟩

public instance : Repr ComplexFloatArray where
  reprPrec a _ := "#c" ++ repr a.toList
