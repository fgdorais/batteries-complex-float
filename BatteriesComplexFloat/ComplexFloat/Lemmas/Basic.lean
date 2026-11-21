/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.ComplexFloat.Basic
public import Batteries.Data.Float.Lemmas.Arithmetic

/-!
# Lemmas about `ComplexFloat` arithmetic
-/

namespace ComplexFloat

public theorem _root_.Float.mulErr_comm (p q : Float) : Float.mulErr p q = Float.mulErr q p := by
  simp only [Float.mulErr]; rw [Float.fma_comm, Float.mul_comm]

@[ext] public theorem ext {z w : ComplexFloat} (hre : z.re = w.re) (him : z.im = w.im) :
    z = w := by
  cases z; cases w; simp_all

@[simp] public theorem re_conj (z : ComplexFloat) : z.conj.re = z.re := rfl
@[simp] public theorem im_conj (z : ComplexFloat) : z.conj.im = -z.im := rfl
@[simp] public theorem re_neg (z : ComplexFloat) : (-z).re = -z.re := rfl
@[simp] public theorem im_neg (z : ComplexFloat) : (-z).im = -z.im := rfl

@[simp] public theorem conj_conj (z : ComplexFloat) : z.conj.conj = z := by
  ext <;> simp

@[simp] public theorem neg_neg (z : ComplexFloat) : - -z = z := by
  ext <;> simp

public theorem conj_neg (z : ComplexFloat) : (-z).conj = -z.conj := by
  ext <;> simp

public theorem mul_comm (z w : ComplexFloat) : z * w = w * z := by
  change ComplexFloat.mul z w = ComplexFloat.mul w z
  simp only [ComplexFloat.mul]
  rw [Float.mul_comm w.re z.re, Float.mul_comm w.im z.im, Float.mul_comm w.re z.im,
    Float.mul_comm w.im z.re, Float.add_comm (z.im * w.re), Float.mulErr_comm w.re z.re,
    Float.mulErr_comm w.im z.im, Float.mulErr_comm w.re z.im, Float.mulErr_comm w.im z.re,
    Float.add_comm (Float.mulErr z.im w.re),
    Float.mul_comm w.recoverInf.re, Float.mul_comm w.recoverInf.im z.recoverInf.im,
    Float.mul_comm w.recoverInf.re z.recoverInf.im, Float.mul_comm w.recoverInf.im z.recoverInf.re,
    Float.add_comm (z.recoverInf.im * w.recoverInf.re), Bool.or_comm w.isInf]
  congr 3
  cases (z.re * w.re).isInf <;> cases (z.im * w.im).isInf <;> cases (z.re * w.im).isInf <;>
    cases (z.im * w.re).isInf <;> rfl

end ComplexFloat
