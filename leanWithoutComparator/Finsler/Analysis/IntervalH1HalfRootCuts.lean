module

public import Finsler.Analysis.IntervalH1HalfRootEquivalence

/-! Actual sqrt-energy cuts of the half-period rotation fixed subset.
Doubling and its certified weak root give a strong-H¹ homeomorphism between
the cut at b and the actual fixed cut at 2b, natural in every cut inclusion.
This is a statement about the original loops and energy, not a Borel model. -/

@[expose] public section

namespace Finsler.SobolevHalfRoot

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevIteration Finsler.SobolevReflectionAction Finsler.Geometry Set
open scoped Topology

noncomputable section

def halfFixedCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) : Set (HalfFixed n) :=
  {u | u.val ∈ energyCut F b}

theorem mem_halfFixedCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (u : HalfFixed n) :
    u ∈ halfFixedCut F b ↔ Real.sqrt (energy F u.val) < b := Iff.rfl

theorem doubleSphere_mem_halfFixedCut_iff {n : ℕ} (F : ReversibleMetric n)
    (b : ℝ) (u : SphereLoop n) :
    doubleSphere u ∈ halfFixedCut F (2 * b) ↔ u ∈ energyCut F b := by
  rw [mem_halfFixedCut, doubleSphere_val, sqrt_energy_iterateSphere, mem_energyCut]
  norm_num only [Nat.cast_ofNat]
  exact mul_lt_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)

theorem rootSphere_mem_energyCut_iff {n : ℕ} (F : ReversibleMetric n)
    (b : ℝ) (u : HalfFixed n) :
    rootSphere u ∈ energyCut F b ↔ u ∈ halfFixedCut F (2 * b) := by
  rw [mem_energyCut, sqrt_energy_rootSphere, mem_halfFixedCut]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm b 2]

def doubleCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    energyCut F b → halfFixedCut F (2 * b) :=
  fun u => ⟨doubleSphere u.val, (doubleSphere_mem_halfFixedCut_iff F b u.val).mpr u.property⟩

def rootCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    halfFixedCut F (2 * b) → energyCut F b :=
  fun u => ⟨rootSphere u.val, (rootSphere_mem_energyCut_iff F b u.val).mpr u.property⟩

theorem doubleCut_val {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (u : energyCut F b) :
    (doubleCut F b u : HalfFixed n) = doubleSphere u.val := rfl

theorem rootCut_val {n : ℕ} (F : ReversibleMetric n) (b : ℝ)
    (u : halfFixedCut F (2 * b)) :
    (rootCut F b u : SphereLoop n) = rootSphere u.val := rfl

theorem root_doubleCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (u : energyCut F b) :
    rootCut F b (doubleCut F b u) = u := Subtype.ext (root_doubleSphere u.val)

theorem double_rootCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ)
    (u : halfFixedCut F (2 * b)) :
    doubleCut F b (rootCut F b u) = u := Subtype.ext (double_rootSphere u.val)

theorem doubleCut_continuous {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    Continuous (doubleCut F b) :=
  ((doubleSphere_continuous n).comp continuous_subtype_val).subtype_mk _

theorem rootCut_continuous {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    Continuous (rootCut F b) :=
  ((rootSphere_continuous n).comp continuous_subtype_val).subtype_mk _

def halfFixedCutHomeomorph {n : ℕ} (F : ReversibleMetric n) (b : ℝ) :
    energyCut F b ≃ₜ halfFixedCut F (2 * b) where
  toFun := doubleCut F b
  invFun := rootCut F b
  left_inv := root_doubleCut F b
  right_inv := double_rootCut F b
  continuous_toFun := doubleCut_continuous F b
  continuous_invFun := rootCut_continuous F b

theorem halfFixedCutHomeomorph_apply {n : ℕ} (F : ReversibleMetric n) (b : ℝ)
    (u : energyCut F b) : halfFixedCutHomeomorph F b u = doubleCut F b u := rfl

theorem halfFixedCutHomeomorph_symm_apply {n : ℕ} (F : ReversibleMetric n) (b : ℝ)
    (u : halfFixedCut F (2 * b)) :
    (halfFixedCutHomeomorph F b).symm u = rootCut F b u := rfl

theorem halfFixedCut_mono {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    halfFixedCut F a ⊆ halfFixedCut F b := fun _ hu => energyCut_mono F hab hu

def halfFixedCutInclusion {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    halfFixedCut F a → halfFixedCut F b :=
  fun u => ⟨u.val, halfFixedCut_mono F hab u.property⟩

theorem halfFixedCutInclusion_val {n : ℕ} (F : ReversibleMetric n) {a b : ℝ}
    (hab : a ≤ b) (u : halfFixedCut F a) :
    (halfFixedCutInclusion F hab u : HalfFixed n) = u.val := rfl

theorem halfFixedCutInclusion_continuous {n : ℕ} (F : ReversibleMetric n) {a b : ℝ}
    (hab : a ≤ b) : Continuous (halfFixedCutInclusion F hab) :=
  continuous_subtype_val.subtype_mk _

theorem doubleCut_natural {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
    (u : energyCut F a) :
    halfFixedCutInclusion F (mul_le_mul_of_nonneg_left hab (by norm_num : (0 : ℝ) ≤ 2))
      (doubleCut F a u) = doubleCut F b (cutInclusion F hab u) := Subtype.ext rfl

theorem rootCut_natural {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
    (u : halfFixedCut F (2 * a)) :
    cutInclusion F hab (rootCut F a u) = rootCut F b
      (halfFixedCutInclusion F
        (mul_le_mul_of_nonneg_left hab (by norm_num : (0 : ℝ) ≤ 2)) u) := Subtype.ext rfl

theorem halfFixedCutHomeomorph_natural {n : ℕ} (F : ReversibleMetric n)
    {a b : ℝ} (hab : a ≤ b) (u : energyCut F a) :
    halfFixedCutInclusion F (mul_le_mul_of_nonneg_left hab (by norm_num : (0 : ℝ) ≤ 2))
      (halfFixedCutHomeomorph F a u) =
        halfFixedCutHomeomorph F b (cutInclusion F hab u) := doubleCut_natural F hab u

end

end Finsler.SobolevHalfRoot
