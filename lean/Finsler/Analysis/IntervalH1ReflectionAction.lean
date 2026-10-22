module

public import Finsler.Analysis.IntervalH1Reverse
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.MulAction

/-! The actual reflection C₂ action on the actual periodic sphere H¹ model.
The group is Multiplicative (ZMod 2); its nonidentity element acts by the
certified weak reflection. Actual sqrt-energy cuts inherit a continuous action
and their monotone inclusions are equivariant. No equivariant cohomology or
Gysin sequence is asserted here. -/

@[expose] public section

namespace Finsler.SobolevReflectionAction

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.Geometry Finsler.SobolevEnergy Set
open scoped Topology

noncomputable section

abbrev ReflectionGroup := Multiplicative (ZMod 2)

def sigma : ReflectionGroup := Multiplicative.ofAdd 1

theorem reflectionGroup_card : Fintype.card ReflectionGroup = 2 := by decide

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  change (x : Fin 2) = (0 : Fin 2) ∨ (x : Fin 2) = (1 : Fin 2)
  have hall : ∀ y : Fin 2, y = 0 ∨ y = 1 := by
    exact (Fin.forall_fin_two (p := fun y : Fin 2 => y = 0 ∨ y = 1)).mpr
      ⟨Or.inl rfl, Or.inr rfl⟩
  exact hall x

theorem sigma_ne_one : sigma ≠ 1 := by decide

theorem sigma_square : sigma * sigma = 1 := by decide

instance (n : ℕ) : MulAction ReflectionGroup (SphereLoop n) where
  smul g u := if g.toAdd = 0 then u else reverseSphere u
  one_smul u := by
    change (if (0 : ZMod 2) = 0 then u else reverseSphere u) = u
    simp
  mul_smul g h u := by
    change (if (g * h).toAdd = 0 then u else reverseSphere u) =
      (if g.toAdd = 0 then (if h.toAdd = 0 then u else reverseSphere u)
        else reverseSphere (if h.toAdd = 0 then u else reverseSphere u))
    rw [toAdd_mul]
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rcases zmod_two_cases g.toAdd with hg | hg <;>
      rcases zmod_two_cases h.toAdd with hh | hh <;>
      simp [hg, hh, h11, reverseSphere_involutive]

theorem smul_formula {n : ℕ} (g : ReflectionGroup) (u : SphereLoop n) :
    g • u = if g.toAdd = 0 then u else reverseSphere u := rfl

theorem sigma_smul {n : ℕ} (u : SphereLoop n) : sigma • u = reverseSphere u := by
  rw [smul_formula]
  change (if (1 : ZMod 2) = 0 then u else reverseSphere u) = _
  simp

theorem smul_isometry (n : ℕ) (g : ReflectionGroup) : Isometry (fun u : SphereLoop n => g • u) := by
  by_cases hg : g.toAdd = 0
  · intro u v
    simp only [smul_formula, hg, ite_true]
  · simpa only [smul_formula, hg, ite_false] using reverseSphere_isometry n

instance (n : ℕ) : ContinuousSMul ReflectionGroup (SphereLoop n) where
  continuous_smul := continuous_prod_of_discrete_left.mpr fun g => (smul_isometry n g).continuous

theorem reflection_action_continuous (n : ℕ) :
    Continuous (fun p : ReflectionGroup × SphereLoop n => p.1 • p.2) := continuous_smul

theorem energy_smul {n : ℕ} (F : ReversibleMetric n) (g : ReflectionGroup) (u : SphereLoop n) :
    energy F (g • u) = energy F u := by
  rw [smul_formula]
  split
  · rfl
  · exact energy_reverseSphere F u

theorem sphereImage_smul {n : ℕ} (g : ReflectionGroup) (u : SphereLoop n) :
    sphereImage (g • u) = sphereImage u := by
  rw [smul_formula]
  split
  · rfl
  · exact sphereImage_reverseSphere u

theorem constant_smul {n : ℕ} (g : ReflectionGroup) (x : Sphere n) :
    g • constantSphereLoop x = constantSphereLoop x := by
  rw [smul_formula]
  split
  · rfl
  · exact reverseSphere_constant x

theorem fixed_iff_reverse_eq {n : ℕ} (u : SphereLoop n) :
    (∀ g : ReflectionGroup, g • u = u) ↔ reverseSphere u = u := by
  constructor
  · intro h
    simpa only [sigma_smul] using h sigma
  · intro h g
    rw [smul_formula]
    split
    · rfl
    · exact h

theorem fixed_iff_representative_symmetric {n : ℕ} (u : SphereLoop n) :
    (∀ g : ReflectionGroup, g • u = u) ↔
      ∀ t : ClosedInterval, sphereRepresentative u (reflectionInterval t) = sphereRepresentative u t := by
  rw [fixed_iff_reverse_eq]
  constructor
  · intro h t
    rw [← sphereRepresentative_reverseSphere, h]
  · intro h
    apply sphereLoop_eq_of_representative_eq
    intro t
    rw [sphereRepresentative_reverseSphere]
    exact h t

def energyCut {n : ℕ} (F : ReversibleMetric n) (a : ℝ) : Set (SphereLoop n) :=
  {u | Real.sqrt (energy F u) < a}

theorem mem_energyCut {n : ℕ} (F : ReversibleMetric n) (a : ℝ) (u : SphereLoop n) :
    u ∈ energyCut F a ↔ Real.sqrt (energy F u) < a := Iff.rfl

theorem smul_mem_energyCut_iff {n : ℕ} (F : ReversibleMetric n) (a : ℝ)
    (g : ReflectionGroup) (u : SphereLoop n) : g • u ∈ energyCut F a ↔ u ∈ energyCut F a := by
  rw [mem_energyCut, mem_energyCut, energy_smul]

theorem energyCut_mono {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    energyCut F a ⊆ energyCut F b := fun _ hu => lt_of_lt_of_le hu hab

theorem constant_mem_energyCut_iff {n : ℕ} (F : ReversibleMetric n) (a : ℝ) (x : Sphere n) :
    constantSphereLoop x ∈ energyCut F a ↔ 0 < a := by
  rw [mem_energyCut, energy_constantSphereLoop, Real.sqrt_zero]

instance {n : ℕ} (F : ReversibleMetric n) (a : ℝ) : MulAction ReflectionGroup (energyCut F a) where
  smul g u := ⟨g • (u : SphereLoop n), (smul_mem_energyCut_iff F a g u).mpr u.property⟩
  one_smul u := Subtype.ext (one_smul ReflectionGroup (u : SphereLoop n))
  mul_smul g h u := Subtype.ext (mul_smul g h (u : SphereLoop n))

theorem energyCut_smul_val {n : ℕ} (F : ReversibleMetric n) (a : ℝ)
    (g : ReflectionGroup) (u : energyCut F a) :
    ((g • u : energyCut F a) : SphereLoop n) = g • (u : SphereLoop n) := rfl

instance {n : ℕ} (F : ReversibleMetric n) (a : ℝ) :
    ContinuousSMul ReflectionGroup (energyCut F a) where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

theorem energyCut_action_continuous {n : ℕ} (F : ReversibleMetric n) (a : ℝ) :
    Continuous (fun p : ReflectionGroup × energyCut F a => p.1 • p.2) := continuous_smul

def cutInclusion {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    energyCut F a → energyCut F b := fun u => ⟨u, energyCut_mono F hab u.property⟩

theorem cutInclusion_val {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
    (u : energyCut F a) : (cutInclusion F hab u : SphereLoop n) = (u : SphereLoop n) := rfl

theorem cutInclusion_continuous {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) :
    Continuous (cutInclusion F hab) := continuous_subtype_val.subtype_mk _

theorem cutInclusion_equivariant {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
    (g : ReflectionGroup) (u : energyCut F a) : cutInclusion F hab (g • u) = g • cutInclusion F hab u :=
  Subtype.ext rfl

end

end Finsler.SobolevReflectionAction
