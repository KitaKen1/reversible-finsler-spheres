module

public import Finsler.Loop.MeridianLoopFamily
public import Finsler.Topology.SphereTopClass

/-! The ACTUAL parameter equator is the unit sphere in the genuine
orthogonal complement of its pole. Compute its real F2 top homology
with pinned Tau Ceti, and construct its nonzero fundamental class.
Nonzero image in loop homology is a SEPARATE calculation. -/

@[expose] public section
namespace Finsler.MeridianEquatorHomology
open CategoryTheory AlgebraicTopology Topology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev orthogonalSpace {n : ℕ} (P : Sphere n) := (ℝ ∙ (P : Ambient n))ᗮ
abbrev orthogonalSphere {n : ℕ} (P : Sphere n) := ↥(Metric.sphere (0 : orthogonalSpace P) 1)

def toOrthogonal {n : ℕ} (P : Sphere n) (v : equator P) : orthogonalSphere P :=
  ⟨⟨(v.val : Ambient n), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr v.property⟩, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact mem_sphere_zero_iff_norm.mp v.val.property⟩

def fromOrthogonal {n : ℕ} (P : Sphere n) (v : orthogonalSphere P) : equator P :=
  ⟨⟨(v.val : Ambient n), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact mem_sphere_zero_iff_norm.mp v.property⟩,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.val.property⟩

def homeomorph {n : ℕ} (P : Sphere n) : equator P ≃ₜ orthogonalSphere P where
  toFun := toOrthogonal P
  invFun := fromOrthogonal P
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    unfold toOrthogonal
    fun_prop
  continuous_invFun := by
    unfold fromOrthogonal
    fun_prop

theorem orthogonal_dimension {n : ℕ} (P : Sphere n) :
    Module.finrank ℝ (orthogonalSpace P) = n :=
  Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere P)

theorem equator_nonempty {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) : Nonempty (equator P) := by
  have hd := orthogonal_dimension P
  have hpos : 0 < Module.finrank ℝ (orthogonalSpace P) := by omega
  let : Nontrivial (orthogonalSpace P) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v⟩ := (NormedSpace.sphere_nonempty (E := orthogonalSpace P) (x := 0)).mpr zero_le_one |>.coe_sort
  exact ⟨fromOrthogonal P v⟩

def homologyIso (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :
    homologyZMod2 (TopCat.of (equator P)) m ≅ ModuleCat.of (ZMod 2) (ZMod 2) := by
  let e : TopCat.of (equator P) ≅ TopCat.of (orthogonalSphere P) := TopCat.isoOfHomeo (homeomorph P)
  have he := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) m).obj coeff).mapIso e
  cases m with
  | zero => omega
  | succ k =>
    exact he ≪≫ ((TauCeti.reducedSingularHomologySuccIso coeff k).app
      (TopCat.of (orthogonalSphere P))).symm ≪≫
      TauCeti.reducedSingularHomologySphereIso coeff (orthogonal_dimension P)

def homologyEquiv (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :
    homologyZMod2 (TopCat.of (equator P)) m ≃ₗ[ZMod 2] ZMod 2 :=
  (homologyIso m hm P).toLinearEquiv

def fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :
    homologyZMod2 (TopCat.of (equator P)) m := (homologyEquiv m hm P).symm 1

theorem fundamental_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) : fundamental m hm P ≠ 0 := by
  intro h
  have he := congrArg (homologyEquiv m hm P) h
  rw [fundamental, LinearEquiv.apply_symm_apply, map_zero] at he
  exact one_ne_zero he

end
end Finsler.MeridianEquatorHomology
