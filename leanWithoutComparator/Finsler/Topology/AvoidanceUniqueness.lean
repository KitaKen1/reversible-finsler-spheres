module

public import Finsler.Topology.FarDiagonalCohomology
public import Finsler.Topology.CohomologyClopen

/-! Uniqueness of the actual Thom lift relative to far union diagonal.
This is stronger than uniqueness in the far-relative group: it yields
comparison primitives vanishing at the actual self-cut time endpoints. -/

@[expose] public section
namespace Finsler.AvoidanceUniqueness

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalCohomology Finsler.DiagonalAvoidanceCocycle Finsler.FarDiagonalCohomology
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

local instance (n : ℕ) : T2Space (product n) :=
  inferInstanceAs (T2Space (Sphere n × Sphere n))

theorem diagonal_cohomology_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : cohomologyZMod2 (TopCat.of (diagonal n)) k) : a = 0 := by
  let f : TopCat.of (diagonal n) ⟶ sphere n :=
    TopCat.ofHom ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩
  let g : sphere n ⟶ TopCat.of (diagonal n) :=
    TopCat.ofHom ⟨fun z => ⟨(z, z), rfl⟩, (continuous_id.prodMk continuous_id).subtype_mk _⟩
  have hid : f ≫ g = 𝟙 (TopCat.of (diagonal n)) := by
    ext z : 1
    apply Subtype.ext
    exact Prod.ext rfl z.property
  have hz : (cohPullback g k).hom a = 0 := SphereTopClass.cohomology_eq_zero_of_ne n k hk hkn _
  have he := congrArg (cohPullback f k).hom hz
  rw [← Cup.pullback_comp, hid, DiagonalCohomology.pullback_id, map_zero] at he
  exact he

theorem avoidance_cohomology_zero (n k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hk : 1 ≤ k) (hkn : k ≠ n) (a : cohomologyZMod2 (TopCat.of (avoid n ρ)) k) : a = 0 := by
  apply CohomologyClopen.union_eq_zero (parts n ρ) (parts_compact n ρ) (parts_disjoint n hρ) k
  intro i
  cases i
  · exact far_cohomology_zero n k hρ hρ2 hk hkn _
  · exact diagonal_cohomology_zero n k hk hkn _

theorem relative_image_injective (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    Function.Injective ((avoidancePair n ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom := by
  have hzero (a : (avoidancePair n ρ).snd.singularCohomology coeff (ZMod 2) coeff (n - 1)) : a = 0 := by
    let e := cohomologyEquiv (avoidancePair n ρ).snd (n - 1)
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e 0 := congrArg e (avoidance_cohomology_zero n (n - 1) hρ hρ2 (by omega) (by omega) _)
      _ = 0 := map_zero _
  have he := (avoidancePair n ρ).singularCohomology_exact_relative coeff (ZMod 2) coeff
    (n - 1) n (by omega)
  intro a b hab
  have hz : ((avoidancePair n ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp he (a - b) hz
  rw [hzero c, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

theorem relativeToPool_injective (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    Function.Injective (relativeToPool (avoidancePair n ρ) n).hom := by
  intro a b hab
  apply relative_image_injective n hn hρ hρ2
  exact (cohomologyEquiv (product n) n).symm.injective hab

end
end Finsler.AvoidanceUniqueness
