module

public import Finsler.Geometry.FarDiagonalGeometry
public import Finsler.Topology.DiagonalUniqueness

/-! Identify the actual far-relative diagonal class. Equality of absolute
images is used only after proving injectivity of the actual relative map,
from the far-set retraction and sphere cohomology. -/

@[expose] public section
namespace Finsler.FarDiagonalCohomology

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.DiagonalGeometry Finsler.DiagonalCohomology
open Finsler.CochainComparison Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.DiagonalAvoidanceCocycle
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def farPair (n : ℕ) (ρ : ℝ) : TopPair.{0} := TopPair.ofSubset (far n ρ)

theorem far_cohomology_zero (n k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hk : 1 ≤ k) (hkn : k ≠ n) (a : cohomologyZMod2 (TopCat.of (far n ρ)) k) : a = 0 := by
  let f : TopCat.of (far n ρ) ⟶ sphere n := TopCat.ofHom FarDiagonalGeometry.firstFar
  let g : sphere n ⟶ TopCat.of (far n ρ) := TopCat.ofHom (FarDiagonalGeometry.sectionFar hρ2)
  let H : TopCat.Homotopy (𝟙 (TopCat.of (far n ρ))) (f ≫ g) :=
    FarDiagonalGeometry.retractionHomotopy hρ hρ2
  have he := homotopy_pullback H k a
  have hz : (cohPullback g k).hom a = 0 := cohomology_eq_zero_of_ne n k hk hkn _
  rw [pullback_id, Cup.pullback_comp, hz, map_zero] at he
  exact he

theorem relative_image_injective (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    Function.Injective ((farPair n ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom := by
  have hzero (a : (farPair n ρ).snd.singularCohomology coeff (ZMod 2) coeff (n - 1)) : a = 0 := by
    let e := cohomologyEquiv (farPair n ρ).snd (n - 1)
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e 0 := congrArg e (far_cohomology_zero n (n - 1) hρ hρ2 (by omega) (by omega) _)
      _ = 0 := map_zero _
  have he := (farPair n ρ).singularCohomology_exact_relative coeff (ZMod 2) coeff
    (n - 1) n (by omega)
  intro a b hab
  have hz : ((farPair n ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp he (a - b) hz
  rw [hzero c, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

theorem relativeToPool_injective (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) : Function.Injective (relativeToPool (farPair n ρ) n).hom := by
  intro a b hab
  apply relative_image_injective n hn hρ hρ2
  exact (cohomologyEquiv (product n) n).symm.injective hab

def fromDeleted (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : farPair n ρ ⟶ diagonalPair n :=
  TopPair.ofSubsetMap (B := far n ρ) (B' := deleted n) (𝟙 (product n))
    (far_subset_deleted n hρ)

def fromAvoidance (n : ℕ) (ρ : ℝ) : farPair n ρ ⟶ avoidancePair n ρ :=
  TopPair.ofSubsetMap (B := far n ρ) (B' := avoid n ρ) (𝟙 (product n))
    (fun x hx => mem_iUnion.mpr ⟨false, hx⟩)

theorem fromDeleted_fst (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    TopPair.Hom.fst (fromDeleted n hρ) = 𝟙 (product n) := by
  ext x : 1
  exact TopPair.ofSubsetMap_fst_apply (B := far n ρ) (B' := deleted n) (𝟙 (product n))
    (far_subset_deleted n hρ) x

theorem fromAvoidance_fst (n : ℕ) (ρ : ℝ) :
    TopPair.Hom.fst (fromAvoidance n ρ) = 𝟙 (product n) := by
  ext x : 1
  exact TopPair.ofSubsetMap_fst_apply (B := far n ρ) (B' := avoid n ρ) (𝟙 (product n))
    (fun x hx => mem_iUnion.mpr ⟨false, hx⟩) x

def thomClass (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (farPair n ρ).singularCohomology coeff (ZMod 2) coeff n :=
  (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (fromDeleted n hρ) n).hom (DiagonalCohomology.relativeClass n hn)

def avoidanceClass (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (farPair n ρ).singularCohomology coeff (ZMod 2) coeff n :=
  (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
    (fromAvoidance n ρ) n).hom (DiagonalAvoidanceCocycle.relativeClass n hn hρ)

theorem thomClass_image (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (relativeToPool (farPair n ρ) n).hom (thomClass n hn hρ) = ambientClass n hn := by
  have he := congrArg (fun f => f.hom (DiagonalCohomology.relativeClass n hn))
    (relative_to_absolute_natural (fromDeleted n hρ) n)
  change (relativeToPool (farPair n ρ) n).hom (thomClass n hn hρ) =
    (cohPullback (TopPair.Hom.fst (fromDeleted n hρ)) n).hom
      ((relativeToPool (diagonalPair n) n).hom (DiagonalCohomology.relativeClass n hn)) at he
  calc
    _ = (cohPullback (TopPair.Hom.fst (fromDeleted n hρ)) n).hom (ambientClass n hn) :=
      he.trans (congrArg _ (DiagonalCohomology.relativeClass_pool_image n hn))
    _ = (cohPullback (𝟙 (product n)) n).hom (ambientClass n hn) :=
      congrArg (fun f : product n ⟶ product n => (cohPullback f n).hom (ambientClass n hn))
        (fromDeleted_fst n hρ)
    _ = _ := pullback_id _ _ _

theorem avoidanceClass_image (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (relativeToPool (farPair n ρ) n).hom (avoidanceClass n hn hρ) = ambientClass n hn := by
  have he := congrArg (fun f => f.hom (DiagonalAvoidanceCocycle.relativeClass n hn hρ))
    (relative_to_absolute_natural (fromAvoidance n ρ) n)
  change (relativeToPool (farPair n ρ) n).hom (avoidanceClass n hn hρ) =
    (cohPullback (TopPair.Hom.fst (fromAvoidance n ρ)) n).hom
      ((relativeToPool (avoidancePair n ρ) n).hom
        (DiagonalAvoidanceCocycle.relativeClass n hn hρ)) at he
  calc
    _ = (cohPullback (TopPair.Hom.fst (fromAvoidance n ρ)) n).hom (ambientClass n hn) :=
      he.trans (congrArg _ (DiagonalAvoidanceCocycle.relativeClass_image n hn hρ))
    _ = (cohPullback (𝟙 (product n)) n).hom (ambientClass n hn) :=
      congrArg (fun f : product n ⟶ product n => (cohPullback f n).hom (ambientClass n hn))
        (fromAvoidance_fst n ρ)
    _ = _ := pullback_id _ _ _

theorem thom_comparison (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    avoidanceClass n (by omega) hρ = thomClass n (by omega) hρ := by
  apply relativeToPool_injective n hn hρ hρ2
  exact (avoidanceClass_image n (by omega) hρ).trans (thomClass_image n (by omega) hρ).symm

end
end Finsler.FarDiagonalCohomology
