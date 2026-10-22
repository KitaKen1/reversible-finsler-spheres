module

public import Finsler.Loop.CompactNearJoinParameters
public import Finsler.Topology.OriginalSecondHalfBoundedFactors

/-! Identify the actual native cut domain on time times the compact
near-pair source with the original partial second-half cut domain.
Both directions and source/cut diagrams are actual continuous maps. -/

@[expose] public section
namespace Finsler.CompactSecondHalfCutIso

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R < 1)

def nativeFamily : TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶
    SelfCutThomCocycle.parameters n :=
  JoinedHalfCollars.secondFamily (CompactNearJoinParameters.inputs α β R hR)

def nativeDomain (r : ℝ) : Set (ClosedInterval × CompactNearJoinParameters.tube α β R) :=
  nativeFamily α β R hR ⁻¹' SupportedSelfCut.neighborhood n r

def nativeCut (r : ℝ) : TopCat.of (nativeDomain α β R hR r) ⟶
    TopCat.of (SupportedSelfCut.neighborhood n r) :=
  TopCat.ofHom ⟨fun z => ⟨nativeFamily α β R hR z.val, z.property⟩,
    ((nativeFamily α β R hR).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem toOld_mem (r : ℝ) (z : nativeDomain α β R hR r) :
    (CompactNearJoinParameters.timeMap α β R z.val).val ∈
      OriginalSecondHalfFamily.domain α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r := by
  have hk := (CompactNearJoinParameters.timeMap α β R z.val).property
  refine ⟨hk, ?_⟩
  change TubeTestWitness.partialValue (X := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalSecondHalfCompactTube.tube α β R)
    (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR)) (SupportedSelfCut.distance n)
        (CompactNearJoinParameters.timeMap α β R z.val).val < r
  rw [TubeTestWitness.partialValue, dite_eq_left hk]
  exact z.property

def toOld (r : ℝ) : TopCat.of (nativeDomain α β R hR r) ⟶
    TopCat.of (OriginalSecondHalfFamily.domain α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r) :=
  TopCat.ofHom ⟨fun z => ⟨(CompactNearJoinParameters.timeMap α β R z.val).val, toOld_mem α β R hR r z⟩,
    (continuous_subtype_val.comp
      ((CompactNearJoinParameters.timeMap α β R).hom.continuous.comp continuous_subtype_val)).subtype_mk _⟩

def toNative (r : ℝ) :
    TopCat.of (OriginalSecondHalfFamily.domain α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r) ⟶ TopCat.of (nativeDomain α β R hR r) :=
  TopCat.ofHom ⟨fun z => ⟨CompactNearJoinParameters.timeInv α β R ⟨z.val, z.property.1⟩,
    (OriginalSecondHalfFamily.cutMap α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r z).property⟩,
    (((CompactNearJoinParameters.timeInv α β R).hom.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _⟩

theorem toOld_toNative (r : ℝ) : toOld α β R hR r ≫ toNative α β R hR r = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem toNative_toOld (r : ℝ) : toNative α β R hR r ≫ toOld α β R hR r = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def cutIso (r : ℝ) : TopCat.of (nativeDomain α β R hR r) ≅
    TopCat.of (OriginalSecondHalfFamily.domain α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r) where
  hom := toOld α β R hR r
  inv := toNative α β R hR r
  hom_inv_id := toOld_toNative α β R hR r
  inv_hom_id := toNative_toOld α β R hR r

theorem source_square (r : ℝ) :
    toOld α β R hR r ≫ SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfFamily.domain α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r) =
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (nativeDomain α β R hR r) ≫ CompactNearJoinParameters.timeMap α β R ≫
          SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
            (OriginalSecondHalfCompactTube.tube α β R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem cut_square (r : ℝ) : toOld α β R hR r ≫
    OriginalSecondHalfFamily.cutMap α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r = nativeCut α β R hR r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

end
end Finsler.CompactSecondHalfCutIso
