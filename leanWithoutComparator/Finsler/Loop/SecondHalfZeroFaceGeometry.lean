module

public import Finsler.Loop.SecondHalfNativeFaceCapDomain
public import Finsler.Topology.JoinedEndpointMaps

/-! At trim parameter zero the actual second time face is the full
native second-half cylinder. Identify its cut domain and bounded
retained target by actual maps, before transferring the closed lifts. -/

@[expose] public section
namespace Finsler.SecondHalfZeroFaceGeometry

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

theorem trim_zero (t : ClosedInterval) : InteriorTimeSlide.trimTime 0 (by norm_num) (by norm_num) t = t := by
  apply Subtype.ext
  change 0 + (1 - 2 * 0) * (t : ℝ) = (t : ℝ)
  ring

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n))

theorem face_family : planeFace (TopCat.of X) 1 ≫
    JoinedFamilyNaturality.globalMap u 0 (by norm_num) (by norm_num) 2 = JoinedHalfCollars.secondFamily u := by
  rw [JoinedEndpointMaps.second_end]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change JoinedHalfCollars.secondFamily u (InteriorTimeSlide.trimTime 0 _ _ z.1, z.2) = _
  rw [trim_zero]

def nativeDomain (r : ℝ) : Set (ClosedInterval × X) := JoinedHalfCollars.secondFamily u ⁻¹' neighborhood n r

def nativeCut (r : ℝ) : TopCat.of (nativeDomain u r) ⟶ TopCat.of (neighborhood n r) :=
  TopCat.ofHom ⟨fun z => ⟨JoinedHalfCollars.secondFamily u z.val, z.property⟩,
    ((JoinedHalfCollars.secondFamily u).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem domain_eq (r : ℝ) : (planeFace (TopCat.of X) 1) ⁻¹'
    domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2 = nativeDomain u r := by
  ext z
  change (planeFace (TopCat.of X) 1 z ∈ tube X ∧
    distanceValue (tube X) (family u 0 (by norm_num) (by norm_num)) 2 (planeFace (TopCat.of X) 1 z) < r) ↔ _
  rw [← JoinedFamilyNaturality.distance_global]
  have he := ConcreteCategory.congr_hom (face_family u) z
  change JoinedFamilyNaturality.globalMap u 0 (by norm_num) (by norm_num) 2 (planeFace (TopCat.of X) 1 z) =
    JoinedHalfCollars.secondFamily u z at he
  rw [he]
  exact and_iff_right (Set.mem_univ _)

def toNative (r : ℝ) :
    TopCat.of ((planeFace (TopCat.of X) 1) ⁻¹'
      domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2) ⟶
        TopCat.of (nativeDomain u r) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, (Set.ext_iff.mp (domain_eq u r) z.val).mp z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem cut_native (r : ℝ) :
    DoubleCapEmbeddingPullback.domainMap (planeFace (TopCat.of X) 1)
      (domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2) ≫
        toCut (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2 =
      toNative u r ≫ nativeCut u r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change JoinedFamilyNaturality.globalMap u 0 (by norm_num) (by norm_num) 2 (planeFace (TopCat.of X) 1 z.val) =
    JoinedHalfCollars.secondFamily u z.val
  exact ConcreteCategory.congr_hom (face_family u) z.val

def nativeRetained {r : ℝ} (hr : r ≤ 1) : TopCat.of (nativeDomain u r) ⟶ TopCat.of (SphereLoop n) :=
  nativeCut u r ≫ TopCat.ofHom (retained n hr)

def nativeBounded {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) : Set (nativeDomain u r) :=
  nativeRetained u hr ⁻¹' {γ | SobolevLength.length F γ < B}

theorem retained_native {r : ℝ} (hr : r ≤ 1) :
    DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
      (domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
      (retainedMap (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) (fun _ => hr) 2) =
        toNative u r ≫ nativeRetained u hr := by
  unfold DoubleCapEmbeddingPullback.retained retainedMap nativeRetained
  rw [← Category.assoc, cut_native, Category.assoc]

def boundedToNative {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain
      (TopCat.of (ClosedInterval × X)) (TopCat.of (SphereLoop n))
      ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
      (DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
        (domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
        (retainedMap (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) (fun _ => hr) 2))
      {γ | SobolevLength.length F γ < B}) ⟶ TopCat.of (nativeBounded u hr F B) := by
  refine TopCat.ofHom ⟨fun z => ⟨toNative u r z.val, ?_⟩, ?_⟩
  · have he := ConcreteCategory.congr_hom (retained_native u hr) z.val
    change _ = nativeRetained u hr (toNative u r z.val) at he
    change SobolevLength.length F (nativeRetained u hr (toNative u r z.val)) < B
    rw [← he]
    exact z.property
  · exact ((toNative u r).hom.continuous.comp continuous_subtype_val).subtype_mk _

theorem bounded_cut {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    boundedToNative u hr F B ≫ SupportedCap.subspaceMap (TopCat.of (nativeDomain u r)) (nativeBounded u hr F B) ≫
      nativeCut u r =
    SupportedCap.subspaceMap
      (TopCat.of ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2))
      (PartialDoubleCapDomainFiltered.boundedDomain (TopCat.of (ClosedInterval × X)) (TopCat.of (SphereLoop n))
        ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
        (DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
          (domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
          (retainedMap (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) (fun _ => hr) 2))
        {γ | SobolevLength.length F γ < B}) ≫
      DoubleCapEmbeddingPullback.domainMap (planeFace (TopCat.of X) 1)
        (domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2) ≫
          toCut (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2 := by
  rw [cut_native]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

end
end Finsler.SecondHalfZeroFaceGeometry
