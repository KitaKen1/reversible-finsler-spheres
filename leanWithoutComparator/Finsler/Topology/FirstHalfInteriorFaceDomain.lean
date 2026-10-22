module

public import Finsler.Topology.DoubleCapEmbeddingPullback
public import Finsler.Topology.FirstHalfInteriorNative
public import Finsler.Topology.JoinedEndpointMaps

/-! The genuine last face of the first trimming square retains its own
time coordinate. Its cut-domain pullback is the actual interior first
cut domain, and the retained map is literally the original native one. -/

@[expose] public section
namespace Finsler.FirstHalfInteriorFaceDomain

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

def projection (X : TopCat.{0}) : TopCat.of (Outer X) ⟶ TopCat.of (ClosedInterval × X) :=
  TopCat.ofHom ⟨fun z => (z.1.2, z.2), (continuous_snd.comp continuous_fst).prodMk continuous_snd⟩

theorem face_projection (X : TopCat.{0}) :
    planeFace X 1 ≫ projection X = 𝟙 (TopCat.of (ClosedInterval × X)) := by
  ext z : 1
  rfl

theorem push_face_mono (X : TopCat.{0}) (q : ℕ) : Mono ((push (planeFace X 1)).f q) := by
  have hid : push (𝟙 (TopCat.of (ClosedInterval × X))) =
      𝟙 (chains (TopCat.of (ClosedInterval × X))) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (TopCat.of (ClosedInterval × X)))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  apply mono_of_mono_fac (h := 𝟙 ((chains (TopCat.of (ClosedInterval × X))).X q))
  have he := congrArg (fun g => g.f q) (push_comp (planeFace X 1) (projection X)).symm
  simpa only [face_projection, hid, HomologicalComplex.comp_f, HomologicalComplex.id_f] using he

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

theorem domain_eq (r : ℝ) :
    (planeFace (TopCat.of X) 1) ⁻¹'
      domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1 =
        FirstHalfInteriorFamily.domain u a ha ha1 r := by
  rw [FirstHalfInteriorPrism.domain_eq_trimmed]
  ext z
  change (planeFace (TopCat.of X) 1 z ∈ tube X ∧
    distanceValue (tube X) (family u a ha.le ha1.le) 1 (planeFace (TopCat.of X) 1 z) < r) ↔ _
  rw [← JoinedFamilyNaturality.distance_global]
  have he := ConcreteCategory.congr_hom (JoinedEndpointMaps.first_end u a ha.le ha1.le) z
  change JoinedFamilyNaturality.globalMap u a ha.le ha1.le 1 (planeFace (TopCat.of X) 1 z) =
    CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le z at he
  rw [he]
  exact and_iff_right (Set.mem_univ _)

def toInterior (r : ℝ) :
    TopCat.of ((planeFace (TopCat.of X) 1) ⁻¹'
      domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) ⟶
        TopCat.of (FirstHalfInteriorFamily.domain u a ha ha1 r) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, (Set.ext_iff.mp (domain_eq u a ha ha1 r) z.val).mp z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem toCut_native (r : ℝ) :
    DoubleCapEmbeddingPullback.domainMap (planeFace (TopCat.of X) 1)
      (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) ≫
        toCut (tube X) (family u a ha.le ha1.le) (fun _ => r) 1 =
      toInterior u a ha ha1 r ≫ FirstHalfInteriorNative.toCut u a ha ha1 r := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  change JoinedFamilyNaturality.globalMap u a ha.le ha1.le 1 (planeFace (TopCat.of X) 1 z.val) =
    CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le z.val
  exact ConcreteCategory.congr_hom (JoinedEndpointMaps.first_end u a ha.le ha1.le) z.val

theorem retained_native {r : ℝ} (hr : r ≤ 1) :
    DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
      (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
      (retainedMap (tube X) (family u a ha.le ha1.le) (fun _ => r) (fun _ => hr) 1) =
        toInterior u a ha ha1 r ≫ FirstHalfInteriorNative.originalRetainedMap u a ha ha1 hr := by
  unfold DoubleCapEmbeddingPullback.retained retainedMap
  rw [← Category.assoc, toCut_native, Category.assoc, FirstHalfInteriorNative.retained_native]

def boundedToInterior {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain
      (TopCat.of (ClosedInterval × X)) (TopCat.of (SphereLoop n))
      ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
      (DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
        (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
        (retainedMap (tube X) (family u a ha.le ha1.le) (fun _ => r) (fun _ => hr) 1))
      (JoinedFilteredCap.sublevel F A)) ⟶
        TopCat.of (FirstHalfInteriorFamily.filteredDomain u a ha ha1 hr F A) := by
  refine TopCat.ofHom ⟨fun z => ⟨toInterior u a ha ha1 r z.val, ?_⟩, ?_⟩
  · have he := ConcreteCategory.congr_hom (retained_native u a ha ha1 hr) z.val
    change _ = FirstHalfInteriorNative.originalRetainedMap u a ha ha1 hr
      (toInterior u a ha ha1 r z.val) at he
    change length F (FirstHalfInteriorNative.originalRetainedMap u a ha ha1 hr
      (toInterior u a ha ha1 r z.val)) < A
    rw [← he]
    exact z.property
  · exact ((toInterior u a ha ha1 r).hom.continuous.comp continuous_subtype_val).subtype_mk _

end
end Finsler.FirstHalfInteriorFaceDomain
