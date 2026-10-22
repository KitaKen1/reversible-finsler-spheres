module

public import Finsler.Loop.FarSubspaceSmallCap
public import Finsler.Loop.SingleCutCanonicalIncoming
public import Finsler.Loop.SmallSupportedCapRestriction

/-! The actual canonical Thom cap lands directly in the actual tested
oscillation small chains. Its canonical incoming component agrees
literally with the original supported Thom stage on this real cover. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalThomSmallLift

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputSelfCutCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (a R : ℝ) (hrR : r < R)
  (hA : ∀ x, SobolevLength.length F (α x) < a) (hR : R ≤ 1) (ε : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)

def near : Set (ambient α) := {z | SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r}

theorem near_open : IsOpen (near α r) :=
  isOpen_lt ((SupportedSelfCut.continuous_distance (m + 1)).comp
    (continuous_fst.prodMk (α.continuous.comp continuous_snd))) continuous_const

def cover (cutFar : ℝ) := FarSubspaceSmallCap.cover (ambient α) (CompactRotatedCutData.source α r)
  (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)
  (SingleCutCanonicalIncoming.cover_open α r F a R hrR hA hR ε) (far α cutFar) (near α r)

theorem cover_open (i : Option (SupportedSelfCut.neighborhood (m + 1) R)) :
    IsOpen (cover α r F a R hrR hA hR ε ρ i) :=
  FarSubspaceSmallCap.cover_open _ _ _ _ _ _
    (isOpen_lt continuous_const ((SupportedSelfCut.continuous_distance (m + 1)).comp
      (continuous_fst.prodMk (α.continuous.comp continuous_snd)))) (near_open α r) i

theorem cover_univ (hε : 0 < ε) (hρr : ρ < r) :
    ⋃ i, cover α r F a R hrR hA hR ε ρ i = Set.univ := by
  apply FarSubspaceSmallCap.cover_univ _ _ _ _ _ _
    (SingleCutCanonicalIncoming.cover_univ α r F a R hrR hA hR hε)
  · apply Set.eq_univ_of_forall
    intro z
    by_cases hz : SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r
    · exact Or.inr hz
    · exact Or.inl (hρr.trans_le (le_of_not_gt hz))
  · exact fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from hz.le

def operation := FarSubspaceSmallCap.operation (ambient α) (CompactRotatedCutData.source α r)
  (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)
  (SingleCutCanonicalIncoming.cover_open α r F a R hrR hA hR ε) (far α ρ) (near α r)
  (fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from hz.le) (m + 1) (SingleCutCanonicalThomCochains.canonicalThom α h)
  (SingleCutCanonicalThomCochains.canonicalThom_far_zero α h)
  (pullback_closed _ _ _ (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) (h.1.trans h.2.2)))

theorem component_source (q : ℕ) :
    (operation α r F a R hrR hA hR ε h).component q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) ≫ push (source α r)).f q =
    (inclusion (ambient α) (cover α r F a R hrR hA hR ε ρ)).f ((m + 1) + q) ≫
      RelativeCapAssociativity.absoluteChain (ambient α) (m + 1) q ((m + 1) + q) rfl
        (SingleCutCanonicalThomCochains.canonicalThom α h) :=
  FarSubspaceSmallCap.component_source (ambient α) (CompactRotatedCutData.source α r)
    (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)
    (SingleCutCanonicalIncoming.cover_open α r F a R hrR hA hR ε) (far α ρ) (near α r)
    (fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from hz.le)
    (m + 1) (SingleCutCanonicalThomCochains.canonicalThom α h)
    (SingleCutCanonicalThomCochains.canonicalThom_far_zero α h) q

theorem canonical_refines (i : Option (SupportedSelfCut.neighborhood (m + 1) R)) :
    Set.MapsTo (CompactInputShortMaps.cylinder α F a hA)
      (cover α r F a R hrR hA hR ε ρ i)
      (SupportedCap.cover (FilteredPrismSelfCut.domain F a)
        (FilteredPrismSelfCut.far F a ρ) (FilteredPrismSelfCut.near F a R) i.isSome) := by
  cases i with
  | none => exact fun _ hz => hz
  | some i => exact fun _ hz => hz.2.trans hrR

theorem cocycle_pullback : cochainPullback (CompactInputShortMaps.cylinder α F a hA) (m + 1)
    (FilteredPrismSelfCut.cocycle (by omega) F a (h.1.trans h.2.2)) =
      SingleCutCanonicalThomCochains.canonicalThom α h := by
  rw [FilteredPrismSelfCut.cocycle, ← pullback_comp, CompactInputShortMaps.cylinder_source]
  rfl

theorem near_component (hρr : ρ < r) (q : ℕ) :
    (operation α r F a R hrR hA hR ε h).component q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)).f q ≫
      (push (SingleCutCanonicalIncoming.toNear α r F a R hrR hA)).f q =
    (inclusion (ambient α) (cover α r F a R hrR hA hR ε ρ)).f ((m + 1) + q) ≫
      (push (CompactInputShortMaps.cylinder α F a hA)).f ((m + 1) + q) ≫
      (FilteredPrismSelfCut.firstThom (by omega) F a (h.1.trans h.2.2) (hρr.trans hrR)).component q := by
  apply SmallSupportedCapRestriction.component
    (cover α r F a R hrR hA hR ε ρ) (CompactInputShortMaps.cylinder α F a hA)
    (FilteredPrismSelfCut.far F a ρ) (FilteredPrismSelfCut.near F a R)
    (FilteredPrismSelfCut.far_open F a ρ) (FilteredPrismSelfCut.near_open F a R)
    (FilteredPrismSelfCut.cover F a (hρr.trans hrR)) Option.isSome
    (canonical_refines α r F a R hrR hA hR ε (ρ := ρ)) (CompactRotatedCutData.source α r)
    (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)
    (SingleCutCanonicalIncoming.toNear α r F a R hrR hA)
    (SingleCutCanonicalIncoming.near_square α r F a R hrR hA) (m + 1) q
    (FilteredPrismSelfCut.cocycle (by omega) F a (h.1.trans h.2.2))
    (FilteredPrismSelfCut.cocycle_far (by omega) F a (h.1.trans h.2.2))
  rw [cocycle_pullback]
  exact component_source α r F a R hrR hA hR ε h q

def testedSmall := (operation α r F a R hrR hA hR ε h).post
  (SingleCutCanonicalIncoming.smallMap α r F a R hrR hA hR ε)

theorem testedSmall_component (hρr : ρ < r) (q : ℕ) :
    (testedSmall α r F a R hrR hA hR ε h).component q ≫
      (inclusion (FilteredTestedCap.space F R a) (FilteredTestedCap.cover F hR a ε)).f q =
    (inclusion (ambient α) (cover α r F a R hrR hA hR ε ρ)).f ((m + 1) + q) ≫
      (push (CompactInputShortMaps.cylinder α F a hA)).f ((m + 1) + q) ≫
      (FilteredPrismSelfCut.thom (by omega) F a (h.1.trans h.2.2) (hρr.trans hrR)).component q := by
  dsimp only [testedSmall, DegreeLoweringHomology.Map.post]
  rw [Category.assoc, ← HomologicalComplex.comp_f, SingleCutCanonicalIncoming.smallMap_source,
    HomologicalComplex.comp_f]
  have hh := near_component α r F a R hrR hA hR ε h hρr q
  have he := congrArg (fun f => f ≫ (push (FilteredPrismSelfCut.toIncoming F R a)).f q) hh
  simpa only [FilteredPrismSelfCut.thom, DegreeLoweringHomology.Map.post,
    SingleCutCanonicalIncoming.incoming, push_comp, HomologicalComplex.comp_f, Category.assoc] using he

end
end Finsler.SingleCutCanonicalThomSmallLift
