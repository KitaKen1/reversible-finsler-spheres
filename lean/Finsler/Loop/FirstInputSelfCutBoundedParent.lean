module

public import Finsler.Loop.FirstInputSelfCutBoundedSpace
public import Finsler.Loop.SingleInputCutMetricAdequacy

/-! Lift the actual ambient nonzero parent to the genuine proper cut.
Its cap remains nonzero by actual cap naturality. The before-tested
metric adequacy then bounds the whole parent in the individual target. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedParent

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ ρ : ℝ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (ambient α) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) d φ = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshort : cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
    (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) d
      (cochainPullback (source α r) d φ) = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

include hfar hε hradius hsmall hfirst hshort hA in
theorem parent_image (q : ℕ)
    (s : ((ambient α).smallSingularSubcomplex (OriginalFirstHalfFactorwiseCover.first σ) : SSet) _⦋d + q⦌)
    (hnz : (TopCat.toSSet.obj (ambient α)).ιChainComplex s.val ≫
      absoluteChain (ambient α) d q (d + q) rfl φ ≠ 0) :
    ∃ i, Set.range ((ambient α).toSSetObjEquiv _ s.val) ⊆
      FirstInputSelfCutBoundedSpace.source α r hr F (a - L + 3 * ε) ''
        FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ i := by
  classical
  obtain ⟨c, hc⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α)
    (OriginalFirstHalfFactorwiseCover.first σ) s.val).mp s.property
  have hs : s.val ∈ ((ambient α).smallSingularSubcomplex (cover α r hr κ ρ)).obj (Opposite.op ⦋d + q⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff (ambient α) (cover α r hr κ ρ) s.val).mpr
      ⟨firstIndex c, hc.trans (hfirst c)⟩
  obtain ⟨i, hi⟩ := FirstInputSelfCutCarrierCap.parent_image α r hr κ ρ d φ hfar q ⟨s.val, hs⟩ hnz
  have hD : Set.range ((ambient α).toSSetObjEquiv _ s.val) ⊆ CompactRotatedCutData.source α r := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := hi hz
    exact w.property
  let τ := SupportedCap.simplexLift (ambient α) (CompactRotatedCutData.source α r) s.val hD
  have hτ : (TopCat.toSSet.map (source α r)).app (Opposite.op ⦋d + q⦌) τ = s.val :=
    SupportedCap.simplexLift_image (ambient α) (CompactRotatedCutData.source α r) s.val hD
  have hcoord (t) : source α r ((OriginalFirstHalfCutNormalizedFactors.cutSpace α r).toSSetObjEquiv _ τ t) =
      (ambient α).toSSetObjEquiv _ s.val t := by
    have hh := congrArg (fun u => (ambient α).toSSetObjEquiv _ u t) hτ
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at hh
    exact hh
  have hproper : (TopCat.toSSet.obj (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)).ιChainComplex τ ≫
      absoluteChain (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) d q (d + q) rfl
        (cochainPullback (source α r) d φ) ≠ 0 := by
    intro hz
    have hh := CapOutputSupport.cap_push_simplex (source α r) d q φ τ
    rw [hτ, hz, zero_comp] at hh
    exact hnz hh.symm
  have hfine : ∀ z ∈ Set.range ((OriginalFirstHalfCutNormalizedFactors.cutSpace α r).toSSetObjEquiv _ τ),
      z.val ∈ OriginalFirstHalfFactorwiseCover.first σ c := by
    rintro z ⟨t, rfl⟩
    exact hc ⟨t, (hcoord t).symm⟩
  obtain ⟨w, hw, hL⟩ := CompactSingleCutLengthOscillation.cap_witness α r hr F L d q
    (cochainPullback (source α r) d φ) hshort τ hproper
  have hbound : ∀ z ∈ Set.range ((OriginalFirstHalfCutNormalizedFactors.cutSpace α r).toSSetObjEquiv _ τ),
      SobolevLength.length F (OriginalFirstHalfCutOutputJoinData.kept α r hr z) < a - L + 3 * ε := by
    intro z hz
    have htest : L - ε ≤ SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr z) := by
      have hh := (abs_lt.mp (hsmall c z w (hfine z hz) (hfine w hw))).1
      linarith
    apply SelfCutLengthControl.filtered_retained_lt F hε
      (FirstInputRotationOriginalFactors.originalCut α r hr z) _ (hA z.val.2) htest
    change SupportedSelfCut.distance (m + 1) (z.val.1, α z.val.2) < SelfCutLengthControl.radius F hε
    exact z.property.trans_lt hradius
  refine ⟨i, ?_⟩
  rintro z ⟨t, rfl⟩
  let zD := (OriginalFirstHalfCutNormalizedFactors.cutSpace α r).toSSetObjEquiv _ τ t
  have hb := hbound zD ⟨t, rfl⟩
  let zB : FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε) := ⟨zD.val, ⟨zD.property, hb⟩⟩
  refine ⟨zB, ?_, hcoord t⟩
  have he : FirstInputSelfCutBoundedSpace.toCut α r hr F (a - L + 3 * ε) zB = zD := Subtype.ext rfl
  change FirstInputSelfCutBoundedSpace.toCut α r hr F (a - L + 3 * ε) zB ∈ carrier α r hr κ i
  rw [he]
  obtain ⟨v, hv, hev⟩ := hi ⟨t, rfl⟩
  have hvz : v = zD := Subtype.ext (hev.trans (hcoord t).symm)
  rwa [← hvz]

end
end Finsler.FirstInputSelfCutBoundedParent
