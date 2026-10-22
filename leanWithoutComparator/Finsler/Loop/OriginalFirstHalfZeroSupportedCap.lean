module

public import Finsler.Loop.OriginalFirstHalfZeroCover
public import Finsler.Loop.OriginalFirstHalfBoundedStage

/-! A supported single cap on the actual near-pair zero cylinder
lands in the real bounded zero-slice proper target. No spatial join
cap is inserted here. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroSupportedCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfZeroCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1)) (B η ρ : ℝ)

def sourceBounded : TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B) ⟶ space α β R :=
  EmbeddedCapOutputSupport.source (space α β R) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (FirstInputRotatingCut.source α β R r) (Iso.refl _) (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B)

theorem sourceBounded_mono (q : ℕ) : Mono ((push (sourceBounded α β R r hR hr F B)).f q) :=
  EmbeddedCapOutputSupport.source_mono (space α β R) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (FirstInputRotatingCut.source α β R r) (Iso.refl _) (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B) q

theorem sourceBounded_stage : sourceBounded α β R r hR hr F B ≫ OriginalFirstHalfCupOneCochains.rotatingZero α β R =
    OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F B ≫
      FirstInputRotationAmbientCap.source α β R r hR hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (d : ℕ) (ξ : singularCochainGroup (ZMod 2) (space α β R) d)
  (ψ : singularCochainGroup (ZMod 2) (FirstInputRotationCochains.space α β R r) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (space α β R) (cover α β R r η ρ none)) d ξ = 0)
  (hsource : cochainPullback (source α β R r) d ξ =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) d ψ)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η d ψ)

include hfar hsource good in
theorem parent_bound (q : ℕ)
    (σ : ((space α β R).smallSingularSubcomplex (cover α β R r η ρ) : SSet) _⦋d + q⦌)
    (hc : (TopCat.toSSet.obj (space α β R)).ιChainComplex σ.val ≫
      absoluteChain (space α β R) d q (d + q) rfl ξ ≠ 0) :
    Set.range ((space α β R).toSSetObjEquiv _ σ.val) ⊆
      source α β R r '' OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (space α β R) (cover α β R r η ρ) σ.val).mp σ.property
  cases i with
  | none => exact (hc (SupportedCap.cap_zero_on_simplex _ _ d q (d + q) rfl ξ hfar σ.val hi)).elim
  | some i =>
    obtain ⟨τ, hτ, hτrange⟩ := EmbeddedCapOutputSupport.exists_parent (space α β R)
      (TopCat.of (FirstInputRotatingCut.source α β R r)) (FirstInputRotatingCut.source α β R r) (Iso.refl _)
      (FirstInputRotationEndpoints.cover α β R r η 0 i) (d + q) σ.val
      (hi.trans (near_image α β R r η ρ i))
    change (TopCat.toSSet.map (source α β R r)).app (Opposite.op ⦋d + q⦌) τ = σ.val at hτ
    let τrot := (TopCat.toSSet.map (FirstInputRotationEndpoints.stage α β R r 0)).app (Opposite.op ⦋d + q⦌) τ
    have hsmall : τrot ∈ ((FirstInputRotationCochains.space α β R r).smallSingularSubcomplex
        (FirstInputRotationFilteredCap.rectangle α β R r η)).obj (Opposite.op ⦋d + q⦌) := by
      apply (TopCat.mem_smallSingularSubcomplex_iff _ _ τrot).mpr
      refine ⟨i, ?_⟩
      rintro _ ⟨t, rfl⟩
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
      exact hτrange ⟨t, rfl⟩
    have hnz : (TopCat.toSSet.obj (TopCat.of (FirstInputRotatingCut.source α β R r))).ιChainComplex τ ≫
        absoluteChain (TopCat.of (FirstInputRotatingCut.source α β R r)) d q (d + q) rfl
          (cochainPullback (source α β R r) d ξ) ≠ 0 := by
      intro hz
      have hn := CapOutputSupport.cap_push_simplex (source α β R r) d q ξ τ
      rw [hτ, hz, zero_comp] at hn
      exact hc hn.symm
    have hrot : (TopCat.toSSet.obj (FirstInputRotationCochains.space α β R r)).ιChainComplex τrot ≫
        absoluteChain (FirstInputRotationCochains.space α β R r) d q (d + q) rfl ψ ≠ 0 := by
      intro hz
      have hn := CapOutputSupport.cap_push_simplex (FirstInputRotationEndpoints.stage α β R r 0) d q ψ τ
      rw [← hsource] at hn
      change _ = (TopCat.toSSet.obj (FirstInputRotationCochains.space α β R r)).ιChainComplex τrot ≫ absoluteChain _ d q (d + q) rfl ψ at hn
      rw [hz] at hn
      haveI := OriginalFirstHalfJointSupportedCap.stage_mono α β R r q
      apply hnz
      apply (cancel_mono ((push (FirstInputRotationEndpoints.stage α β R r 0)).f q)).mp
      rw [zero_comp]
      exact hn
    have hb := good q ⟨τrot, hsmall⟩ hrot
    rintro _ ⟨t, rfl⟩
    refine ⟨(TopCat.of (FirstInputRotatingCut.source α β R r)).toSSetObjEquiv _ τ t, ?_, ?_⟩
    · have ht := hb _ ⟨t, rfl⟩
      change (((FirstInputRotationCochains.space α β R r).toSSetObjEquiv _
        ((TopCat.toSSet.map (FirstInputRotationEndpoints.stage α β R r 0)).app (Opposite.op ⦋d + q⦌) τ)) t) ∈
          FirstInputRotationFilteredCap.domain α β R r hR hr F B at ht
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at ht
      exact ht
    · have he := congrArg (fun s => (space α β R).toSSetObjEquiv _ s t) hτ
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
      exact he

def component (q : ℕ) : (small (space α β R) (cover α β R r η ρ)).X (d + q) ⟶
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))).X q :=
  EmbeddedCapOutputSupport.component (space α β R) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (FirstInputRotatingCut.source α β R r) (Iso.refl _) (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B)
    (cover α β R r η ρ) d ξ (parent_bound α β R r hR hr F B η ρ d ξ ψ hfar hsource good) q

theorem component_source (q : ℕ) :
    component α β R r hR hr F B η ρ d ξ ψ hfar hsource good q ≫ (push (sourceBounded α β R r hR hr F B)).f q =
    (inclusion (space α β R) (cover α β R r η ρ)).f (d + q) ≫ absoluteChain (space α β R) d q (d + q) rfl ξ :=
  EmbeddedCapOutputSupport.component_source (space α β R) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (FirstInputRotatingCut.source α β R r) (Iso.refl _) (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B)
    (cover α β R r η ρ) d ξ (parent_bound α β R r hR hr F B η ρ d ξ ψ hfar hsource good) q

end
end Finsler.OriginalFirstHalfZeroSupportedCap
