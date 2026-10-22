module

public import Finsler.Loop.OriginalFirstHalfJointCover
public import Finsler.Loop.FirstInputRotationSupportedCap

/-! Lift an original-input cap into the bounded rotation-zero proper
domain. Both far supports control whole parents before the spatial
join cap has been applied. The actual proper bound is reused. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfJointSupportedCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointCover
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationFilteredCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1)) (B η κ ρ : ℝ)

def bounded : Set (FirstInputRotatingCut.source α β R r) :=
  FirstInputRotationEndpoints.stage α β R r 0 ⁻¹' domain α β R r hR hr F B

def source : TopCat.of (bounded α β R r hR hr F B) ⟶ ambient α β :=
  EmbeddedCapOutputSupport.source (ambient α β) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (proper α β R r) (properIso α β R r) (bounded α β R r hR hr F B)

def boundedStage : TopCat.of (bounded α β R r hR hr F B) ⟶ TopCat.of (domain α β R r hR hr F B) :=
  TopCat.ofHom ⟨fun z => ⟨FirstInputRotationEndpoints.stage α β R r 0 z.val, z.property⟩, by fun_prop⟩

def retained : TopCat.of (bounded α β R r hR hr F B) ⟶ TopCat.of (JoinedFilteredCap.sublevel F B) :=
  boundedStage α β R r hR hr F B ≫ FirstInputRotationFilteredCap.retained α β R r hR hr F B

theorem stage_mono (q : ℕ) : Mono ((push (FirstInputRotationEndpoints.stage α β R r 0)).f q) := by
  haveI : Mono (FirstInputRotationEndpoints.stage α β R r 0) :=
    (TopCat.mono_iff_injective _).mpr (fun x y h => congrArg Prod.snd h)
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (FirstInputRotationEndpoints.stage α β R r 0)).app (Opposite.op ⦋q⦌))))

theorem source_mono (q : ℕ) : Mono ((push (source α β R r hR hr F B)).f q) :=
  EmbeddedCapOutputSupport.source_mono (ambient α β) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (proper α β R r) (properIso α β R r) (bounded α β R r hR hr F B) q

variable (d : ℕ) (ξ : singularCochainGroup (ZMod 2) (ambient α β) d)
  (ψ : singularCochainGroup (ZMod 2) (space α β R r) d)
  (hjoin : cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) d ξ = 0)
  (hcut : cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) d ξ = 0)
  (hsource : cochainPullback (OriginalFirstHalfJointCover.source α β R r) d ξ =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) d ψ)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η d ψ)

include hjoin hcut hsource good in
theorem parent_bound (q : ℕ)
    (σ : ((ambient α β).smallSingularSubcomplex (cover α β R r η κ ρ) : SSet) _⦋d + q⦌)
    (hc : (TopCat.toSSet.obj (ambient α β)).ιChainComplex σ.val ≫
      absoluteChain (ambient α β) d q (d + q) rfl ξ ≠ 0) :
    Set.range ((ambient α β).toSSetObjEquiv _ σ.val) ⊆
      OriginalFirstHalfJointCover.source α β R r '' bounded α β R r hR hr F B := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β)
    (cover α β R r η κ ρ) σ.val).mp σ.property
  cases i with
  | none =>
    exact (hc (SupportedCap.cap_zero_on_simplex _ _ d q (d + q) rfl ξ hjoin σ.val
      (fun z hz => by
        change κ ≤ pairGap α β z
        exact (show κ < pairGap α β z from hi hz).le))).elim
  | some i =>
    cases i with
    | none => exact (hc (SupportedCap.cap_zero_on_simplex _ _ d q (d + q) rfl ξ hcut σ.val hi)).elim
    | some i =>
      obtain ⟨τ, hτ, hτrange⟩ := EmbeddedCapOutputSupport.exists_parent (ambient α β)
        (TopCat.of (FirstInputRotatingCut.source α β R r)) (proper α β R r) (properIso α β R r)
        (FirstInputRotationEndpoints.cover α β R r η 0 i) (d + q) σ.val
        (hi.trans (near_image α β R r η κ ρ i))
      change (TopCat.toSSet.map (OriginalFirstHalfJointCover.source α β R r)).app (Opposite.op ⦋d + q⦌) τ = σ.val at hτ
      let τrot := (TopCat.toSSet.map (FirstInputRotationEndpoints.stage α β R r 0)).app (Opposite.op ⦋d + q⦌) τ
      have hsmall : τrot ∈ ((space α β R r).smallSingularSubcomplex (rectangle α β R r η)).obj (Opposite.op ⦋d + q⦌) := by
        apply (TopCat.mem_smallSingularSubcomplex_iff _ _ τrot).mpr
        refine ⟨i, ?_⟩
        rintro _ ⟨t, rfl⟩
        rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
        exact hτrange ⟨t, rfl⟩
      have hnz : (TopCat.toSSet.obj (TopCat.of (FirstInputRotatingCut.source α β R r))).ιChainComplex τ ≫
          absoluteChain (TopCat.of (FirstInputRotatingCut.source α β R r)) d q (d + q) rfl
            (cochainPullback (OriginalFirstHalfJointCover.source α β R r) d ξ) ≠ 0 := by
        intro hz
        have hn := CapOutputSupport.cap_push_simplex (OriginalFirstHalfJointCover.source α β R r) d q ξ τ
        rw [hτ, hz, zero_comp] at hn
        exact hc hn.symm
      have hrot : (TopCat.toSSet.obj (space α β R r)).ιChainComplex τrot ≫
          absoluteChain (space α β R r) d q (d + q) rfl ψ ≠ 0 := by
        intro hz
        have hn := CapOutputSupport.cap_push_simplex (FirstInputRotationEndpoints.stage α β R r 0) d q ψ τ
        rw [← hsource] at hn
        change _ = (TopCat.toSSet.obj (space α β R r)).ιChainComplex τrot ≫ absoluteChain _ d q (d + q) rfl ψ at hn
        rw [hz] at hn
        haveI := stage_mono α β R r q
        apply hnz
        apply (cancel_mono ((push (FirstInputRotationEndpoints.stage α β R r 0)).f q)).mp
        rw [zero_comp]
        exact hn
      have hb := good q ⟨τrot, hsmall⟩ hrot
      rintro _ ⟨t, rfl⟩
      refine ⟨(TopCat.of (FirstInputRotatingCut.source α β R r)).toSSetObjEquiv _ τ t, ?_, ?_⟩
      · have ht := hb _ ⟨t, rfl⟩
        change (((space α β R r).toSSetObjEquiv _
          ((TopCat.toSSet.map (FirstInputRotationEndpoints.stage α β R r 0)).app (Opposite.op ⦋d + q⦌) τ)) t) ∈
            domain α β R r hR hr F B at ht
        rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at ht
        exact ht
      · have he := congrArg (fun s => (ambient α β).toSSetObjEquiv _ s t) hτ
        rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
        exact he

def component (q : ℕ) :
    (small (ambient α β) (cover α β R r η κ ρ)).X (d + q) ⟶
      (chains (TopCat.of (bounded α β R r hR hr F B))).X q :=
  EmbeddedCapOutputSupport.component (ambient α β) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (proper α β R r) (properIso α β R r) (bounded α β R r hR hr F B) (cover α β R r η κ ρ) d ξ
    (parent_bound α β R r hR hr F B η κ ρ d ξ ψ hjoin hcut hsource good) q

theorem component_source (q : ℕ) :
    component α β R r hR hr F B η κ ρ d ξ ψ hjoin hcut hsource good q ≫
      (push (source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f (d + q) ≫
      absoluteChain (ambient α β) d q (d + q) rfl ξ :=
  EmbeddedCapOutputSupport.component_source (ambient α β) (TopCat.of (FirstInputRotatingCut.source α β R r))
    (proper α β R r) (properIso α β R r) (bounded α β R r hR hr F B) (cover α β R r η κ ρ) d ξ
    (parent_bound α β R r hR hr F B η κ ρ d ξ ψ hjoin hcut hsource good) q

end
end Finsler.OriginalFirstHalfJointSupportedCap
