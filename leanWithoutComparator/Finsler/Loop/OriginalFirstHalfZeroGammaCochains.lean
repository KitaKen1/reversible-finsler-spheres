module

public import Finsler.Loop.OriginalFirstHalfZeroCover
public import Finsler.Loop.OriginalFirstHalfGammaCaps

/-! Actual gamma on the near-pair zero cylinder: its literal
ambient/proper restrictions and local coboundary-cap zero. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroGammaCochains

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfZeroCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem coboundary_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (ξ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f (d + 1) (cochainCoboundary (ZMod 2) Y d ξ) =
      cochainCoboundary (ZMod 2) X d (cochainPullback f d ξ) :=
  (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm d (d + 1)) ξ).symm

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def gamma : singularCochainGroup (ZMod 2) (space α β R) ((m + 1) + p) :=
  cochainPullback (OriginalFirstHalfCupOneCochains.nearSource α β R) ((m + 1) + p)
    (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)

theorem ambient_restriction : gamma α β R r hr h p T =
    cochainPullback (OriginalFirstHalfCupOneCochains.rotatingZero α β R) ((m + 1) + p)
      (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T) :=
  OriginalFirstHalfCupOneCochains.gamma_near α β r hr h p T R hR

theorem source_restriction :
    cochainPullback (source α β R r) ((m + 1) + p) (gamma α β R r hr h p T) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + p)
      (FirstInputRotationCupOne.gamma α β R r hR hr h p T) := by
  rw [gamma, ← pullback_comp]
  change cochainPullback (SupportedCap.subspaceMap (space α β R) (FirstInputRotatingCut.source α β R r) ≫
    OriginalFirstHalfCupOneCochains.nearSource α β R) ((m + 1) + p)
      (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T) = _
  rw [← OriginalFirstHalfJointCover.source_near]
  exact OriginalFirstHalfJointCochains.source_gamma α β R r hR hr h p T

theorem far_zero (η : ℝ) :
    cochainPullback (SupportedCap.subspaceMap (space α β R) (cover α β R r η ρ none)) ((m + 1) + p)
      (gamma α β R r hr h p T) = 0 := by
  apply pullback_support (OriginalFirstHalfCupOneCochains.nearSource α β R) (cover α β R r η ρ none)
    (OriginalFirstHalfCupOneCochains.cutFar α β ρ) _ ((m + 1) + p)
    (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T)
    (OriginalFirstHalfCupOneCochains.gamma_cut_far_zero α β r hr h p T)
  intro z hz
  exact hz

include hR in
theorem source_boundary_zero
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainPullback (source α β R r) (((m + 1) + p) + 1)
      (cochainCoboundary (ZMod 2) (space α β R) ((m + 1) + p) (gamma α β R r hr h p T)) = 0 := by
  rw [coboundary_pullback, source_restriction α β R r hR hr h p T]
  exact pullback_closed (FirstInputRotationEndpoints.stage α β R r 0) _ _
    (FirstInputRotationCupOne.gamma_closed α β R r hR hr h p T hT)

include hR in
theorem boundary_small_zero (η : ℝ)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    (inclusion (space α β R) (cover α β R r η ρ)).f ((((m + 1) + p) + 1) + q) ≫
      absoluteChain (space α β R) (((m + 1) + p) + 1) q ((((m + 1) + p) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (space α β R) ((m + 1) + p) (gamma α β R r hr h p T)) = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((space α β R).smallSingularSubcomplex (cover α β R r η ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (space α β R) (cover α β R r η ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  cases i with
  | none =>
    apply SupportedCap.cap_zero_on_simplex _ _ _ q _ rfl _ _ σ.val hi
    rw [coboundary_pullback, far_zero]
    exact map_zero _
  | some i =>
    apply SupportedCap.cap_zero_on_simplex (space α β R) (FirstInputRotatingCut.source α β R r) _ q _ rfl _
      (source_boundary_zero α β R r hR hr h p T hT) σ.val
    intro z hz
    obtain ⟨w, hw, rfl⟩ := near_image α β R r η ρ i (hi hz)
    exact w.property

end
end Finsler.OriginalFirstHalfZeroGammaCochains
