module

public import Finsler.Loop.FirstInputRotationCochains
public import Finsler.Loop.CompactJoinCocycle
public import Finsler.Loop.TestedCupOneSupport

/-! The actual join/cut-tested cup-one on the genuine proper rotating
cut domain. Its inner/far and tested-length supports come from actual
naturality; every part of the acyclic-model primitive is covered. -/

@[expose] public section
namespace Finsler.FirstInputRotationCupOne

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.FirstInputRotationCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1)

def spatial : space α β R r ⟶ TopCat.of (P × Q) :=
  TopCat.ofHom ⟨fun z => z.2.val.2.val, by fun_prop⟩

def join {κ : ℝ} (hκ : 0 < κ) : singularCochainGroup (ZMod 2) (space α β R r) (m + 1) :=
  cochainPullback (spatial α β R r) (m + 1) (CompactJoinCocycle.cocycle α β (by omega) hκ)

variable {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def gamma : singularCochainGroup (ZMod 2) (space α β R r) ((m + 1) + p) :=
  cochainCup (m + 1) p (thom α β R r hR hr (by omega) h) (tested α β R r hR hr p T)

def primitive {κ : ℝ} (hκ : 0 < κ) :
    singularCochainGroup (ZMod 2) (space α β R r) ((m + 1) + (m + p)) :=
  CupOne.cupOne (space α β R r) (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega)
    (join α β R r hκ) (gamma α β R r hR hr h p T)

theorem join_closed {κ : ℝ} (hκ : 0 < κ) :
    cochainCoboundary (ZMod 2) (space α β R r) (m + 1) (join α β R r hκ) = 0 :=
  pullback_closed (spatial α β R r) (m + 1) _ (CompactJoinCocycle.cocycle_closed α β (by omega) hκ)

theorem gamma_closed
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (space α β R r) ((m + 1) + p) (gamma α β R r hR hr h p T) = 0 :=
  cochainCupZMod2_respects_cocycles (m + 1) p _ _ (thom_closed α β R r hR hr (by omega) h)
    (tested_closed α β R r hR hr p T hT)

theorem boundary {κ : ℝ} (hκ : 0 < κ)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (space α β R r) ((m + 1) + (m + p))
      (primitive α β R r hR hr h p T hκ) =
      CupOne.cup (space α β R r) (m + 1) ((m + 1) + p) (((m + 1) + (m + p)) + 1) (by omega)
        (join α β R r hκ) (gamma α β R r hR hr h p T) -
      CupOne.cup (space α β R r) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
        (gamma α β R r hR hr h p T) (join α β R r hκ) :=
  CupOne.boundary_cocycles (space α β R r) (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega)
    _ _ (join_closed α β R r hκ) (gamma_closed α β R r hR hr h p T hT)

theorem primitive_inner_zero {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (space α β R r) (collar α β R r δ)) ((m + 1) + (m + p))
      (primitive α β R r hR hr h p T hκ) = 0 := by
  apply CupOne.restriction_zero _ (m + 1) ((m + 1) + p) ((m + 1) + (m + p)) (by omega) _ _ (Or.inr ?_)
  rw [gamma, cochainCup_naturality, thom_inner_zero α β R r hR hr (by omega) h, cochainCup_zero_left]

theorem primitive_short_zero {κ : ℝ} (hκ : 0 < κ) (F : ReversibleMetric (m + 1)) (L : ℝ)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0) :
    cochainPullback (SupportedCap.subspaceMap (space α β R r)
      (TestedCupOneSupport.short F (testedMap α β R r hR hr) L)) ((m + 1) + (m + p))
      (primitive α β R r hR hr h p T hκ) = 0 :=
  TestedCupOneSupport.primitive_zero F (testedMap α β R r hR hr) L (m + 1) p
    (thom α β R r hR hr (by omega) h) T hshort (m + 1) ((m + 1) + (m + p)) (by omega) _

theorem primitive_boundary_short_zero {κ : ℝ} (hκ : 0 < κ) (F : ReversibleMetric (m + 1)) (L : ℝ)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0) :
    cochainPullback (SupportedCap.subspaceMap (space α β R r)
      (TestedCupOneSupport.short F (testedMap α β R r hR hr) L)) (((m + 1) + (m + p)) + 1)
      (cochainCoboundary (ZMod 2) (space α β R r) ((m + 1) + (m + p))
        (primitive α β R r hR hr h p T hκ)) = 0 :=
  TestedCupOneSupport.coboundary_zero F (testedMap α β R r hR hr) L ((m + 1) + (m + p)) _
    (primitive_short_zero α β R r hR hr h p T hκ F L hshort)

end
end Finsler.FirstInputRotationCupOne
