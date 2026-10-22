module

public import Finsler.Loop.OriginalFirstHalfCupOrderCochains
public import Finsler.Topology.PartialDoubleCap

/-! Decompose the actual original gamma into the genuine Thom and
literal tested zero-extension caps. Their near/proper source diagrams
agree with the established rotation-zero two-cap model. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfGammaCaps

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

private theorem absolute_transport (X : TopCat.{0}) (d q i j : ℕ) (hi : d + q = i) (hj : d + q = j)
    (hij : i = j) (ξ : singularCochainGroup (ZMod 2) X d) :
    eqToHom (congrArg (chains X).X hij) ≫ absoluteChain X d q j hj ξ = absoluteChain X d q i hi ξ := by
  cases hij
  exact Category.id_comp _

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def thom : singularCochainGroup (ZMod 2) (ambient α β) (m + 1) :=
  cochainPullback (firstInput α β) (m + 1) (FirstInputRotationZeroTimeFactors.originalThom α h)

def tested : singularCochainGroup (ZMod 2) (ambient α β) p :=
  cochainPullback (firstInput α β) p (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)

theorem gamma_cup : gamma α β r hr h p T = cochainCup (m + 1) p (thom α β h) (tested α β r hr p T) := by
  rw [gamma, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality]
  rfl

theorem gamma_cap (q : ℕ) :
    absoluteChain (ambient α β) ((m + 1) + p) q (((m + 1) + p) + q) rfl (gamma α β r hr h p T) =
    eqToHom (congrArg (chains (ambient α β)).X (Nat.add_assoc (m + 1) p q)) ≫
      PartialDoubleCap.cap (ambient α β) (m + 1) p q (thom α β h) (tested α β r hr p T) := by
  have ha := CupCapOrder.cap_cup (ambient α β) (m + 1) p ((m + 1) + p) q rfl
    (thom α β h) (tested α β r hr p T)
  rw [CupOne.cup_comparison] at ha
  rw [gamma_cup, PartialDoubleCap.cap, ← Category.assoc,
    absolute_transport (ambient α β) (m + 1) (p + q) (((m + 1) + p) + q) ((m + 1) + (p + q))
      (by omega) rfl (Nat.add_assoc (m + 1) p q)]
  exact ha.symm

theorem near_thom (R : ℝ) (hR : R ≤ 1 / 2) :
    cochainPullback (nearSource α β R) (m + 1) (thom α β h) =
    cochainPullback (rotatingZero α β R) (m + 1) (FirstInputRotationAmbientCover.ambientThom α β R hR (by omega) h) := by
  have he := FirstInputRotationZeroTimeFactors.thom_zero α β R hR h
  rw [FirstInputRotationCutCylinder.thom, ← pullback_comp] at he
  rw [thom, ← pullback_comp]
  exact he.symm

theorem near_tested (R : ℝ) (hR : R ≤ 1 / 2) :
    cochainPullback (nearSource α β R) p (tested α β r hr p T) =
    cochainPullback (rotatingZero α β R) p (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T) := by
  have he := FirstInputRotationZeroTimeFactors.tested_zero α β R r hR hr p T
  rw [FirstInputRotationCutCylinder.tested, ← pullback_comp] at he
  rw [tested, ← pullback_comp]
  exact he.symm

theorem proper_thom (R : ℝ) (hR : R ≤ 1 / 2) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (m + 1) (thom α β h) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (m + 1)
      (FirstInputRotationCochains.thom α β R r hR hr (by omega) h) := by
  rw [OriginalFirstHalfJointCover.source_near, pullback_comp, near_thom α β h R hR,
    ← pullback_comp, OriginalFirstHalfJointCochains.rotating_square, pullback_comp,
    FirstInputRotationAmbientCover.thom_source]

theorem proper_tested (R : ℝ) (hR : R ≤ 1 / 2) :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) p (tested α β r hr p T) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) p
      (FirstInputRotationCochains.tested α β R r hR hr p T) := by
  rw [OriginalFirstHalfJointCover.source_near, pullback_comp, near_tested α β r hr p T R hR,
    ← pullback_comp, OriginalFirstHalfJointCochains.rotating_square, pullback_comp,
    FirstInputRotationAmbientCap.tested_restriction]

end
end Finsler.OriginalFirstHalfGammaCaps
