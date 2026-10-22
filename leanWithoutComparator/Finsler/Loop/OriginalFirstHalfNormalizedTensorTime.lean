module

public import Finsler.Loop.FirstFactorOriginalTimeComparison
public import Finsler.Loop.OriginalFirstHalfNormalizationTime
public import Finsler.Loop.OriginalFirstHalfNormalizationExternalShuffle

/-! The actual normalized original-cylinder cap applied after first-
input tensor time. It agrees with the genuine full original-input time
operation after the external cross in the identical bounded target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizedTensorTime

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut Finsler.OriginalFirstHalfCupOneCochains
open Finsler.OriginalFirstHalfJointSupportedCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {κ : ℝ} (hκ : 0 < κ) (hκR : κ < R) (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (hη : 0 < η) (hρr : ρ < r)
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def cap (q : ℕ) :=
  SingleCapTimePrism.aligned (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
    (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT) q

theorem cap_comm (q : ℕ) :
    cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT (q + 1) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q =
    (chains (ambient α β)).d (((m + 1) + (m + p)) + q + 2) (((m + 1) + (m + p)) + q + 1) ≫
      cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q :=
  SingleCapTimePrism.aligned_comm _ _ _ _ _ _ _ q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of (P × Q)) t)).f (((m + 1) + (m + p)) + q + 1) ≫
      cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q = 0 := by
  apply SingleCapTimePrism.endpoint_zero (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
    (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT)
    (inner α β δ) (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ)
    (OriginalFirstHalfNormalizationCup.order_inner_zero α β r hr h p T hκ)
    (push (source α β R r hR hr F B)) (source_mono α β R r hR hr F B)
    (OriginalFirstHalfNormalizationBounded.normalizedCap_source α β R r hR hr h p T hκ F B η goodN) t _ q
  intro x
  rcases ht with rfl | rfl
  · exact (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le
  · exact (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le

def tensorTime : DegreeLoweringHomology.Map (chains (TopCat.of P) ⊗ chains (TopCat.of Q))
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p)) :=
  FirstFactorOriginalTimeComparison.tensorOperation (TopCat.of P) (TopCat.of Q) ((m + 1) + (m + p))
    (cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT)
    (cap_comm α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 0 (Or.inl rfl))
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 1 (Or.inr rfl))

theorem component_normal (q : ℕ) :
    (tensorTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).component q =
    (FullFirstFactorTimePrism.prism (TopCat.of P) (TopCat.of Q)).hom
      (((m + 1) + (m + p)) + q) (((m + 1) + (m + p)) + q + 1) ≫
      (SmallRectangleCross.ambient (TopCat.of (ClosedInterval × P)) (TopCat.of Q)).f
        (((m + 1) + (m + p)) + q + 1) ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f
        (((m + 1) + (m + p)) + q + 1) ≫
      cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q := by
  rfl

theorem homology_eq (q : ℕ) :
    ((OriginalFirstHalfNormalizationTime.normalizedTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).pre
      (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))).homology q =
    (tensorTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).homology q := by
  exact FirstFactorOriginalTimeComparison.homology_eq (TopCat.of P) (TopCat.of Q) ((m + 1) + (m + p))
    (cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT)
    (cap_comm α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 0 (Or.inl rfl))
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 1 (Or.inr rfl)) q

theorem retained_homology_eq (q : ℕ) :
    (((OriginalFirstHalfNormalizationTime.normalizedTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).pre
      (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))).post
      (push (retained α β R r hR hr F B))).homology q =
    ((tensorTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).post
      (push (retained α β R r hR hr F B))).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    homology_eq α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q]

end
end Finsler.OriginalFirstHalfNormalizedTensorTime
