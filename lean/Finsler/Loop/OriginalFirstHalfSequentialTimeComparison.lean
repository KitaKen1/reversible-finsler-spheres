module

public import Finsler.Loop.OriginalFirstHalfSequentialCupAgreement
public import Finsler.Loop.OriginalFirstHalfCupOrderTimeHomology
public import Finsler.Loop.SingleCapTimePrismComparison

/-! The real localized join/gamma full-time operation agrees with
the original-input cup-first full-time operation by actual relative
cover comparisons, already in the identical bounded proper target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfSequentialTimeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCupOrderCochains
open Finsler.OriginalFirstHalfSequentialCommonCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)
  (F : ReversibleMetric (m + 1)) (B : ℝ)

def fromCap {ι : Type*} (U : ι → Set (ambient α β)) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ)
    (c : DegreeLoweringHomology.Map (small (ambient α β) U)
      (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B)))
      (((m + 1) + (m + p)) + 1))
    (hs : ∀ q, c.component q ≫ (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
      (inclusion (ambient α β) U).f ((((m + 1) + (m + p)) + 1) + q) ≫
        absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
          ((((m + 1) + (m + p)) + 1) + q) rfl (originalOrder α β r hr h p T hκ false)) :=
  SingleCapTimePrism.operation (TopCat.of (P × Q)) U hU hcover
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) ((m + 1) + (m + p)) c
    (inner α β δ) (originalOrder α β r hr h p T hκ false) (original_inner_zero α β r hr h p T hκ false)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B) hs
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)

variable (η : ℝ) (hη : 0 < η) (hκR : κ < R) (hρr : ρ < r)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (good : ∀ b, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (properOrder α β R r hR hr h p T hκ b))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def onJoin := fromCap α β R r hR hr h p T hκ F B
  (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ)
  (OriginalFirstHalfJoinTimeCover.cover_open α β R r η ρ κ)
  (OriginalFirstHalfJoinTimeCover.cover_univ α β R r η ρ hη hκR hρr)
  (OriginalFirstHalfSequentialJoinGamma.operation α β R r η hR hr h p T hκ F B goodΓ hT)
  (OriginalFirstHalfSequentialJoinGamma.component_source α β R r η hR hr h p T hκ F B goodΓ hT)

def onCommon := fromCap α β R r hR hr h p T hκ F B
  (cover α β R r η κ ρ) (cover_open α β R r η κ ρ) (cover_univ α β R r η κ ρ hη hκR hρr)
  (OriginalFirstHalfSequentialCupAgreement.sequential α β R r η hR hr h p T hκ F B goodΓ hT)
  (OriginalFirstHalfSequentialCupAgreement.sequential_source α β R r η hR hr h p T hκ F B goodΓ hT)

theorem join_common (q : ℕ) :
    (onJoin α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).homology q =
      (onCommon α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).homology q := by
  apply SingleCapTimePrismComparison.homology_eq (TopCat.of (P × Q))
    (cover α β R r η κ ρ) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ)
    Prod.fst (fun _ _ hz => hz.1)
    (cover_open α β R r η κ ρ) (cover_univ α β R r η κ ρ hη hκR hρr)
    (OriginalFirstHalfJoinTimeCover.cover_open α β R r η ρ κ)
    (OriginalFirstHalfJoinTimeCover.cover_univ α β R r η ρ hη hκR hρr)
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) ((m + 1) + (m + p))
    (OriginalFirstHalfSequentialCupAgreement.sequential α β R r η hR hr h p T hκ F B goodΓ hT)
    (OriginalFirstHalfSequentialJoinGamma.operation α β R r η hR hr h p T hκ F B goodΓ hT)
    (inner α β δ) (originalOrder α β r hr h p T hκ false) (original_inner_zero α β r hr h p T hκ false)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B)
    (OriginalFirstHalfSequentialCupAgreement.sequential_source α β R r η hR hr h p T hκ F B goodΓ hT)
    (OriginalFirstHalfSequentialJoinGamma.component_source α β R r η hR hr h p T hκ F B goodΓ hT)
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)
    (fun _ => rfl) q

theorem cup_common (q : ℕ) :
    (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT false).homology q =
      (onCommon α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).homology q := by
  apply SingleCapTimePrismComparison.homology_eq (TopCat.of (P × Q))
    (cover α β R r η κ ρ) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    Prod.snd (fun _ _ hz => hz.2)
    (cover_open α β R r η κ ρ) (cover_univ α β R r η κ ρ hη hκR hρr)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) ((m + 1) + (m + p))
    (OriginalFirstHalfSequentialCupAgreement.sequential α β R r η hR hr h p T hκ F B goodΓ hT)
    (OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η good false hT)
    (inner α β δ) (originalOrder α β r hr h p T hκ false) (original_inner_zero α β r hr h p T hκ false)
    (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B))
    (OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B)
    (OriginalFirstHalfSequentialCupAgreement.sequential_source α β R r η hR hr h p T hκ F B goodΓ hT)
    (OriginalFirstHalfCupOrderBounded.cap_source α β R r hR hr h p T hκ F B η good false)
    (fun x => show distance (m + 1) (0, α x.1) ≤ δ from (UniformSelfCutCollar.distance_zero α x.1).le.trans h.1.le)
    (fun x => show distance (m + 1) (1, α x.1) ≤ δ from (UniformSelfCutCollar.distance_one α x.1).le.trans h.1.le)
    (fun t => (OriginalFirstHalfSequentialCupAgreement.component_eq α β R r η hR hr h p T hκ F B goodΓ good hT t).symm) q

theorem join_cup (q : ℕ) :
    (onJoin α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).homology q =
      (OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT false).homology q :=
  (join_common α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT q).trans
    (cup_common α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ good hT q).symm

theorem retained_join_cup (q : ℕ) :
    ((onJoin α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).post
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B))).homology q =
    ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT false).post
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B))).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    join_cup α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ good hT q]

end
end Finsler.OriginalFirstHalfSequentialTimeComparison
