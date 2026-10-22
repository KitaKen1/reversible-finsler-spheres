module

public import Finsler.Loop.OriginalFirstHalfSequentialCommonCover
public import Finsler.Loop.OriginalFirstHalfSequentialJoinGamma
public import Finsler.Loop.OriginalFirstHalfCupOrderBounded

/-! The actual localized join followed by gamma equals the genuine
join-first cup cap on a real common cover, in the same bounded target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfSequentialCupAgreement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfCupOrderCochains
open Finsler.OriginalFirstHalfSequentialCommonCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p) {κ : ℝ} (hκ : 0 < κ)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (good : ∀ b, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (properOrder α β R r hR hr h p T hκ b))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def sequential := (OriginalFirstHalfSequentialJoinGamma.operation α β R r η hR hr h p T hκ F B goodΓ hT).pre
  (toJoin α β R r η κ ρ)

def cup := (OriginalFirstHalfCupOrderBounded.operation α β R r hR hr h p T hκ F B η good false hT).pre
  (toCup α β R r η κ ρ)

theorem sequential_source (q : ℕ) :
    (sequential α β R r η hR hr h p T hκ F B goodΓ hT).component q ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
        ((((m + 1) + (m + p)) + 1) + q) rfl (originalOrder α β r hr h p T hκ false) := by
  dsimp only [sequential, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, OriginalFirstHalfSequentialJoinGamma.component_source, ← Category.assoc]
  have hi := congrArg (fun f => f.f ((((m + 1) + (m + p)) + 1) + q))
    (toJoin_inclusion α β R r η κ ρ)
  simp only [HomologicalComplex.comp_f] at hi
  rw [hi]
  rfl

theorem cup_source (q : ℕ) :
    (cup α β R r η hR hr h p T hκ F B good hT).component q ≫
      (push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q =
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
        ((((m + 1) + (m + p)) + 1) + q) rfl (originalOrder α β r hr h p T hκ false) := by
  dsimp only [cup, DegreeLoweringHomology.Map.pre, OriginalFirstHalfCupOrderBounded.operation]
  rw [Category.assoc, OriginalFirstHalfCupOrderBounded.cap_source, ← Category.assoc]
  have hi := congrArg (fun f => f.f ((((m + 1) + (m + p)) + 1) + q))
    (toCup_inclusion α β R r η κ ρ)
  simp only [HomologicalComplex.comp_f] at hi
  rw [hi]

theorem component_eq (q : ℕ) :
    (sequential α β R r η hR hr h p T hκ F B goodΓ hT).component q =
      (cup α β R r η hR hr h p T hκ F B good hT).component q := by
  haveI := OriginalFirstHalfJointSupportedCap.source_mono α β R r hR hr F B q
  apply (cancel_mono ((push (OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B)).f q)).mp
  rw [sequential_source, cup_source]

theorem homology_eq (q : ℕ) :
    (sequential α β R r η hR hr h p T hκ F B goodΓ hT).homology q =
      (cup α β R r η hR hr h p T hκ F B good hT).homology q := by
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  exact component_eq α β R r η hR hr h p T hκ F B goodΓ good hT

end
end Finsler.OriginalFirstHalfSequentialCupAgreement
