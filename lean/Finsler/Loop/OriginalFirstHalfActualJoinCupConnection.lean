module

public import Finsler.Loop.OriginalFirstHalfAnnularTimeAssembly
public import Finsler.Loop.OriginalFirstHalfZeroTimeComparison

/-! Connect the genuine existing spatial join/full-time rotating
operations to both actual original-input cup time models. This does
not yet identify the cut-first cup model with geometric cut/output join. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfActualJoinCupConnection

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfJointSupportedCap Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  {κ : ℝ} (hκ : 0 < κ) (h2κR : 2 * κ ≤ R) (hκR : κ < R)
  (hη : 0 < η) (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem existing_to_sequential (q : ℕ) :
    (FirstInputRotationJoinedTime.joined α β hκ h2κR hR hr p T h F B η hη hρr oldGood hT 0).homology q =
    ((OriginalFirstHalfSequentialTimeComparison.onJoin α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ hT).post
      (push (retained α β R r hR hr F B))).homology q := by
  have he := OriginalFirstHalfZeroTimeComparison.joined_existing α β R r hR hr h p T F B η hη hρr goodΓ oldGood hT hκ h2κR q
  have ha := congrArg (fun k => k ≫ HomologicalComplex.homologyMap (push (retained α β R r hR hr F B)) q)
    (OriginalFirstHalfAnnularTimeAssembly.joined_sequential α β R r η hκ h2κR hκR hη hR hr h hρr p T F B goodΓ hT q)
  apply he.symm.trans
  simpa only [DegreeLoweringHomology.Map.post_homology, OriginalFirstHalfZeroTimeComparison.joined,
    OriginalFirstHalfAnnularJoinFirstIdentity.joined] using ha

variable (good : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η
  (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v))

include goodΓ in
theorem existing_to_join_cup (q : ℕ) :
    (FirstInputRotationJoinedTime.joined α β hκ h2κR hR hr p T h F B η hη hρr oldGood hT 0).homology q =
    ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT false).post
      (push (retained α β R r hR hr F B))).homology q :=
  (existing_to_sequential α β R r η hκ h2κR hκR hη hR hr h hρr p T F B goodΓ oldGood hT q).trans
    (OriginalFirstHalfSequentialTimeComparison.retained_join_cup α β R r hR hr h p T hκ F B η hη hκR hρr goodΓ good hT q)

variable
  (goodχ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + (m + p))
    (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ))
  (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
      (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)))

include goodΓ goodχ goodδ in
theorem existing_to_cut_cup (q : ℕ) :
    (FirstInputRotationJoinedTime.joined α β hκ h2κR hR hr p T h F B η hη hρr oldGood hT 0).homology q =
    ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT true).post
      (push (retained α β R r hR hr F B))).homology q := by
  rw [existing_to_join_cup α β R r η hκ h2κR hκR hη hR hr h hρr p T F B goodΓ oldGood hT good q]
  simp only [DegreeLoweringHomology.Map.post_homology]
  rw [OriginalFirstHalfCupOrderTimeHomology.homology_eq α β R r hR hr h p T hκ hκR F B η hη hρr good hT goodχ goodδ q]

include goodΓ good goodχ goodδ in
theorem corrected_to_cut_cup (q : ℕ) :
    (FirstInputRotationJoinedTime.joined α β hκ h2κR hR hr p T h F B η hη hρr oldGood hT 1).homology q =
    ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F B η hη hρr good hT true).post
      (push (retained α β R r hR hr F B))).homology q :=
  (FirstInputRotationJoinedTime.homology_eq α β hκ h2κR hR hr p T h F B η hη hρr oldGood hT q).symm.trans
    (existing_to_cut_cup α β R r η hκ h2κR hκR hη hR hr h hρr p T F B goodΓ oldGood hT good goodχ goodδ q)

end
end Finsler.OriginalFirstHalfActualJoinCupConnection
