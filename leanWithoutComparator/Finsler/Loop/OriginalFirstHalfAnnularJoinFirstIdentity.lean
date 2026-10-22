module

public import Finsler.Loop.OriginalFirstHalfAnnularCoarseCap

/-! On actual spatially small inputs, the real spatial join cap
followed by gamma time is exactly the coarse capped annular prism. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularJoinFirstIdentity

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_prism {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (P : ∀ q, C.X q ⟶ D.X (q + 1)) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ P j = P i ≫ eqToHom (congrArg D.X (congrArg (fun k => k + 1) h)) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ)
  {κ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (p : ℕ)

theorem prism_cap_transport (q : ℕ) :
    eqToHom (congrArg (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X
      (Nat.add_assoc (m + 1) (m + p) q)) ≫
      (CompactJoinCapLocalization.localized α β (by omega) hκ hκR).component ((m + p) + q) ≫
        AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) =
    OriginalFirstHalfAnnularJoinCover.prism α β κ (((m + 1) + (m + p)) + q) ≫
      eqToHom (congrArg (small (ambient α β) (OriginalFirstHalfAnnularJoinCover.cover α β κ)).X
        (show ((m + 1) + (m + p)) + q + 1 = (m + 1) + ((m + p) + q + 1) by omega)) ≫
        (OriginalFirstHalfAnnularJoinCap.native α β R hκ hκR).component ((m + p) + q + 1) := by
  have hp := OriginalFirstHalfAnnularJoinCap.prism_cap α β R hκ hκR ((m + p) + q)
  have ht := transport_prism (OriginalFirstHalfAnnularJoinCover.prism α β κ)
    (((m + 1) + (m + p)) + q) ((m + 1) + ((m + p) + q)) (Nat.add_assoc (m + 1) (m + p) q)
  have hh := congrArg (fun k => eqToHom (congrArg
    (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X
      (Nat.add_assoc (m + 1) (m + p) q)) ≫ k) hp.symm
  calc
    _ = (eqToHom (congrArg (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X
        (Nat.add_assoc (m + 1) (m + p) q)) ≫
          OriginalFirstHalfAnnularJoinCover.prism α β κ ((m + 1) + ((m + p) + q))) ≫
        eqToHom (congrArg (small (ambient α β) (OriginalFirstHalfAnnularJoinCover.cover α β κ)).X
          (show (m + 1) + ((m + p) + q) + 1 = (m + 1) + (((m + p) + q) + 1) by omega)) ≫
          (OriginalFirstHalfAnnularJoinCap.native α β R hκ hκR).component ((m + p) + q + 1) := by
      simpa only [Category.assoc] using hh
    _ = _ := by
      rw [ht]
      simp only [Category.assoc, eqToHom_trans_assoc]

variable (r η : ℝ) (hη : 0 < η) (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def joined := DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR)
  (OriginalFirstHalfZeroGammaTime.operation α β R r hR hr h p T F B η hη hρr goodΓ hT)

theorem on_small (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (((m + 1) + (m + p)) + q) ≫
      (joined α β R hκ hκR p r η hη hR hr h hρr T F B goodΓ hT).component q =
    OriginalFirstHalfAnnularJoinCover.prism α β κ (((m + 1) + (m + p)) + q) ≫
      SingleCapTimeRefinement.aligned ((m + 1) + (m + p))
        (OriginalFirstHalfAnnularCoarseCap.coarse α β R r η hκ hκR hη hρr hR hr h p T F B goodΓ hT) q := by
  dsimp only [joined]
  rw [DegreeLoweringComposition.component, ← Category.assoc,
    ← transport_f (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ))
      (((m + 1) + (m + p)) + q) ((m + 1) + ((m + p) + q)) (Nat.add_assoc (m + 1) (m + p) q)]
  simp only [Category.assoc]
  rw [← Category.assoc
      ((inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f ((m + 1) + ((m + p) + q)))
      ((CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR).component ((m + p) + q))
      ((OriginalFirstHalfZeroGammaTime.operation α β R r hR hr h p T F B η hη hρr goodΓ hT).component q),
    CompactJoinCapLocalization.unrefined_small, OriginalFirstHalfZeroGammaTime.component_normal,
    OriginalFirstHalfAnnularCoarseCap.coarse_aligned]
  simpa only [Category.assoc] using congrArg (fun k => k ≫ ClosedCapDegreeTransport.align m p
    (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
      (OriginalFirstHalfZeroCover.cover α β R r η ρ) (OriginalFirstHalfZeroCover.cover_open α β R r η ρ)
      (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr)
      (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) m p
      (OriginalFirstHalfZeroGammaTime.component α β R r hR hr h p T F B η goodΓ hT)) q)
    (prism_cap_transport α β R hκ hκR p q)

end
end Finsler.OriginalFirstHalfAnnularJoinFirstIdentity
