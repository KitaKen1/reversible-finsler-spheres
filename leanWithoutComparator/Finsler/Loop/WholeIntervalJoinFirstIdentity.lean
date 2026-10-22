module

public import Finsler.Loop.WholeIntervalNativeCap
public import Finsler.Loop.TimeCapCompositionAlignment

/-! Identify the genuine join-first native time operation on spatially
small input chains with the whole-interval coarse capped time prism.
All degree transports and the actual native retraction are retained. -/

@[expose] public section
namespace Finsler.WholeIntervalJoinFirstIdentity

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_prism {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (P : ∀ q, C.X q ⟶ D.X (q + 1)) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ P j = P i ≫ eqToHom (congrArg D.X (congrArg (fun k => k + 1) h)) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R η κ : ℝ)
  (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hη : 0 < η)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X ((m + 1) + (p + q)) ⟶ E.X q)
  (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)

theorem coarse_aligned (q : ℕ) :
    DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
      (WholeIntervalNativeCap.coarse α β R η κ (by omega) hκ hκR hη E p c hc) (by omega) q =
      eqToHom (congrArg
        (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).X
        (show ((m + 1) + (m + p)) + q + 1 = (m + 1) + ((m + p) + q + 1) by omega)) ≫
          (WholeIntervalLocalizedJoinCap.native α β R κ (by omega) hκ hκR).component ((m + p) + q + 1) ≫
            ClosedCapDegreeTransport.align m p
              (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
                (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
                (FullSecondHalfAnnularInputs.faceCover_open _ η)
                (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) E m p c) q := by
  let Rt := smallSingularRetraction (X := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) coeff
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
    (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη)
  have he := TimeCapCompositionAlignment.compose_aligned
    (WholeIntervalNativeCap.first α β R η κ (by omega) hκ hκR hη)
    (NestedCapHomology.operation (m + 1) p c hc)
    ((m + 1) + (m + p)) (m + p) (by omega) (by omega) q
  dsimp only [WholeIntervalNativeCap.first, DegreeLoweringHomology.Map.post] at he
  rw [Category.assoc, ← DegreeLoweringSuccAlignment.pre (m + p)
    (NestedCapHomology.operation (m + 1) p c hc) (by omega) Rt q,
    TimeCapCompositionAlignment.nested_pre_aligned] at he
  exact he

theorem prism_cap_transport (q : ℕ) :
    eqToHom (congrArg
      (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X
      (Nat.add_assoc (m + 1) (m + p) q)) ≫
        (CompactJoinCapLocalization.localized α β (by omega) hκ hκR).component ((m + p) + q) ≫
          AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) =
      WholeIntervalJoinCover.prism α β κ (((m + 1) + (m + p)) + q) ≫
        eqToHom (congrArg
          (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).X
          (show ((m + 1) + (m + p)) + q + 1 = (m + 1) + ((m + p) + q + 1) by omega)) ≫
            (WholeIntervalLocalizedJoinCap.native α β R κ (by omega) hκ hκR).component ((m + p) + q + 1) := by
  have hp := WholeIntervalLocalizedJoinCap.prism_cap α β R κ (by omega) hκ hκR ((m + p) + q)
  have ht := transport_prism (WholeIntervalJoinCover.prism α β κ)
    (((m + 1) + (m + p)) + q) ((m + 1) + ((m + p) + q)) (Nat.add_assoc (m + 1) (m + p) q)
  have hh := congrArg (fun z => eqToHom (congrArg
    (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X
      (Nat.add_assoc (m + 1) (m + p) q)) ≫ z) hp.symm
  calc
    _ = (eqToHom (congrArg
        (small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).X
          (Nat.add_assoc (m + 1) (m + p) q)) ≫
        WholeIntervalJoinCover.prism α β κ ((m + 1) + ((m + p) + q))) ≫
          eqToHom (congrArg
            (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).X
            (show (m + 1) + ((m + p) + q) + 1 = (m + 1) + (((m + p) + q) + 1) by omega)) ≫
              (WholeIntervalLocalizedJoinCap.native α β R κ (by omega) hκ hκR).component ((m + p) + q + 1) := by
      simpa only [Category.assoc] using hh
    _ = _ := by
      rw [ht]
      simp only [Category.assoc, eqToHom_trans_assoc]

variable (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) E (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) E m p c) q)

def joined : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q))) E ((m + 1) + (m + p)) :=
  DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) w

include hw in
theorem on_small (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (((m + 1) + (m + p)) + q) ≫
      (joined α β R κ hκ hκR E p w).component q =
        WholeIntervalJoinCover.prism α β κ (((m + 1) + (m + p)) + q) ≫
          DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
            (WholeIntervalNativeCap.coarse α β R η κ (by omega) hκ hκR hη E p c hc) (by omega) q := by
  dsimp only [joined]
  rw [DegreeLoweringComposition.component, ← Category.assoc,
    ← transport_f (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ))
      (((m + 1) + (m + p)) + q) ((m + 1) + ((m + p) + q)) (Nat.add_assoc (m + 1) (m + p) q)]
  simp only [Category.assoc]
  rw [← Category.assoc
      ((inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f ((m + 1) + ((m + p) + q)))
      ((CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR).component ((m + p) + q)) (w.component q),
    CompactJoinCapLocalization.unrefined_small, hw q, coarse_aligned]
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) E m p c) q)
    (prism_cap_transport α β R κ hκ hκR p q)

end
end Finsler.WholeIntervalJoinFirstIdentity
