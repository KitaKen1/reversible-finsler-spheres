module

public import Finsler.Loop.OriginalFirstHalfAnnularCommonCover
public import Finsler.Loop.OriginalFirstHalfZeroGammaTime
public import Finsler.Loop.OriginalFirstHalfSequentialJoinGamma
public import Finsler.Loop.DegreeLoweringRefinedComposition
public import Finsler.Loop.UnpackedTimeCapAlignment
public import Finsler.Loop.SingleCapTimeRefinement

/-! The real coarse whole-interval first cap followed by the actual
gamma retraction/cap. On a common cover it is exactly the established
sequential cap, and its time alignment retains the actual retraction. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularCoarseCap

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfAnnularCommonCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η : ℝ)
  {κ ρ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hη : 0 < η) (hρr : ρ < r)

def first := (OriginalFirstHalfAnnularJoinCap.native α β R hκ hκR).post
  (smallSingularRetraction (X := OriginalFirstHalfZeroCover.space α β R) coeff
    (OriginalFirstHalfZeroCover.cover α β R r η ρ) (OriginalFirstHalfZeroCover.cover_open α β R r η ρ)
    (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr))

theorem first_on_common (q : ℕ) :
    (toCoarse α β R r η κ ρ).f ((m + 1) + q) ≫
      (first α β R r η hκ hκR hη hρr).component q =
    (toSequential α β R r η κ ρ).f ((m + 1) + q) ≫
      (OriginalFirstHalfLocalizedJoinCap.operation α β R r η ρ hκ).component q := by
  let Y := OriginalFirstHalfZeroCover.space α β R
  let U := OriginalFirstHalfZeroCover.cover α β R r η ρ
  let Rt := smallSingularRetraction (X := Y) coeff U
    (OriginalFirstHalfZeroCover.cover_open α β R r η ρ) (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr)
  have hs : inclusion Y U ≫ Rt = 𝟙 _ := ι_comp_smallSingularRetraction (X := Y) coeff U
    (OriginalFirstHalfZeroCover.cover_open α β R r η ρ) (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr)
  change (toCoarse α β R r η κ ρ).f ((m + 1) + q) ≫
    ((OriginalFirstHalfAnnularJoinCap.native α β R hκ hκR).component q ≫ Rt.f q) = _
  rw [← Category.assoc, first_cap_source α β R r η κ ρ hκ hκR q]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, hs, HomologicalComplex.id_f, Category.comp_id]

variable (hR : R ≤ 1 / 2) (hr : r < 1) {δ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (F : ReversibleMetric (m + 1)) (B : ℝ)
  (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def coarse := DegreeLoweringRegrade.regrade
  (DegreeLoweringComposition.compose (first α β R r η hκ hκR hη hρr)
    (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η goodΓ hT))
  (((m + 1) + (m + p)) + 1) (by omega)

theorem coarse_on_common (q : ℕ) :
    (toCoarse α β R r η κ ρ).f ((((m + 1) + (m + p)) + 1) + q) ≫
      (coarse α β R r η hκ hκR hη hρr hR hr h p T F B goodΓ hT).component q =
    (toSequential α β R r η κ ρ).f ((((m + 1) + (m + p)) + 1) + q) ≫
      (OriginalFirstHalfSequentialJoinGamma.operation α β R r η hR hr h p T hκ F B goodΓ hT).component q :=
  DegreeLoweringRefinedComposition.regraded_component_eq (toCoarse α β R r η κ ρ)
    (toSequential α β R r η κ ρ) (first α β R r η hκ hκR hη hρr)
    (OriginalFirstHalfLocalizedJoinCap.operation α β R r η ρ hκ)
    (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η goodΓ hT)
    (first_on_common α β R r η hκ hκR hη hρr) (((m + 1) + (m + p)) + 1) (by omega) q

theorem coarse_aligned (q : ℕ) :
    SingleCapTimeRefinement.aligned ((m + 1) + (m + p))
      (coarse α β R r η hκ hκR hη hρr hR hr h p T F B goodΓ hT) q =
    eqToHom (congrArg (small (ambient α β) (OriginalFirstHalfAnnularJoinCover.cover α β κ)).X
      (show ((m + 1) + (m + p)) + q + 1 = (m + 1) + ((m + p) + q + 1) by omega)) ≫
      (OriginalFirstHalfAnnularJoinCap.native α β R hκ hκR).component ((m + p) + q + 1) ≫
        ClosedCapDegreeTransport.align m p
          (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
            (OriginalFirstHalfZeroCover.cover α β R r η ρ) (OriginalFirstHalfZeroCover.cover_open α β R r η ρ)
            (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr)
            (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) m p
            (OriginalFirstHalfZeroGammaTime.component α β R r hR hr h p T F B η goodΓ hT)) q := by
  let Rt := smallSingularRetraction (X := OriginalFirstHalfZeroCover.space α β R) coeff
    (OriginalFirstHalfZeroCover.cover α β R r η ρ) (OriginalFirstHalfZeroCover.cover_open α β R r η ρ)
    (OriginalFirstHalfZeroCover.cover_univ α β R r hη hρr)
  have he := TimeCapCompositionAlignment.compose_aligned (first α β R r η hκ hκR hη hρr)
    (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η goodΓ hT)
    ((m + 1) + (m + p)) (m + p) (by omega) (by omega) q
  dsimp only [first, DegreeLoweringHomology.Map.post] at he
  rw [Category.assoc, ← DegreeLoweringSuccAlignment.pre (m + p)
    (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η goodΓ hT) (by omega) Rt q,
    UnpackedTimeCapAlignment.aligned] at he
  calc
    _ = DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
        (DegreeLoweringComposition.compose (first α β R r η hκ hκR hη hρr)
          (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η goodΓ hT)) (by omega) q := by
      rw [SingleCapTimeRefinement.aligned_normal]
      dsimp only [coarse, DegreeLoweringRegrade.regrade, DegreeLoweringSuccAlignment.align]
      simp only [← Category.assoc, eqToHom_trans]
    _ = _ := he

end
end Finsler.OriginalFirstHalfAnnularCoarseCap
