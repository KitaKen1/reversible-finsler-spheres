module

public import Finsler.Loop.FirstFactorFullMappedTimeComparison
public import Finsler.Loop.OriginalFirstHalfNormalizedTensorTime
public import Finsler.Loop.OriginalFirstHalfFactorwiseCover
public import Finsler.Loop.SingleCapTimeRefinement

/-! Apply both genuine refinement comparisons to the real normalized
original cut-first cup. The resulting all-input operation uses actual
factorwise cylinder subdivisions in the identical bounded target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfFactorwiseNormalizedTime

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut Finsler.OriginalFirstHalfCupOneCochains
open Finsler.OriginalFirstHalfJointSupportedCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {κ : ℝ} (hκ : 0 < κ) (hκR : κ < R) (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (hη : 0 < η) (hρr : ρ < r)
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def smallCap (q : ℕ) :=
  SingleCapTimeRefinement.aligned ((m + 1) + (m + p))
    (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT) q

theorem smallCap_comm (q : ℕ) :
    smallCap α β R r hR hr h p T hκ F B η goodN hT (q + 1) ≫
      (chains (TopCat.of (bounded α β R r hR hr F B))).d (q + 1) q =
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).d
      (((m + 1) + (m + p)) + q + 2) (((m + 1) + (m + p)) + q + 1) ≫
      smallCap α β R r hR hr h p T hκ F B η goodN hT q :=
  SingleCapTimeRefinement.aligned_comm _ _ q

theorem smallCap_source (q : ℕ) :
    smallCap α β R r hR hr h p T hκ F B η goodN hT q ≫
      (push (source α β R r hR hr F B)).f q =
    eqToHom (congrArg (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X
      (show ((m + 1) + (m + p)) + q + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫
    (inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).f
      ((((m + 1) + (m + p)) + 1) + q) ≫
    absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
      ((((m + 1) + (m + p)) + 1) + q) rfl
      (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) := by
  rw [smallCap, SingleCapTimeRefinement.aligned_normal, Category.assoc]
  exact congrArg (fun k => eqToHom (congrArg
    (small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)).X
    (show ((m + 1) + (m + p)) + q + 1 = (((m + 1) + (m + p)) + 1) + q by omega)) ≫ k)
    (OriginalFirstHalfNormalizationBounded.normalizedCap_source α β R r hR hr h p T hκ F B η goodN q)

theorem retracted_cap (q : ℕ) :
    (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)).f
        (((m + 1) + (m + p)) + q + 1) ≫ smallCap α β R r hR hr h p T hκ F B η goodN hT q =
    OriginalFirstHalfNormalizedTensorTime.cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q := by
  exact SingleCapTimeRefinement.aligned_refinement ((m + 1) + (m + p))
    (SingleCapTimePrism.retracted (TopCat.of (P × Q)) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
      (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p))
      (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT))
    (OriginalFirstHalfNormalizationBounded.normalizedOperation α β R r hR hr h p T hκ F B η goodN hT)
    (TauCeti.smallSingularRetraction (X := ambient α β) coeff (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)) (fun _ => rfl) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t) ⊗ₘ 𝟙 (chains (TopCat.of Q))).f
      (((m + 1) + (m + p)) + q + 1) ≫
    (FirstFactorMappedRectangles.coarse (X := TopCat.of P) (Y := TopCat.of Q) (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f
        (((m + 1) + (m + p)) + q + 1) ≫
    smallCap α β R r hR hr h p T hκ F B η goodN hT q = 0 := by
  simp only [FirstFactorMappedRectangles.coarse, HomologicalComplex.comp_f, Category.assoc,
    retracted_cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q]
  exact FirstFactorOriginalTimeComparison.tensor_endpoint_zero (TopCat.of P) (TopCat.of Q)
    ((m + 1) + (m + p))
    (OriginalFirstHalfNormalizedTensorTime.cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT)
    t (OriginalFirstHalfNormalizedTensorTime.endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT t ht) q

variable (σ : ℝ) (hσ : 0 < σ)
  (index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)))
  (hindex : ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
    (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × P)) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)))

def operation : DegreeLoweringHomology.Map (chains (TopCat.of P) ⊗ chains (TopCat.of Q))
    (chains (TopCat.of (bounded α β R r hR hr F B))) ((m + 1) + (m + p)) :=
  FirstFactorFullMappedTimeComparison.operation (X := TopCat.of P) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex ((m + 1) + (m + p))
    (smallCap α β R r hR hr h p T hκ F B η goodN hT)
    (smallCap_comm α β R r hR hr h p T hκ F B η goodN hT)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 0 (Or.inl rfl))
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 1 (Or.inr rfl))

theorem component_normal (q : ℕ) :
    (operation α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT σ hσ index hindex).component q =
    (TauCeti.smallSingularRetraction (X := TopCat.of P) coeff
      (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ))
      (CommonPrismRefinement.endpointCover_open (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ))
      (CommonPrismRefinement.endpointCover_univ (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_univ hσ)) ⊗ₘ
      TauCeti.smallSingularRetraction (X := TopCat.of Q) coeff (OriginalFirstHalfFactorwiseCover.other σ)
        (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)).f
      (((m + 1) + (m + p)) + q) ≫
    (FirstFactorTensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)).hom
      (((m + 1) + (m + p)) + q) (((m + 1) + (m + p)) + q + 1) ≫
    (FactorwiseSubdivisionComparison.factorwise (X := TopCat.of (ClosedInterval × P)) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
      (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)).f
      (((m + 1) + (m + p)) + q + 1) ≫
    (FirstFactorMappedRectangles.targetMap (X := TopCat.of P) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
      (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
      (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex).f
      (((m + 1) + (m + p)) + q + 1) ≫ smallCap α β R r hR hr h p T hκ F B η goodN hT q := by
  rfl

theorem homology_eq (q : ℕ) :
    (OriginalFirstHalfNormalizedTensorTime.tensorTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).homology q =
    (operation α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT σ hσ index hindex).homology q := by
  have hc := FirstFactorFullMappedTimeComparison.homology_eq (X := TopCat.of P) (Y := TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) index hindex ((m + 1) + (m + p))
    (smallCap α β R r hR hr h p T hκ F B η goodN hT)
    (smallCap_comm α β R r hR hr h p T hκ F B η goodN hT)
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 0 (Or.inl rfl))
    (endpoint_zero α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT 1 (Or.inr rfl)) q
  refine Eq.trans ?_ hc
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro q'
  rw [OriginalFirstHalfNormalizedTensorTime.component_normal]
  simp only [FirstFactorFullMappedTimeComparison.coarseOperation, TimePrismDescent.operation,
    TimePrismDescent.component, FirstFactorMappedTimeComparison.coarseCap,
    FirstFactorMappedRectangles.coarse, HomologicalComplex.comp_f, Category.assoc,
    retracted_cap α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT q']

theorem retained_homology_eq (q : ℕ) :
    ((OriginalFirstHalfNormalizedTensorTime.tensorTime α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT).post
      (push (retained α β R r hR hr F B))).homology q =
    ((operation α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT σ hσ index hindex).post
      (push (retained α β R r hR hr F B))).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    homology_eq α β R r hR hr h p T hκ hκR F B η hη hρr goodN hT σ hσ index hindex q]

end
end Finsler.OriginalFirstHalfFactorwiseNormalizedTime
