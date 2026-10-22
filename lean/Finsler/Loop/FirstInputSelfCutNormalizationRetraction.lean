module

public import Finsler.Loop.FirstInputSelfCutNormalizationCap
public import Finsler.Loop.CapCochainBoundaryPre
public import Finsler.Loop.SingleCapSourceCollar

/-! Refine and retract the actual single-input primitive cap through
the same metric first cover used by the actual time factorization.
Both primitive endpoint terms vanish in the proper small target. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutNormalizationRetraction

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open Finsler.FirstInputSelfCutNormalizationCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (σ : ℝ) (hσ : 0 < σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))

def subdivision :=
  TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ) ≫
  FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst

def refinedPrimitive (q : ℕ) :=
  (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f ((m + p) + q) ≫
    primitiveCap α r hr κ h p T q

def retractedPrimitive (q : ℕ) :=
  (subdivision α r hr κ σ hσ firstIndex hfirst).f ((m + p) + q) ≫ primitiveCap α r hr κ h p T q

def retractedBoundary (q : ℕ) :=
  (subdivision α r hr κ σ hσ firstIndex hfirst).f (((m + p) + 1) + q) ≫ boundaryCap α r hr κ h p T hT q

theorem refined_source (q : ℕ) :
    refinedPrimitive α r hr κ h p T σ firstIndex hfirst q ≫ (FirstInputSelfCutTime.sourceMap α r hr κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((m + p) + q) ≫
      absoluteChain (ambient α) (m + p) q ((m + p) + q) rfl (primitive α r hr h p T) := by
  dsimp only [refinedPrimitive]
  rw [Category.assoc, primitive_source, ← Category.assoc]
  have hi := congrArg (fun f => f.f ((m + p) + q))
    (SmallRefinementComparison.refinement_inclusion (X := ambient α)
      (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
  simp only [HomologicalComplex.comp_f] at hi
  rw [FirstInputSelfCutBoundedFactorization.firstMap, hi]

theorem retracted_boundary (q : ℕ) :
    retractedPrimitive α r hr κ h p T σ hσ firstIndex hfirst (q + 1) ≫
      (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).d (q + 1) q =
    (chains (ambient α)).d ((m + p) + (q + 1)) ((m + p) + q) ≫
      retractedPrimitive α r hr κ h p T σ hσ firstIndex hfirst q -
    eqToHom (congrArg (chains (ambient α)).X
      (show (m + p) + (q + 1) = ((m + p) + 1) + q by omega)) ≫
      retractedBoundary α r hr κ h p T hT σ hσ firstIndex hfirst q :=
  CapCochainBoundaryPre.pre (subdivision α r hr κ σ hσ firstIndex hfirst) (m + p)
    (primitiveCap α r hr κ h p T) (boundaryCap α r hr κ h p T hT)
    (boundary α r hr κ h p T hT) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q) ≫
      retractedPrimitive α r hr κ h p T σ hσ firstIndex hfirst q = 0 := by
  change (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q) ≫
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f ((m + p) + q) ≫
    refinedPrimitive α r hr κ h p T σ firstIndex hfirst q = 0
  apply SingleCapSourceCollar.lift_zero (OriginalFirstHalfFactorwiseCover.first σ) (inner α δ) (m + p)
    (primitive α r hr h p T) (primitive_inner_zero α r hr h p T) (AnnularTimeTrim.slice (TopCat.of P) t) _
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ))
    (FirstInputSelfCutTime.sourceMap α r hr κ) (FirstInputSelfCutTime.sourceMap_mono α r hr κ)
    (refinedPrimitive α r hr κ h p T σ firstIndex hfirst)
    (refined_source α r hr κ h p T σ firstIndex hfirst) q
  intro x
  rcases ht with rfl | rfl
  · exact (UniformSelfCutCollar.distance_zero α x).le.trans h.1.le
  · exact (UniformSelfCutCollar.distance_one α x).le.trans h.1.le

theorem boundary_normal (q : ℕ) :
    retractedBoundary α r hr κ h p T hT σ hσ firstIndex hfirst q =
    eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + 1) + q = ((m + 1) + p) + q by omega)) ≫
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + 1) + p) + q) ≫
    (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f (((m + 1) + p) + q) ≫
    ((FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component q -
      (FirstInputSelfCutOperations.rawOperation α r hr κ h p T hT).component q) := by
  dsimp only [retractedBoundary, boundaryCap]
  rw [← Category.assoc, ← LocalizedCapCupComponentSource.transport_f
    (subdivision α r hr κ σ hσ firstIndex hfirst) (((m + p) + 1) + q) (((m + 1) + p) + q) (by omega)]
  simp only [subdivision, HomologicalComplex.comp_f, Category.assoc]

end
end Finsler.FirstInputSelfCutNormalizationRetraction
