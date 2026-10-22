module

public import Finsler.Loop.NativeMovingNonnorthGeometry

/-! The ORIGINAL pre-time cut cochain vanishes on all nine nonnorth
moving segments. This kills all 27 corresponding terms in the old
global coefficient. The only retained pieces per rotation quarter
are 0,4,8,12; no same-leg or source-permutation conclusion is hidden. -/
@[expose] public section
namespace Finsler.NativeMovingNonnorthZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingTriangleSupport Finsler.NativeMovingNonnorthGeometry Finsler.NativeMovingThirteen
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem parameter_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k i q : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hηr : η + r ≤ 3 / 5) :
    cochainPullback (segmentFamily P v₀ k (nonnorthSegment i q)) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) = 0 := by
  have hf (z : NativeGlobalTimeSquare.rotationDomain P ⊗ TopCat.I) :
      segmentFamily P v₀ k (nonnorthSegment i q) z ∈
        LocalizedParameterCutCochain.farCarrier (m + 1) (NorthMeridianEvaluationPoint.target P v₀) (3 / 5) :=
    Or.inr (NorthMeridianEvaluationPoint.excluded_distance P v₀
      ⟨_, nonnorth_excluded P v₀ k i q z⟩)
  have hz := LocalizedParameterCutCochain.family_zero m m (NorthMeridianEvaluationPoint.target P v₀)
    hρ hρr hr hη hηr (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))
    (segmentFamily P v₀ k (nonnorthSegment i q)) hf
  rw [GlobalCutTimePrismAlignment.parameterCochain, NativeMovingTriangleSupport.pullback_pre,
    hz, CochainDegreeTransport.pre, comp_zero]

theorem segment_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k i q : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hηr : η + r ≤ 3 / 5) :
    segmentEvaluation m P v₀ k (nonnorthSegment i q) hρ hρr hr hη = 0 := by
  have hz := parameter_zero m P v₀ k i q hρ hρr hr hη hηr
  change NativeMovingTimeSplit.rotationInput P (3 * m) ≫
    (UniversalTimeTriangleChain.interval (NativeGlobalTimeSquare.rotationDomain P) (3 * m + 1) ≫
      cochainPullback (segmentFamily P v₀ k (nonnorthSegment i q)) (3 * m + 2)
        (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)) = 0
  rw [hz, comp_zero, comp_zero]

theorem missing_index (j : Fin 13) (hj : j ∉ ({0, 4, 8, 12} : Finset (Fin 13))) :
    ∃ i q : Fin 3, nonnorthSegment i q = j := by
  fin_cases j <;> first | exact False.elim (hj (by decide)) | decide

theorem omitted_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (j : Fin 13)
    (hj : j ∉ ({0, 4, 8, 12} : Finset (Fin 13))) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hηr : η + r ≤ 3 / 5) :
    segmentEvaluation m P v₀ k j hρ hρr hr hη = 0 := by
  obtain ⟨i, q, rfl⟩ := missing_index j hj
  exact segment_zero m P v₀ k i q hρ hρr hr hη hηr

theorem sum_four (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hηr : η + r ≤ 3 / 5) :
    (∑ j : Fin 13, segmentEvaluation m P v₀ k j hρ hρr hr hη) =
      segmentEvaluation m P v₀ k 0 hρ hρr hr hη + segmentEvaluation m P v₀ k 4 hρ hρr hr hη +
      segmentEvaluation m P v₀ k 8 hρ hρr hr hη + segmentEvaluation m P v₀ k 12 hρ hρr hr hη := by
  classical
  have hs : (∑ j ∈ ({0, 4, 8, 12} : Finset (Fin 13)), segmentEvaluation m P v₀ k j hρ hρr hr hη) =
      ∑ j : Fin 13, segmentEvaluation m P v₀ k j hρ hρr hr hη :=
    Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => omitted_zero m P v₀ k j hj hρ hρr hr hη hηr)
  rw [← hs]
  norm_num [Finset.sum_insert, Finset.sum_singleton, add_assoc]

theorem north_four (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hηr : η + r ≤ 3 / 5) :
    (chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalDoublePrismCoefficient.cochain m P v₀ k hρ hρr hr hη =
      segmentEvaluation m P v₀ k 0 hρ hρr hr hη + segmentEvaluation m P v₀ k 4 hρ hρr hr hη +
      segmentEvaluation m P v₀ k 8 hρ hρr hr hη + segmentEvaluation m P v₀ k 12 hρ hρr hr hη :=
  (north_thirteen m P v₀ k hρ hρr hr hη hη2).trans (sum_four m P v₀ k hρ hρr hr hη hηr)

theorem coefficient_twelve (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hηr : η + r ≤ 3 / 5) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ = ∑ k : Fin 3,
      ((segmentEvaluation m P v₀ k 0 hρ hρr hr hη).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) +
       (segmentEvaluation m P v₀ k 4 hρ hρr hr hη).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) +
       (segmentEvaluation m P v₀ k 8 hρ hρr hr hη).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) +
       (segmentEvaluation m P v₀ k 12 hρ hρr hr hη).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)) := by
  rw [NativeGlobalDoublePrismCoefficient.original_coefficient_raw m hm P v₀ hρ hρr hr hη hη2]
  simp_rw [north_four m P v₀ _ hρ hρr hr hη hη2 hηr]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_add, LinearMap.add_apply]

end
end Finsler.NativeMovingNonnorthZero
