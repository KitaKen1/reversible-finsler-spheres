module

public import Finsler.Loop.JoinTimeInputRefinement

/-! Compare the actual join-first map with a closed full-time map whose
cap is the genuine common-cover cap. The actual relative double prism
remains in the identical output complex. Both endpoints factor through
the fine cover, and the input refinement is removed on homology. -/

@[expose] public section
namespace Finsler.WholeIntervalRelativeHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem map_ext {C E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (f g : DegreeLoweringHomology.Map C E d) (h : ∀ q, f.component q = g.component q) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      cases he
      rfl

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R η σ κ : ℝ)
  (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hη : 0 < η) (hσ : 0 < σ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X ((m + 1) + (p + q)) ⟶ E.X q)
  (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)

theorem fine_aligned (q : ℕ) :
    DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
      (NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ E p c hc) (by omega) q =
      (WholeIntervalJoinCover.refinement α β κ R η σ).f (((m + 1) + (m + p)) + q + 1) ≫
        DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
          (WholeIntervalNativeCap.coarse α β R η κ (by omega) hκ hκR hη E p c hc) (by omega) q := by
  have he : NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ E p c hc =
      (WholeIntervalNativeCap.coarse α β R η κ (by omega) hκ hκR hη E p c hc).pre
        (WholeIntervalJoinCover.refinement α β κ R η σ) := by
    apply map_ext
    intro t
    exact (WholeIntervalNativeCap.coarse_on_common α β R η κ (by omega) hκ hκR hη E p c hc σ t).symm
  rw [he, DegreeLoweringSuccAlignment.pre]

variable (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) E (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη) E m p c) q)

include hw in
theorem input_component (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (JoinTimeInputRefinement.cover α β R η σ κ)).f (((m + 1) + (m + p)) + q) ≫
      (WholeIntervalJoinFirstIdentity.joined α β R κ hκ hκR E p w).component q =
        (inclusion (TopCat.of (P × Q)) (JoinTimeInputRefinement.cover α β R η σ κ)).f (((m + 1) + (m + p)) + q) ≫
          (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom
            (((m + 1) + (m + p)) + q) (((m + 1) + (m + p)) + q + 1) ≫
          (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
            (WholeIntervalJoinCover.cover α β κ) (WholeIntervalJoinCover.cover_open α β κ)
            (WholeIntervalJoinCover.cover_univ α β κ hκ)).f (((m + 1) + (m + p)) + q + 1) ≫
          DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
            (WholeIntervalNativeCap.coarse α β R η κ (by omega) hκ hκR hη E p c hc) (by omega) q := by
  let V := WholeIntervalJoinCover.cover α β κ
  let Rt := smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff V
    (WholeIntervalJoinCover.cover_open α β κ) (WholeIntervalJoinCover.cover_univ α β κ hκ)
  have hs : inclusion (TopCat.of (P × (ClosedInterval × Q))) V ≫ Rt = 𝟙 _ :=
    ι_comp_smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff V (WholeIntervalJoinCover.cover_open α β κ)
      (WholeIntervalJoinCover.cover_univ α β κ hκ)
  have hp (i : ℕ) : WholeIntervalJoinCover.prism α β κ i =
      (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f i ≫
        (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom i (i + 1) ≫ Rt.f (i + 1) := by
    have ht := congrArg (fun f => f ≫ Rt.f (i + 1)) (WholeIntervalJoinCover.prism_inclusion α β κ i)
    simp only [Category.assoc] at ht
    rw [← HomologicalComplex.comp_f, hs, HomologicalComplex.id_f, Category.comp_id] at ht
    exact ht.symm
  calc
    _ = (JoinTimeInputRefinement.spatial α β R η σ κ).f (((m + 1) + (m + p)) + q) ≫
        ((inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (((m + 1) + (m + p)) + q) ≫
          (WholeIntervalJoinFirstIdentity.joined α β R κ hκ hκR E p w).component q) := by
      rw [← Category.assoc, ← HomologicalComplex.comp_f, JoinTimeInputRefinement.spatial_inclusion]
    _ = _ := by
      rw [WholeIntervalJoinFirstIdentity.on_small α β R η κ hκ hκR hη E p c hc w hw q, hp]
      simp only [Rt, V, ← Category.assoc, ← HomologicalComplex.comp_f, JoinTimeInputRefinement.spatial_inclusion]

variable (b : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q))) E ((m + 1) + (m + p)))
  (hb : ∀ q, b.component q =
    (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom
      (((m + 1) + (m + p)) + q) (((m + 1) + (m + p)) + q + 1) ≫
    (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
      (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
      (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ (by linarith))).f
        (((m + 1) + (m + p)) + q + 1) ≫
    DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
      (NativeCommonTripleCap.operation α β R η σ κ (by omega) hκ E p c hc) (by omega) q)

include hw hb in
theorem homology_eq (q : ℕ) :
    (WholeIntervalJoinFirstIdentity.joined α β R κ hκ hκR E p w).homology q = b.homology q := by
  let X : TopCat.{0} := TopCat.of (P × Q)
  let Z : TopCat.{0} := TopCat.of (P × (ClosedInterval × Q))
  let S := JoinTimeInputRefinement.cover α β R η σ κ
  let U : JoinTimeInputRefinement.FineIndex α β R → Set Z := OriginalNativeCommonCover.cover α β R η σ κ
  let V : (P × Q) → Set Z := WholeIntervalJoinCover.cover α β κ
  let j := inclusion X S
  let H := (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).compLeft j
  let rindex : JoinTimeInputRefinement.FineIndex α β R → P × Q := fun i => (i.2.1, i.2.2.2)
  have href : ∀ i, U i ⊆ V (rindex i) := fun _ _ hz => ⟨hz.2.1.2, hz.2.2.2⟩
  let J := SmallRefinementComparison.comparison (X := Z) U V rindex href
    (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ (by linarith))
    (WholeIntervalJoinCover.cover_open α β κ) (WholeIntervalJoinCover.cover_univ α β κ hκ)
  let u := DegreeLoweringSuccAlignment.align ((m + 1) + (m + p))
    (WholeIntervalNativeCap.coarse α β R η κ (by omega) hκ hκR hη E p c hc) (by omega)
  have hz₀ (t : ℕ) : (j ≫ push (OriginalSecondHalfEndpointZero.face 0)).f (((m + 1) + (m + p)) + t) ≫
      (J.hom (((m + 1) + (m + p)) + t) (((m + 1) + (m + p)) + t + 1) ≫ u t) = 0 := by
    rw [← JoinTimeInputRefinement.zero_inclusion α β R η σ κ, HomologicalComplex.comp_f,
      Category.assoc, ← Category.assoc ((inclusion Z U).f (((m + 1) + (m + p)) + t)),
      TimeCoverRefinementComparison.small_zero, zero_comp, comp_zero]
  have hz₁ (t : ℕ) : (j ≫ push (OriginalSecondHalfEndpointZero.face 1)).f (((m + 1) + (m + p)) + t) ≫
      (J.hom (((m + 1) + (m + p)) + t) (((m + 1) + (m + p)) + t + 1) ≫ u t) = 0 := by
    rw [← JoinTimeInputRefinement.one_inclusion α β R η σ κ, HomologicalComplex.comp_f,
      Category.assoc, ← Category.assoc ((inclusion Z U).f (((m + 1) + (m + p)) + t)),
      TimeCoverRefinementComparison.small_zero, zero_comp, comp_zero]
  apply SmallInclusionHomologyCancellation.homology_eq X S
    (JoinTimeInputRefinement.cover_open α β R η σ κ)
    (JoinTimeInputRefinement.cover_univ α β R η σ κ hη hσ hκ (by linarith)) E ((m + 1) + (m + p))
    (WholeIntervalJoinFirstIdentity.joined α β R κ hκ hκR E p w) b q
  apply TimeCylinderComparison.homology_eq H J ((m + 1) + (m + p)) u
    (DegreeLoweringSuccAlignment.comm _ _ _) hz₀ hz₁
    ((WholeIntervalJoinFirstIdentity.joined α β R κ hκ hκR E p w).pre j) (b.pre j)
  · intro t
    simpa only [DegreeLoweringHomology.Map.pre, H, Homotopy.compLeft_hom, Category.assoc] using
      input_component α β R η σ κ hκ hκR hη E p c hc w hw t
  · intro t
    dsimp only [DegreeLoweringHomology.Map.pre]
    rw [hb t, fine_aligned α β R η σ κ hκ hκR hη E p c hc]
    simp only [H, U, V, rindex, u, Homotopy.compLeft_hom, HomologicalComplex.comp_f, WholeIntervalJoinCover.refinement,
      Category.assoc]

end
end Finsler.WholeIntervalRelativeHomology
