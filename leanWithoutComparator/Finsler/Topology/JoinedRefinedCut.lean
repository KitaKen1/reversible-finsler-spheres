module

public import Finsler.Topology.JoinedAnnularFiltered
public import Finsler.Topology.FactorwiseSubdivisionComparison

/-! One common rectangle refinement gives closed retained-length
components on the full two-time-plane source. Their ambient inclusions
are literally the specified small approximation, actual family map and
original annular cut, in the original cut's degree convention. -/

@[expose] public section
namespace Finsler.JoinedRefinedCut

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

private theorem transport_d (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i j i' j' : ℕ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j ≫ eqToHom (congrArg D.X h.symm) = f.f i := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def retraction (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    chains (TopCat.of (Outer X)) ⟶ small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) :=
  FactorwiseSubdivisionComparison.productRetraction
    (X := TopCat.of (ClosedInterval × ClosedInterval)) (Y := TopCat.of X)
    (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η)
    (PairDistanceCover.cover (id : X → X) η)
    (PairDistanceCover.cover_open id continuous_id η) (PairDistanceCover.cover_univ id hη)
    (PairDistanceCover.cover_open id continuous_id η) (PairDistanceCover.cover_univ id hη)

theorem retraction_inclusion (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    retraction X η hη ≫ inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) =
      TauCeti.singularSmallApprox (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η) := by
  unfold retraction FactorwiseSubdivisionComparison.productRetraction
  exact TauCeti.smallSingularRetraction_comp_ι coeff _ _ _

theorem exists_closed_filtered_components {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∀ (i : Fin 3) (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ v : ∀ q, (chains (TopCat.of (Outer X))).X ((m + p) + q + 1) ⟶
        (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q,
      ∀ q,
        (v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          (TauCeti.singularSmallApprox (X := TopCat.of (Outer X)) coeff
            (JoinedFilteredCap.rectangleCover X η)).f ((m + p) + q + 1) ≫
          (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
        (v (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (chains (TopCat.of (Outer X))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v q) := by
  obtain ⟨η, hη, hηb, hop⟩ := JoinedAnnularFiltered.exists_closed_filtered_output m F u a ha ha1
    h hρr hr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro i p L A T hT hshort hA
  obtain ⟨d, hid⟩ := hop i p L A T hT hshort hA
  let C := chains (TopCat.of (Outer X))
  let R := retraction X η hη
  let z := fun q => R.f ((m + 1) + (p + q)) ≫ d q
  have hz (q : ℕ) : z (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
      C.d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ z q := by
    dsimp [z]
    rw [Category.assoc, (hid q).2, ← Category.assoc, R.comm, Category.assoc]
  let v := fun q => eqToHom (congrArg C.X
    (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)) ≫ z q
  refine ⟨v, ?_⟩
  intro q
  constructor
  · dsimp [v, z]
    rw [Category.assoc, Category.assoc, (hid q).1]
    have he : (m + p) + q + 1 = (m + 1) + (p + q) := by omega
    have hi := transport_f (R ≫ inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) ≫
      push (JoinedFamilyNaturality.globalMap u a ha ha1 i)) _ _ he
    have hh := congrArg (fun t => t ≫ AnnularCutComparison.cut m p h
      (show ρ < r by linarith [h.1.trans h.2.2]) hr T hT q) hi
    have hR := congrArg (fun f => f.f ((m + p) + q + 1)) (retraction_inclusion X η hη)
    rw [← hR]
    simpa only [HomologicalComplex.comp_f, Category.assoc] using hh
  · dsimp [v]
    have ht := transport_d C ((m + p) + q + 2) ((m + p) + q + 1)
      ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) (by omega) (by omega)
    rw [Category.assoc, hz, ← Category.assoc, ht]
    simp only [Category.assoc]
    rfl

end
end Finsler.JoinedRefinedCut
