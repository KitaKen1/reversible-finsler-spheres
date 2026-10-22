module

public import Finsler.Topology.JoinedSimultaneousPrisms

/-! Extend an actual closed small filtered cap with the genuine
rectangle retraction. Its original annular inclusion and all-degree
boundary compatibility are preserved. -/

@[expose] public section
namespace Finsler.JoinedSmallCapExtension

open CategoryTheory AlgebraicTopology TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedSimultaneousPrisms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem retraction_inclusion (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    retraction X η hη ≫ inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) =
      singularSmallApprox (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η) :=
  smallSingularRetraction_comp_ι (X := TopCat.of (Outer X)) coeff
    (JoinedFilteredCap.rectangleCover X η) (rectangles_open X η) (rectangles_univ X η hη)

variable (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (k : ℕ)
  (v : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X (k + q + 1) ⟶ E.X q)

def cap (q : ℕ) : (chains (TopCat.of (Outer X))).X (k + q + 1) ⟶ E.X q :=
  (retraction X η hη).f (k + q + 1) ≫ v q

theorem cap_comm
    (hv : ∀ q, v (q + 1) ≫ E.d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d (k + q + 2) (k + q + 1) ≫ v q)
    (q : ℕ) : cap X η hη E k v (q + 1) ≫ E.d (q + 1) q =
      (chains (TopCat.of (Outer X))).d (k + q + 2) (k + q + 1) ≫ cap X η hη E k v q := by
  dsimp [cap]
  rw [Category.assoc, hv q]
  simpa only [Nat.add_succ, Nat.add_zero, Category.assoc] using
    congrArg (fun f => f ≫ v q) ((retraction X η hη).comm (k + q + 2) (k + q + 1))

theorem cap_inclusion {P L : TopCat.{0}} (B : Set L) (f : TopCat.of (Outer X) ⟶ P)
    (z : ∀ q, (chains P).X (k + q + 1) ⟶ (chains L).X q)
    (v : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X (k + q + 1) ⟶
      (chains (TopCat.of B)).X q)
    (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap L B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f (k + q + 1) ≫
        (push f).f (k + q + 1) ≫ z q) (q : ℕ) :
    cap X η hη (chains (TopCat.of B)) k v q ≫ (push (SupportedCap.subspaceMap L B)).f q =
      (singularSmallApprox (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η)).f (k + q + 1) ≫
        (push f).f (k + q + 1) ≫ z q := by
  dsimp [cap]
  rw [Category.assoc, hv q]
  have hi := congrArg (fun g => g.f (k + q + 1)) (retraction_inclusion X η hη)
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g => g ≫ (push f).f (k + q + 1) ≫ z q) hi

end
end Finsler.JoinedSmallCapExtension
