module

public import Finsler.Loop.WholeIntervalLocalizedJoinCap
public import Finsler.Loop.NativeCommonTripleCap

/-! The whole-interval first cap, followed by the genuine native small
retraction and closed two-cap, is a closed coarse three-stage operation.
On the existing common cover it restricts literally to the actual native
common three-cap, already in the identical bounded output complex. -/

@[expose] public section
namespace Finsler.WholeIntervalNativeCap

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem compose_pre_component {B C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {a b : ℕ} (f : DegreeLoweringHomology.Map C D a) (g : DegreeLoweringHomology.Map D E b)
    (e : B ⟶ C) (q : ℕ) :
    ((DegreeLoweringComposition.compose f g).pre e).component q =
      eqToHom (congrArg B.X (Nat.add_assoc a b q)) ≫
        (e.f (a + (b + q)) ≫ f.component (b + q)) ≫ g.component q := by
  dsimp only [DegreeLoweringHomology.Map.pre]
  rw [DegreeLoweringComposition.component, ← Category.assoc,
    ← transport_f e ((a + b) + q) (a + (b + q)) (Nat.add_assoc a b q)]
  simp only [Category.assoc]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R η κ : ℝ)
  (hn : 1 ≤ n) (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hη : 0 < η)

def first : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ))
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)) n :=
  (WholeIntervalLocalizedJoinCap.native α β R κ hn hκ hκR).post
    (smallSingularRetraction (X := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) coeff
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
      (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη))

theorem first_on_common (σ : ℝ) (q : ℕ) :
    (WholeIntervalJoinCover.refinement α β κ R η σ).f (n + q) ≫
      (first α β R η κ hn hκ hκR hη).component q =
        (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component q := by
  let Y : TopCat.{0} := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)
  let U := SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η
  let Rt := smallSingularRetraction (X := Y) coeff U
    (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη)
  have hs : inclusion Y U ≫ Rt = 𝟙 _ := ι_comp_smallSingularRetraction (X := Y) coeff U
    (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη)
  change (WholeIntervalJoinCover.refinement α β κ R η σ).f (n + q) ≫
    ((WholeIntervalLocalizedJoinCap.native α β R κ hn hκ hκR).component q ≫ Rt.f q) = _
  rw [← Category.assoc, ← WholeIntervalLocalizedJoinCap.common_component α β R κ hn hκ hκR η σ q,
    Category.assoc, ← HomologicalComplex.comp_f, hs, HomologicalComplex.id_f, Category.comp_id]

variable (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X (n + (p + q)) ⟶ E.X q)
  (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        (n + (p + (q + 1))) (n + (p + q)) ≫ c q)

def coarse : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)) E (n + (n + p)) :=
  DegreeLoweringComposition.compose (first α β R η κ hn hκ hκR hη) (NestedCapHomology.operation n p c hc)

theorem coarse_on_common (σ : ℝ) (q : ℕ) :
    (WholeIntervalJoinCover.refinement α β κ R η σ).f ((n + (n + p)) + q) ≫
      (coarse α β R η κ hn hκ hκR hη E p c hc).component q =
        (NativeCommonTripleCap.operation α β R η σ κ hn hκ E p c hc).component q := by
  have he := compose_pre_component (first α β R η κ hn hκ hκR hη) (NestedCapHomology.operation n p c hc)
    (WholeIntervalJoinCover.refinement α β κ R η σ) q
  rw [first_on_common] at he
  exact he

end
end Finsler.WholeIntervalNativeCap
