module

public import Finsler.Loop.OriginalNativeCommonCover
public import Finsler.Topology.CapOutputSupport
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! Localize the genuine time join cap on the original factor cover,
then compare its retracted image with the common-cover cap directly in
the same native small-chain target. No target homology inclusion is
cancelled and no closure of a tested zero extension is used. -/

@[expose] public section
namespace Finsler.CoarseJoinTimeCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R η σ κ : ℝ)
  (hn : 1 ≤ n) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

include hκR in
theorem parent_near (q : ℕ)
    (τ : ((TopCat.of (P × (ClosedInterval × Q))).smallSingularSubcomplex
      (OriginalNativeCommonCover.oldCover α β σ κ) : SSet) _⦋n + q⦌)
    (hτ : (TopCat.toSSet.obj (TopCat.of (P × (ClosedInterval × Q)))).ιChainComplex τ.val ≫
      absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
        (CompactJoinCocycle.timeCocycle α β hn hκ) ≠ 0) :
    Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ τ.val) ⊆
      OriginalSecondHalfCompactTube.tube α β R := by
  obtain ⟨⟨x, y⟩, hs⟩ := (TopCat.mem_smallSingularSubcomplex_iff
    (TopCat.of (P × (ClosedInterval × Q)))) _ τ.val |>.mp τ.property
  rcases PairDistanceCover.near_far_rectangle (fun x => basepoint (α x))
    (fun y : ClosedInterval × Q => basepoint (β y.2)) κ x y with hfar | hnear
  · have hf : Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ τ.val) ⊆
        NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) κ :=
      fun z hz => hfar z.1 (hs hz).1.2 z.2 (hs hz).2.2
    exact (hτ (SupportedCap.cap_zero_on_simplex _ _ n q (n + q) rfl
      (CompactJoinCocycle.timeCocycle α β hn hκ)
      (CompactJoinCocycle.timeCocycle_far_zero α β hn hκ) τ.val hf)).elim
  · intro z hz
    exact (hnear z.1 (hs hz).1.2 z.2 (hs hz).2.2).le.trans hκR

def localized : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.oldCover α β σ κ))
    (chains (TopCat.of (OriginalSecondHalfCompactTube.tube α β R))) n :=
  CapOutputSupport.operation (X := TopCat.of (P × (ClosedInterval × Q)))
    (Y := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.oldCover α β σ κ) (𝟙 _) (OriginalSecondHalfCompactTube.tube α β R)
    n (CompactJoinCocycle.timeCocycle α β hn hκ)
    (fun q τ hτ z hz => parent_near α β R σ κ hn hκ hκR q τ hτ hz)
    (CompactJoinCocycle.timeCocycle_closed α β hn hκ)

def native : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.oldCover α β σ κ))
    (chains (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) n :=
  (localized α β R σ κ hn hκ hκR).post (push (CompactNearJoinParameters.timeInv α β R))

theorem source (q : ℕ) : (native α β R σ κ hn hκ hκR).component q ≫
    (push (JoinTimeCommonRefinement.source α β R)).f q =
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.oldCover α β σ κ)).f (n + q) ≫
        absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
          (CompactJoinCocycle.timeCocycle α β hn hκ) := by
  have hm : CompactNearJoinParameters.timeInv α β R ≫ JoinTimeCommonRefinement.source α β R =
      SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q))) (OriginalSecondHalfCompactTube.tube α β R) := by
    rw [JoinTimeCommonRefinement.source, ← Category.assoc,
      CompactNearJoinParameters.timeInv_timeMap, Category.id_comp]
  have hi := CapOutputSupport.component_inclusion
    (X := TopCat.of (P × (ClosedInterval × Q))) (Y := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.oldCover α β σ κ) (𝟙 _) (OriginalSecondHalfCompactTube.tube α β R)
    n (CompactJoinCocycle.timeCocycle α β hn hκ)
    (fun q τ hτ z hz => parent_near α β R σ κ hn hκ hκR q τ hτ hz) q
  have hid : push (𝟙 (TopCat.of (P × (ClosedInterval × Q)))) =
      𝟙 (chains (TopCat.of (P × (ClosedInterval × Q)))) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (TopCat.of (P × (ClosedInterval × Q))))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [hid, HomologicalComplex.id_f, Category.comp_id] at hi
  dsimp only [native, DegreeLoweringHomology.Map.post]
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp, hm]
  exact hi

theorem source_mono (q : ℕ) : Mono ((push (JoinTimeCommonRefinement.source α β R)).f q) := by
  haveI : IsIso (CompactNearJoinParameters.timeMap α β R) :=
    inferInstanceAs (IsIso (CompactNearJoinParameters.timeIso α β R).hom)
  haveI : Mono (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (OriginalSecondHalfCompactTube.tube α β R)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (JoinTimeCommonRefinement.source α β R) := by
    dsimp only [JoinTimeCommonRefinement.source]
    infer_instance
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (JoinTimeCommonRefinement.source α β R)).app (Opposite.op ⦋q⦌))))

theorem common_component (q : ℕ) :
    (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component q ≫
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f q =
      (OriginalNativeCommonCover.toOriginal α β R η σ κ).f (n + q) ≫
        (native α β R σ κ hn hκ hκR).component q := by
  haveI := source_mono α β R q
  apply (cancel_mono ((push (JoinTimeCommonRefinement.source α β R)).f q)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f,
    OriginalNativeCommonCover.cap_source, Category.assoc, source,
    ← Category.assoc, ← HomologicalComplex.comp_f, OriginalNativeCommonCover.toOriginal_inclusion]

variable (hη : 0 < η) (hσ : 0 < σ)

def before : DegreeLoweringHomology.Map (chains (TopCat.of (P × (ClosedInterval × Q))))
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)) n :=
  (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).pre
    (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
      (OriginalNativeCommonCover.cover α β R η σ κ)
      (OriginalNativeCommonCover.cover_open α β R η σ κ)
      (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ (by linarith)))

def after : DegreeLoweringHomology.Map (chains (TopCat.of (P × (ClosedInterval × Q))))
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)) n :=
  ((native α β R σ κ hn hκ hκR).pre
    (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
      (OriginalNativeCommonCover.oldCover α β σ κ) (OriginalNativeCommonCover.oldCover_open α β σ κ)
      (OriginalNativeCommonCover.oldCover_univ α β σ κ hσ hκ))).post
        (smallSingularRetraction (X := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) coeff
          (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
          (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη))

theorem before_small (q : ℕ) :
    ((before α β R η σ κ hn hκ hκR hη hσ).pre
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ))).component q =
        (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component q := by
  dsimp only [before, DegreeLoweringHomology.Map.pre]
  have hs := ι_comp_smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ (by linarith))
  rw [← Category.assoc, ← HomologicalComplex.comp_f, hs, HomologicalComplex.id_f, Category.id_comp]

theorem after_small (q : ℕ) :
    ((after α β R η σ κ hn hκ hκR hη hσ).pre
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ))).component q =
        (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component q := by
  let X : TopCat.{0} := TopCat.of (P × (ClosedInterval × Q))
  let V := OriginalNativeCommonCover.oldCover α β σ κ
  let Rold := smallSingularRetraction (X := X) coeff V (OriginalNativeCommonCover.oldCover_open α β σ κ)
    (OriginalNativeCommonCover.oldCover_univ α β σ κ hσ hκ)
  have hs : inclusion X (OriginalNativeCommonCover.cover α β R η σ κ) ≫ Rold =
      OriginalNativeCommonCover.toOriginal α β R η σ κ := by
    rw [← OriginalNativeCommonCover.toOriginal_inclusion, Category.assoc,
      ι_comp_smallSingularRetraction, Category.comp_id]
  let Y : TopCat.{0} := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)
  let U := SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η
  let Rnative := smallSingularRetraction (X := Y) coeff U
    (FullSecondHalfAnnularInputs.faceCover_open _ η) (FullSecondHalfAnnularInputs.faceCover_univ _ η hη)
  change (inclusion X (OriginalNativeCommonCover.cover α β R η σ κ)).f (n + q) ≫
    ((Rold.f (n + q) ≫ (native α β R σ κ hn hκ hκR).component q) ≫ Rnative.f q) = _
  rw [← Category.assoc, ← Category.assoc, ← HomologicalComplex.comp_f, hs,
    ← common_component α β R η σ κ hn hκ hκR q, Category.assoc,
    ← HomologicalComplex.comp_f, ι_comp_smallSingularRetraction,
    HomologicalComplex.id_f, Category.comp_id]

theorem homology_eq (q : ℕ) :
    (before α β R η σ κ hn hκ hκR hη hσ).homology q =
      (after α β R η σ κ hn hκ hκR hη hσ).homology q := by
  apply SmallInclusionHomologyCancellation.homology_eq
    (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ)
    (OriginalNativeCommonCover.cover_open α β R η σ κ)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ (by linarith))
    _ n _ _ q
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro t
  rw [before_small, after_small]

end
end Finsler.CoarseJoinTimeCap
