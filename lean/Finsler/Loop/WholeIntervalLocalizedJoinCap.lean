module

public import Finsler.Loop.WholeIntervalJoinCover
public import Finsler.Loop.NormalizedCapTimePrism

/-! Localize the genuine first time join cap on the whole-interval
cover. On spatially small inputs its actual small prism commutes with
the actual localized spatial cap, already in the native near cylinder. -/

@[expose] public section
namespace Finsler.WholeIntervalLocalizedJoinCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem cap_cast (X : TopCat.{0}) (a q N : ℕ) (h : a + q = N)
    (φ : singularCochainGroup (ZMod 2) X a) :
    eqToHom (congrArg (chains X).X h.symm) ≫ absoluteChain X a q (a + q) rfl φ =
      absoluteChain X a q N h φ := by
  subst N
  simp only [eqToHom_refl, Category.id_comp]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R κ : ℝ)
  (hn : 1 ≤ n) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

include hκR in
theorem parent_near (q : ℕ)
    (τ : ((TopCat.of (P × (ClosedInterval × Q))).smallSingularSubcomplex
      (WholeIntervalJoinCover.cover α β κ) : SSet) _⦋n + q⦌)
    (hτ : (TopCat.toSSet.obj (TopCat.of (P × (ClosedInterval × Q)))).ιChainComplex τ.val ≫
      absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
        (CompactJoinCocycle.timeCocycle α β hn hκ) ≠ 0) :
    Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ τ.val) ⊆
      OriginalSecondHalfCompactTube.tube α β R := by
  obtain ⟨⟨x, y⟩, hs⟩ := (TopCat.mem_smallSingularSubcomplex_iff
    (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ) τ.val).mp τ.property
  rcases PairDistanceCover.near_far_rectangle (fun x => basepoint (α x))
    (fun y => basepoint (β y)) κ x y with hfar | hnear
  · have hf : Set.range ((TopCat.of (P × (ClosedInterval × Q))).toSSetObjEquiv _ τ.val) ⊆
        NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) κ :=
      fun z hz => hfar z.1 (hs hz).1 z.2.2 (hs hz).2
    exact (hτ (SupportedCap.cap_zero_on_simplex _ _ n q (n + q) rfl
      (CompactJoinCocycle.timeCocycle α β hn hκ)
      (CompactJoinCocycle.timeCocycle_far_zero α β hn hκ) τ.val hf)).elim
  · intro z hz
    exact (hnear z.1 (hs hz).1 z.2.2 (hs hz).2).le.trans hκR

def localized : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ))
    (chains (TopCat.of (OriginalSecondHalfCompactTube.tube α β R))) n :=
  CapOutputSupport.operation (X := TopCat.of (P × (ClosedInterval × Q)))
    (Y := TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ) (𝟙 _)
    (OriginalSecondHalfCompactTube.tube α β R) n (CompactJoinCocycle.timeCocycle α β hn hκ)
    (fun q τ hτ z hz => parent_near α β R κ hn hκ hκR q τ hτ hz)
    (CompactJoinCocycle.timeCocycle_closed α β hn hκ)

def native : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ))
    (chains (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) n :=
  (localized α β R κ hn hκ hκR).post (push (CompactNearJoinParameters.timeInv α β R))

theorem source (q : ℕ) : (native α β R κ hn hκ hκR).component q ≫
    (push (JoinTimeCommonRefinement.source α β R)).f q =
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).f (n + q) ≫
        absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
          (CompactJoinCocycle.timeCocycle α β hn hκ) := by
  have hm : CompactNearJoinParameters.timeInv α β R ≫ JoinTimeCommonRefinement.source α β R =
      SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q))) (OriginalSecondHalfCompactTube.tube α β R) := by
    rw [JoinTimeCommonRefinement.source, ← Category.assoc,
      CompactNearJoinParameters.timeInv_timeMap, Category.id_comp]
  have hi := CapOutputSupport.component_inclusion
    (X := TopCat.of (P × (ClosedInterval × Q))) (Y := TopCat.of (P × (ClosedInterval × Q)))
    (WholeIntervalJoinCover.cover α β κ) (𝟙 _) (OriginalSecondHalfCompactTube.tube α β R)
    n (CompactJoinCocycle.timeCocycle α β hn hκ)
    (fun q τ hτ z hz => parent_near α β R κ hn hκ hκR q τ hτ hz) q
  have hid : push (𝟙 (TopCat.of (P × (ClosedInterval × Q)))) =
      𝟙 (chains (TopCat.of (P × (ClosedInterval × Q)))) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (TopCat.of (P × (ClosedInterval × Q))))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [hid, HomologicalComplex.id_f, Category.comp_id] at hi
  dsimp only [native, DegreeLoweringHomology.Map.post]
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp, hm]
  exact hi

theorem common_component (η σ : ℝ) (q : ℕ) :
    (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component q ≫
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f q =
      (WholeIntervalJoinCover.refinement α β κ R η σ).f (n + q) ≫
        (native α β R κ hn hκ hκR).component q := by
  haveI := CoarseJoinTimeCap.source_mono α β R q
  apply (cancel_mono ((push (JoinTimeCommonRefinement.source α β R)).f q)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f,
    OriginalNativeCommonCover.cap_source, Category.assoc, source,
    ← Category.assoc, ← HomologicalComplex.comp_f, WholeIntervalJoinCover.refinement_inclusion]

theorem source_succ (q : ℕ) :
    eqToHom (congrArg
      (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).X
      (show n + q + 1 = n + (q + 1) by omega)) ≫
        (native α β R κ hn hκ hκR).component (q + 1) ≫
          (push (JoinTimeCommonRefinement.source α β R)).f (q + 1) =
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).f (n + q + 1) ≫
        absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n (q + 1) (n + q + 1) (by omega)
          (CompactJoinCocycle.timeCocycle α β hn hκ) := by
  rw [source, ← Category.assoc,
    transport_f (inclusion (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ))
      (n + q + 1) (n + (q + 1)) (by omega), Category.assoc]
  rw [cap_cast (TopCat.of (P × (ClosedInterval × Q))) n (q + 1) (n + q + 1) (by omega)]

theorem prism_cap (q : ℕ) :
    WholeIntervalJoinCover.prism α β κ (n + q) ≫
      eqToHom (congrArg
        (small (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).X
        (show n + q + 1 = n + (q + 1) by omega)) ≫
          (native α β R κ hn hκ hκR).component (q + 1) =
      (CompactJoinCapLocalization.localized α β hn hκ hκR).component q ≫
        AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) q := by
  haveI := CoarseJoinTimeCap.source_mono α β R (q + 1)
  apply (cancel_mono ((push (JoinTimeCommonRefinement.source α β R)).f (q + 1))).mp
  calc
    _ = WholeIntervalJoinCover.prism α β κ (n + q) ≫
        (inclusion (TopCat.of (P × (ClosedInterval × Q))) (WholeIntervalJoinCover.cover α β κ)).f (n + q + 1) ≫
          absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n (q + 1) (n + q + 1) (by omega)
            (CompactJoinCocycle.timeCocycle α β hn hκ) := by
      simp only [Category.assoc]
      rw [source_succ]
    _ = ((inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (n + q) ≫
        (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom (n + q) (n + q + 1)) ≫
          absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n (q + 1) (n + q + 1) (by omega)
            (CompactJoinCocycle.timeCocycle α β hn hκ) := by
      rw [← Category.assoc, ← WholeIntervalJoinCover.prism_inclusion]
    _ = (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (n + q) ≫
        absoluteChain (TopCat.of (P × Q)) n q (n + q) rfl (CompactJoinCocycle.cocycle α β hn hκ) ≫
          (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom q (q + 1) := by
      rw [Category.assoc, NormalizedCapTimePrism.actual_join_cap]
    _ = ((CompactJoinCapLocalization.localized α β hn hκ hκR).component q ≫
        (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f q) ≫
          (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom q (q + 1) := by
      rw [CompactJoinCapLocalization.source]
      simp only [Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun z => (CompactJoinCapLocalization.localized α β hn hκ hκR).component q ≫ z)
          (WholeIntervalJoinCover.native_prism_source α β R q)).symm

end
end Finsler.WholeIntervalLocalizedJoinCap
