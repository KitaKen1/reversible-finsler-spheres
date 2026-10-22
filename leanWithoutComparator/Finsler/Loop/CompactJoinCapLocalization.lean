module

public import Finsler.Loop.CompactNearJoinParameters
public import Finsler.Topology.CapOutputSupport
public import Finsler.Topology.SmallRectangleShuffle
public import Finsler.Topology.SmallInclusionHomologyCancellation
public import Finsler.Topology.NearFarCapSelf

/-! Localize the genuine normalized join Thom cap into the actual
compact near-pair source. A nonzero cap has its whole original parent
there by the actual factor-cover near/far dichotomy. The resulting
closed cap is constructed, including its source diagram and ordinary
ambient homology image; no support/lift or target injectivity is assumed. -/

@[expose] public section
namespace Finsler.CompactJoinCapLocalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))

def cover (ρ : ℝ) : (P × Q) → Set (P × Q) :=
  SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of Q)
    (PairDistanceCover.cover (fun x => basepoint (α x)) (ρ / 4))
    (PairDistanceCover.cover (fun y => basepoint (β y)) (ρ / 4))

theorem cover_open (ρ : ℝ) (c : P × Q) : IsOpen (cover α β ρ c) :=
  FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of Q)
    (PairDistanceCover.cover (fun x => basepoint (α x)) (ρ / 4))
    (PairDistanceCover.cover (fun y => basepoint (β y)) (ρ / 4))
    (PairDistanceCover.cover_open _ (H1AlignmentHomotopy.basepoint_continuous.comp α.continuous) _)
    (PairDistanceCover.cover_open _ (H1AlignmentHomotopy.basepoint_continuous.comp β.continuous) _) c

theorem cover_univ {ρ : ℝ} (hρ : 0 < ρ) : ⋃ c, cover α β ρ c = Set.univ :=
  FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of Q)
    (PairDistanceCover.cover (fun x => basepoint (α x)) (ρ / 4))
    (PairDistanceCover.cover (fun y => basepoint (β y)) (ρ / 4))
    (PairDistanceCover.cover_univ _ (div_pos hρ (by norm_num)))
    (PairDistanceCover.cover_univ _ (div_pos hρ (by norm_num)))

theorem parent_near (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R)
    (q : ℕ) (σ : ((TopCat.of (P × Q)).smallSingularSubcomplex (cover α β ρ) : SSet) _⦋n + q⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ.val ≫
      absoluteChain (TopCat.of (P × Q)) n q (n + q) rfl (CompactJoinCocycle.cocycle α β hn hρ) ≠ 0) :
    Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ.val) ⊆ CompactNearJoinParameters.tube α β R := by
  obtain ⟨⟨x, y⟩, hs⟩ :=
    (TopCat.mem_smallSingularSubcomplex_iff (TopCat.of (P × Q)) (cover α β ρ) σ.val).mp σ.property
  rcases PairDistanceCover.near_far_rectangle (fun x => basepoint (α x))
    (fun y => basepoint (β y)) ρ x y with hfar | hnear
  · have hf : Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ.val) ⊆
        NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
          (fun x => basepoint (α x)) (fun y => basepoint (β y)) ρ := by
      intro z hz
      exact hfar z.1 (hs hz).1 z.2 (hs hz).2
    exact (hσ (SupportedCap.cap_zero_on_simplex (TopCat.of (P × Q)) _ n q (n + q) rfl
      (CompactJoinCocycle.cocycle α β hn hρ) (CompactJoinCocycle.cocycle_far_zero α β hn hρ)
      σ.val hf)).elim
  · intro z hz
    exact (hnear z.1 (hs hz).1 z.2 (hs hz).2).le.trans hρR

def localized (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) :
    DegreeLoweringHomology.Map (small (TopCat.of (P × Q)) (cover α β ρ))
      (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) n :=
  CapOutputSupport.operation (X := TopCat.of (P × Q)) (Y := TopCat.of (P × Q))
    (cover α β ρ) (𝟙 (TopCat.of (P × Q)))
    (CompactNearJoinParameters.tube α β R) n (CompactJoinCocycle.cocycle α β hn hρ)
    (fun q σ hσ => parent_near α β hn hρ hρR q σ hσ) (CompactJoinCocycle.cocycle_closed α β hn hρ)

theorem source (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) (q : ℕ) :
    (localized α β hn hρ hρR).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f q =
        (inclusion (TopCat.of (P × Q)) (cover α β ρ)).f (n + q) ≫
          absoluteChain (TopCat.of (P × Q)) n q (n + q) rfl (CompactJoinCocycle.cocycle α β hn hρ) := by
  have hid : push (𝟙 (TopCat.of (P × Q))) = 𝟙 (chains (TopCat.of (P × Q))) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (TopCat.of (P × Q)))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hi := CapOutputSupport.component_inclusion (X := TopCat.of (P × Q)) (Y := TopCat.of (P × Q))
    (cover α β ρ) (𝟙 (TopCat.of (P × Q)))
    (CompactNearJoinParameters.tube α β R) n (CompactJoinCocycle.cocycle α β hn hρ)
    (fun q σ hσ => parent_near α β hn hρ hρR q σ hσ) q
  rw [hid, HomologicalComplex.id_f] at hi
  exact hi.trans (congrArg (fun f => (inclusion (TopCat.of (P × Q)) (cover α β ρ)).f (n + q) ≫ f)
    (Category.comp_id (absoluteChain (TopCat.of (P × Q)) n q (n + q) rfl
      (CompactJoinCocycle.cocycle α β hn hρ))))

def unrefined (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) :
    DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
      (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) n :=
  (localized α β hn hρ hρR).pre (smallSingularRetraction (X := TopCat.of (P × Q)) coeff
    (cover α β ρ) (cover_open α β ρ) (cover_univ α β hρ))

theorem unrefined_small (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) (q : ℕ) :
    (inclusion (TopCat.of (P × Q)) (cover α β ρ)).f (n + q) ≫
      (unrefined α β hn hρ hρR).component q = (localized α β hn hρ hρR).component q := by
  dsimp only [unrefined, DegreeLoweringHomology.Map.pre]
  have hs : inclusion (TopCat.of (P × Q)) (cover α β ρ) ≫
      smallSingularRetraction (X := TopCat.of (P × Q)) coeff (cover α β ρ)
        (cover_open α β ρ) (cover_univ α β hρ) = 𝟙 _ :=
    ι_comp_smallSingularRetraction (X := TopCat.of (P × Q)) coeff (cover α β ρ)
      (cover_open α β ρ) (cover_univ α β hρ)
  rw [← Category.assoc, ← HomologicalComplex.comp_f, hs, HomologicalComplex.id_f, Category.id_comp]

theorem ambient_homology (hn : 1 ≤ n) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : 2 * ρ ≤ R) (q : ℕ) :
    ((unrefined α β hn hρ hρR).post
      (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R)))).homology q =
      (SupportedCapHomology.absoluteOperation (TopCat.of (P × Q)) n
        (CompactJoinCocycle.cocycle α β hn hρ) (CompactJoinCocycle.cocycle_closed α β hn hρ)).homology q := by
  apply SmallInclusionHomologyCancellation.homology_eq (TopCat.of (P × Q)) (cover α β ρ)
    (cover_open α β ρ) (cover_univ α β hρ) (chains (TopCat.of (P × Q))) n _ _ q
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro t
  change (inclusion (TopCat.of (P × Q)) (cover α β ρ)).f (n + t) ≫
      ((unrefined α β hn hρ hρR).component t ≫
        (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f t) = _
  rw [← Category.assoc, unrefined_small α β hn hρ hρR t, source α β hn hρ hρR t]
  rfl

end
end Finsler.CompactJoinCapLocalization
