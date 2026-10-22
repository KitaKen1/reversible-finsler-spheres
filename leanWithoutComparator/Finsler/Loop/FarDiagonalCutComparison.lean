module

public import Finsler.Loop.FarNormalizedDiagonalCap

/-! Changing from a genuine far/near cover to the specified deleted-
diagonal/near cover preserves the cap in the actual near homology.
Together with the actual supported representative primitive this
identifies normalized and specified diagonal cuts in that same target. -/

@[expose] public section
namespace Finsler.FarDiagonalCutComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable (m : ℕ) {X : TopCat.{0}} (f g : X ⟶ BorelEvaluation.sphere (m + 1))
  {ρ : ℝ} (hρ : 0 < ρ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
  (hf : Set.MapsTo (DiagonalPullbackCut.pairEvaluation f g) A (DiagonalAvoidanceCocycle.far (m + 1) ρ))

include hρ hc hf in
theorem diagonal_in_near (x : X) (hx : f x = g x) : x ∈ B := by
  have hs : x ∈ A ∪ B := by rw [hc]; trivial
  rcases hs with ha | hb
  · exact ((far_exclusion m f g hρ A hf ha) hx).elim
  · exact hb

theorem push_identity (Y : TopCat.{0}) : push (𝟙 Y) = 𝟙 (chains Y) := by
  change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
    (TopCat.toSSet.{0}.map (𝟙 Y)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

theorem specified_homology (q : ℕ) :
    (SupportedCapHomology.operation X A B hA hB hc (m + 1)
      (DiagonalPullbackCut.cocycle (dim_pos m) f g) (specified_supported m f g hρ A hf)
      (DiagonalPullbackCut.cocycle_closed (dim_pos m) f g)).homology q =
    (DiagonalCutNaturality.operation (dim_pos m) f g B hB (diagonal_in_near m f g hρ A B hc hf)).homology q := by
  have he := SupportedCapNaturality.homology_naturality (𝟙 X)
    A B (DiagonalPullbackCut.exclusion f g) B hA hB hc
    (DiagonalPullbackCut.exclusion_open f g) hB
    (DiagonalPullbackCut.neighborhood_cover f g B (diagonal_in_near m f g hρ A B hc hf))
    (far_exclusion m f g hρ A hf) (fun _ hx => hx) (m + 1) q
    (DiagonalPullbackCut.cocycle (dim_pos m) f g)
    (DiagonalPullbackCut.cocycle_supported (dim_pos m) f g)
    (DiagonalPullbackCut.cocycle_closed (dim_pos m) f g)
  have hr : restriction (𝟙 X) B B (fun _ hx => hx) = 𝟙 (TopCat.of B) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  rw [push_identity, HomologicalComplex.homologyMap_id, Category.id_comp,
    hr, push_identity, HomologicalComplex.homologyMap_id, Category.comp_id] at he
  simpa only [cochain_identity, DiagonalCutNaturality.operation] using he.symm

include hρ hc hf in
theorem normalized_homology (hm : 1 ≤ m) (hρ2 : ρ ≤ 2) (q : ℕ) :
    (FarNormalizedDiagonalCap.operation m f g hρ A B hA hB hc hf).homology q =
    (DiagonalCutNaturality.operation (dim_pos m) f g B hB (diagonal_in_near m f g hρ A B hc hf)).homology q := by
  exact (representative_homology m f g hρ hm hρ2 A B hA hB hc hf q).trans
    (specified_homology m f g hρ A B hA hB hc hf q)

include hρ hc hf in
theorem normalized_post_homology (hm : 1 ≤ m) (hρ2 : ρ ≤ 2) {Y : TopCat.{0}} (j : TopCat.of B ⟶ Y) (q : ℕ) :
    ((FarNormalizedDiagonalCap.operation m f g hρ A B hA hB hc hf).post (push j)).homology q =
    ((DiagonalCutNaturality.operation (dim_pos m) f g B hB (diagonal_in_near m f g hρ A B hc hf)).post (push j)).homology q := by
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    normalized_homology m f g hρ A B hA hB hc hf hm hρ2 q]

end
end Finsler.FarDiagonalCutComparison
