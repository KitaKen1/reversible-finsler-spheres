module

public import Finsler.Topology.ShuffleBlockNormalization

/-! In the actual standard prism triangulation, a time step inside
the front cap block makes its spatial projection degenerate. A
normalized pulled-back join cochain therefore kills every such term.
This is the concrete front-block part of moving the join cap past
the time prism; the remaining tail and full chain equality are separate. -/

@[expose] public section
namespace Finsler.PrismCapFront

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 900000

def front (p a : ℕ) (ha : a ≤ p + 1) (i : Fin (p + 1)) :
    (Δ[p] : SSet.{0}) _⦋a⦌ :=
  (Δ[p] : SSet.{0}).map (SimplexCategory.subinterval 0 a (by omega)).op (PrismShuffle.rect p i).1

theorem front_apply (p a : ℕ) (ha : a ≤ p + 1) (i : Fin (p + 1)) (j : Fin (a + 1)) :
    front p a ha i j = i.predAbove ⟨j.val, by omega⟩ := rfl

theorem early_front_degenerate (p a : ℕ) (ha : a ≤ p + 1)
    (i : Fin (p + 1)) (hi : i.val < a) :
    front p a ha i ∈ (Δ[p] : SSet.{0}).degenerate a := by
  by_contra hn
  have hs := (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mp hn
  have hlt := hs (show (⟨i.val, by omega⟩ : Fin (a + 1)) < ⟨i.val + 1, by omega⟩ by
    change i.val < i.val + 1
    omega)
  have hleft : front p a ha i ⟨i.val, by omega⟩ = i := by
    change i.predAbove i.castSucc = i
    exact Fin.predAbove_castSucc_self i
  have hright : front p a ha i ⟨i.val + 1, by omega⟩ = i := by
    change i.predAbove i.succ = i
    exact Fin.predAbove_succ_self i
  rw [hleft, hright] at hlt
  exact (lt_irrefl i) hlt

theorem late_front_eq (p a : ℕ) (ha : a ≤ p + 1)
    (i : Fin (p + 1)) (hi : a ≤ i.val) :
    front p a ha i = SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.subinterval 0 a (show 0 + a ≤ p by omega)) := by
  apply SSet.stdSimplex.ext
  intro j
  change i.predAbove ⟨j.val, by omega⟩ = ⟨j.val, by omega⟩
  rw [Fin.predAbove_of_le_castSucc _ _ (show (⟨j.val, by omega⟩ : Fin (p + 2)) ≤ i.castSucc by
    change j.val ≤ i.val
    omega)]
  rfl

theorem early_normalized_zero (p a : ℕ) (ha : a ≤ p + 1)
    (i : Fin (p + 1)) (hi : i.val < a) (Y : TopCat.{0})
    (g : (Δ[p] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (φ : singularCochainGroup (ZMod 2) Y a) :
    (TopCat.toSSet.obj Y).ιChainComplex (g.app _ (front p a ha i)) ≫
      SingularNormalization.normalize Y a φ = 0 :=
  ShuffleBlockNormalization.normalize_simplex_zero Y a φ _
    (ShuffleBlockNormalization.map_degenerate g _ (early_front_degenerate p a ha i hi))

end
end Finsler.PrismCapFront
