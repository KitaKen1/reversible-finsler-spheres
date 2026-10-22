module

public import Finsler.Loop.PrismCapFront

/-! The tail of each surviving actual standard prism simplex is the
actual prism on the spatial tail, with its time-step index shifted by
the front cap degree. This retains the original parent simplex. -/

@[expose] public section
namespace Finsler.PrismCapTail

open CategoryTheory MonoidalCategory AlgebraicTopology
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1100000

def embedding (a q : ℕ) : (Δ[q] : SSet.{0}) ⟶ Δ[a + q] :=
  SSet.stdSimplex.map (SimplexCategory.subinterval a q (by omega))

def tail (a q : ℕ) (i : Fin (a + q + 1)) :
    ((Δ[a + q] : SSet.{0}) ⊗ Δ[1]) _⦋q + 1⦌ :=
  ((Δ[a + q] : SSet.{0}) ⊗ Δ[1]).map
    (SimplexCategory.subinterval a (q + 1) (by omega)).op (PrismShuffle.rect (a + q) i)

theorem late_tail_eq (a q : ℕ) (i : Fin (a + q + 1)) (hi : a ≤ i.val) :
    tail a q i = ((embedding a q) ⊗ₘ 𝟙 (Δ[1] : SSet.{0})).app _
      (PrismShuffle.rect q ⟨i.val - a, by omega⟩) := by
  let k : Fin (q + 1) := ⟨i.val - a, by omega⟩
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    change i.predAbove ⟨j.val + a, by omega⟩ = ⟨(k.predAbove j).val + a, by omega⟩
    apply Fin.ext
    change (i.predAbove ⟨j.val + a, by omega⟩).val = (k.predAbove j).val + a
    by_cases hj : (⟨j.val + a, by omega⟩ : Fin (a + q + 2)) ≤ i.castSucc
    · have hj' : j ≤ k.castSucc := by
        change j.val ≤ i.val - a
        change j.val + a ≤ i.val at hj
        omega
      rw [Fin.predAbove_of_le_castSucc _ _ hj, Fin.predAbove_of_le_castSucc _ _ hj']
      rfl
    · have hj' : k.castSucc < j := by
        change i.val - a < j.val
        change ¬j.val + a ≤ i.val at hj
        omega
      rw [Fin.predAbove_of_castSucc_lt _ _ (lt_of_not_ge hj), Fin.predAbove_of_castSucc_lt _ _ hj']
      change j.val + a - 1 = (j.val - 1) + a
      change i.val - a < j.val at hj'
      omega
  · apply SSet.stdSimplex.ext
    intro j
    change SSet.stdSimplex.objMk₁.{0} i.succ.castSucc ⟨j.val + a, by omega⟩ =
      SSet.stdSimplex.objMk₁.{0} k.succ.castSucc j
    have hj : (⟨j.val + a, by omega⟩ : Fin (a + q + 2)).castSucc < i.succ.castSucc ↔
        j.castSucc < k.succ.castSucc := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      change j.val + a < i.val + 1 ↔ j.val < (i.val - a) + 1
      omega
    simp only [SSet.stdSimplex.objMk₁_apply, hj]

end
end Finsler.PrismCapTail
