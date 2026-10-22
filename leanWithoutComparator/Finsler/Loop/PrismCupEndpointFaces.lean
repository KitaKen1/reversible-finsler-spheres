module

public import Finsler.Loop.PrismCupRightFaces
public import Finsler.Topology.PrismRectangle

/-! Actual front and back faces of every simplicial homotopy prism.
Early jumps retain endpoint ONE on the tail; late jumps retain endpoint
ZERO on the front. These are simplex equalities, with no cochain premise. -/
@[expose] public section
namespace Finsler.PrismCupEndpointFaces
open CategoryTheory MonoidalCategory AlgebraicTopology
open scoped Simplicial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable {X Y : SSet.{0}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)

def simplex (n : ℕ) (σ : X _⦋n⦌) (i : Fin (n + 1)) : Y _⦋n + 1⦌ :=
  (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h).app _ (PrismShuffle.rect n i)

theorem early_front (p q N : ℕ) (hN : p + q = N) (σ : X _⦋N⦌) (i : Fin (N + 1)) (hi : i.val ≤ p) :
    Y.map (SimplexCategory.subinterval 0 (p + 1) (by omega)).op (simplex H N σ i) =
      simplex H p (X.map (SimplexCategory.subinterval 0 p (by omega)).op σ) ⟨i.val, by omega⟩ := by
  subst N
  unfold simplex
  rw [← NatTrans.naturality_apply]
  change (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h).app _ (PrismCupRightFaces.front p q i) = _
  rw [PrismCupRightFaces.early_front p q i hi]
  change ((PrismCupRightFaces.embedding p q ▷ Δ[1]) ≫ (SSet.yonedaEquiv.symm σ ▷ Δ[1]) ≫ H.h).app _ _ = _
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  dsimp only [PrismCupRightFaces.embedding, PrismCapTail.embedding]
  rw [SSet.yonedaEquiv_symm_naturality_left]

theorem late_tail (a q N : ℕ) (hN : a + q = N) (σ : X _⦋N⦌) (i : Fin (N + 1)) (hi : a ≤ i.val) :
    Y.map (SimplexCategory.subinterval a (q + 1) (by omega)).op (simplex H N σ i) =
      simplex H q (X.map (SimplexCategory.subinterval a q (by omega)).op σ) ⟨i.val - a, by omega⟩ := by
  subst N
  unfold simplex
  rw [← NatTrans.naturality_apply]
  change (SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h).app _ (PrismCapTail.tail a q i) = _
  rw [PrismCapTail.late_tail_eq a q i hi]
  change ((PrismCapTail.embedding a q ▷ Δ[1]) ≫ (SSet.yonedaEquiv.symm σ ▷ Δ[1]) ≫ H.h).app _ _ = _
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  dsimp only [PrismCupRightFaces.embedding, PrismCapTail.embedding]
  rw [SSet.yonedaEquiv_symm_naturality_left]

theorem early_tail (p q N : ℕ) (hN : p + q = N) (σ : X _⦋N⦌) (i : Fin (N + 1)) (hi : i.val ≤ p) :
    Y.map (SimplexCategory.subinterval (p + 1) q (by omega)).op (simplex H N σ i) =
      g.app _ (X.map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  subst N
  have he : ((Δ[p + q] : SSet.{0}) ⊗ Δ[1]).map (SimplexCategory.subinterval (p + 1) q (by omega)).op
      (PrismShuffle.rect (p + q) i) = SSet.ι₁.app _
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.subinterval p q (by omega))) := by
    apply Prod.ext
    · exact PrismCupRightFaces.early_tail p q i hi
    · apply SSet.stdSimplex.ext
      intro j
      change SSet.stdSimplex.objMk₁.{0} i.succ.castSucc ⟨j.val + (p + 1), by omega⟩ = 1
      exact SSet.stdSimplex.objMk₁_of_le_castSucc _ _ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
  unfold simplex
  rw [← NatTrans.naturality_apply, he]
  change (SSet.ι₁ ≫ SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h).app _ _ = _
  rw [SSet.ι₁_comp_assoc, H.h₁]
  rfl

theorem late_front (a q N : ℕ) (hN : a + q = N) (σ : X _⦋N⦌) (i : Fin (N + 1)) (hi : a ≤ i.val) :
    Y.map (SimplexCategory.subinterval 0 a (by omega)).op (simplex H N σ i) =
      f.app _ (X.map (SimplexCategory.subinterval 0 a (by omega)).op σ) := by
  subst N
  have he : ((Δ[a + q] : SSet.{0}) ⊗ Δ[1]).map (SimplexCategory.subinterval 0 a (by omega)).op
      (PrismShuffle.rect (a + q) i) = SSet.ι₀.app _
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.subinterval 0 a (by omega))) := by
    apply Prod.ext
    · exact PrismCapFront.late_front_eq (a + q) a (by omega) i hi
    · apply SSet.stdSimplex.ext
      intro j
      change SSet.stdSimplex.objMk₁.{0} i.succ.castSucc ⟨j.val, by omega⟩ = 0
      exact SSet.stdSimplex.objMk₁_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
  unfold simplex
  rw [← NatTrans.naturality_apply, he]
  change (SSet.ι₀ ≫ SSet.yonedaEquiv.symm σ ▷ Δ[1] ≫ H.h).app _ _ = _
  rw [SSet.ι₀_comp_assoc, H.h₀]
  rfl

end
end Finsler.PrismCupEndpointFaces
