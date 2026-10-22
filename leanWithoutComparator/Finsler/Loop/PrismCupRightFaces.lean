module

public import Finsler.Loop.MappedPrismCapSimplex

/-! Actual prism front/tail formulas for a spatial RIGHT cup factor.
The surviving time jumps lie in the front; later jumps make the spatial
right face degenerate. The original parent simplex is retained. -/
@[expose] public section
namespace Finsler.PrismCupRightFaces
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MappedPrismCapSimplex
open scoped Simplicial DoldKan
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def embedding (p q : ℕ) : (Δ[p] : SSet.{0}) ⟶ Δ[p + q] :=
  SSet.stdSimplex.map (SimplexCategory.subinterval 0 p (by omega))

def front (p q : ℕ) (i : Fin (p + q + 1)) :
    ((Δ[p + q] : SSet.{0}) ⊗ Δ[1]) _⦋p + 1⦌ :=
  ((Δ[p + q] : SSet.{0}) ⊗ Δ[1]).map
    (SimplexCategory.subinterval 0 (p + 1) (by omega)).op (PrismShuffle.rect (p + q) i)

def tail (p q : ℕ) (i : Fin (p + q + 1)) : (Δ[p + q] : SSet.{0}) _⦋q⦌ :=
  (Δ[p + q] : SSet.{0}).map
    (SimplexCategory.subinterval (p + 1) q (by omega)).op (PrismShuffle.rect (p + q) i).1

theorem early_front (p q : ℕ) (i : Fin (p + q + 1)) (hi : i.val ≤ p) :
    front p q i = ((embedding p q) ⊗ₘ 𝟙 (Δ[1] : SSet.{0})).app _
      (PrismShuffle.rect p ⟨i.val, by omega⟩) := by
  let k : Fin (p + 1) := ⟨i.val, by omega⟩
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    change i.predAbove ⟨j.val, by omega⟩ = ⟨(k.predAbove j).val, by omega⟩
    apply Fin.ext
    change (i.predAbove ⟨j.val, by omega⟩).val = (k.predAbove j).val
    by_cases hj : j ≤ k.castSucc
    · have hh : (⟨j.val, by omega⟩ : Fin (p + q + 2)) ≤ i.castSucc := by
        change j.val ≤ i.val
        exact hj
      rw [Fin.predAbove_of_le_castSucc _ _ hh, Fin.predAbove_of_le_castSucc _ _ hj]
      rfl
    · have hh : i.castSucc < (⟨j.val, by omega⟩ : Fin (p + q + 2)) := by
        change i.val < j.val
        exact lt_of_not_ge hj
      rw [Fin.predAbove_of_castSucc_lt _ _ hh, Fin.predAbove_of_castSucc_lt _ _ (lt_of_not_ge hj)]
      rfl
  · apply SSet.stdSimplex.ext
    intro j
    change SSet.stdSimplex.objMk₁.{0} i.succ.castSucc ⟨j.val, by omega⟩ =
      SSet.stdSimplex.objMk₁.{0} k.succ.castSucc j
    have hj : (⟨j.val, by omega⟩ : Fin (p + q + 2)).castSucc < i.succ.castSucc ↔
        j.castSucc < k.succ.castSucc := by rfl
    simp only [SSet.stdSimplex.objMk₁_apply, hj]

theorem early_tail (p q : ℕ) (i : Fin (p + q + 1)) (hi : i.val ≤ p) :
    tail p q i = SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.subinterval p q (by omega)) := by
  apply SSet.stdSimplex.ext
  intro j
  change i.predAbove ⟨j.val + (p + 1), by omega⟩ = ⟨j.val + p, by omega⟩
  rw [Fin.predAbove_of_castSucc_lt _ _ (show i.castSucc < (⟨j.val + (p + 1), by omega⟩ : Fin (p + q + 2)) by
    change i.val < j.val + (p + 1); omega)]
  apply Fin.ext
  change j.val + (p + 1) - 1 = j.val + p
  omega

theorem late_tail_degenerate (p q : ℕ) (i : Fin (p + q + 1)) (hi : p < i.val) :
    tail p q i ∈ (Δ[p + q] : SSet.{0}).degenerate q := by
  by_contra hn
  have hs := (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mp hn
  have hlt := hs (show (⟨i.val - (p + 1), by omega⟩ : Fin (q + 1)) <
      ⟨i.val - (p + 1) + 1, by omega⟩ by change i.val - (p + 1) < i.val - (p + 1) + 1; omega)
  have hl : tail p q i ⟨i.val - (p + 1), by omega⟩ = i := by
    change i.predAbove ⟨i.val - (p + 1) + (p + 1), by omega⟩ = i
    have he : (⟨i.val - (p + 1) + (p + 1), by omega⟩ : Fin (p + q + 2)) = i.castSucc := by
      apply Fin.ext; change i.val - (p + 1) + (p + 1) = i.val; omega
    rw [he, Fin.predAbove_castSucc_self]
  have hr : tail p q i ⟨i.val - (p + 1) + 1, by omega⟩ = i := by
    change i.predAbove ⟨i.val - (p + 1) + 1 + (p + 1), by omega⟩ = i
    have he : (⟨i.val - (p + 1) + 1 + (p + 1), by omega⟩ : Fin (p + q + 2)) = i.succ := by
      apply Fin.ext; change i.val - (p + 1) + 1 + (p + 1) = i.val + 1; omega
    rw [he, Fin.predAbove_succ_self]
  rw [hl, hr] at hlt
  exact (lt_irrefl i) hlt

theorem model_front (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) :
    (embedding p q ⊗ₘ 𝟙 (Δ[1] : SSet.{0})) ≫ ProductSimplexCarrier.model X Y σ τ =
      ProductSimplexCarrier.model X Y
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) τ := by
  dsimp only [ProductSimplexCarrier.model, embedding]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    SSet.yonedaEquiv_symm_naturality_left]

theorem mapped_front (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + q + 1)) (hi : i.val ≤ p) :
    (TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 (p + 1) (by omega)).op
      (simplex X Y (p + q) σ τ i) =
      simplex X Y p ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ)
        τ ⟨i.val, by omega⟩ := by
  dsimp only [simplex]
  rw [← NatTrans.naturality_apply (ProductSimplexCarrier.model X Y σ τ)]
  change (ProductSimplexCarrier.model X Y σ τ).app _ (front p q i) = _
  rw [early_front p q i hi]
  change (((embedding p q ⊗ₘ 𝟙 (Δ[1] : SSet.{0})) ≫ ProductSimplexCarrier.model X Y σ τ).app _
    (PrismShuffle.rect p ⟨i.val, by omega⟩)) = _
  rw [model_front]

theorem tail_projection (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) (i : Fin (p + q + 1)) :
    (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app _
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval (p + 1) q (by omega)).op
        (simplex X Y (p + q) σ τ i)) =
      (SSet.yonedaEquiv.symm σ).app _ (tail p q i) := by
  dsimp only [simplex]
  rw [← NatTrans.naturality_apply (ProductSimplexCarrier.model X Y σ τ)]
  change ((ProductSimplexCarrier.model X Y σ τ ≫ TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app _
    (((Δ[p + q] : SSet.{0}) ⊗ Δ[1]).map (SimplexCategory.subinterval (p + 1) q (by omega)).op
      (PrismShuffle.rect (p + q) i))) = _
  rw [model_fst]
  rfl

theorem tail_coefficient (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) (i : Fin (p + q + 1))
    (A : singularCochainGroup (ZMod 2) X q) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval (p + 1) q (by omega)).op
        (simplex X Y (p + q) σ τ i)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) q A =
      (TopCat.toSSet.obj X).ιChainComplex ((SSet.yonedaEquiv.symm σ).app _ (tail p q i)) ≫ A := by
  change _ ≫ ((SSet.chainComplexMap (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)) coeff).f q ≫ A) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, tail_projection]

theorem early_tail_coefficient (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + q + 1)) (hi : i.val ≤ p) (A : singularCochainGroup (ZMod 2) X q) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval (p + 1) q (by omega)).op
        (simplex X Y (p + q) σ τ i)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) q A =
      (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ A := by
  rw [tail_coefficient, early_tail p q i hi]
  rfl

theorem late_tail_zero (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + q + 1)) (hi : p < i.val) (A : singularCochainGroup (ZMod 2) X q)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval (p + 1) q (by omega)).op
        (simplex X Y (p + q) σ τ i)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) q A = 0 := by
  rw [tail_coefficient, ← NormalizedPrismCapFront.normalize_eq X q A hA]
  exact ShuffleBlockNormalization.normalize_simplex_zero X q A _
    (ShuffleBlockNormalization.map_degenerate (SSet.yonedaEquiv.symm σ) _ (late_tail_degenerate p q i hi))

end
end Finsler.PrismCupRightFaces
