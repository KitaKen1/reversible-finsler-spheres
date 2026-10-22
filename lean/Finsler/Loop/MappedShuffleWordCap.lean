module

public import Finsler.Loop.ShuffleWordCapFront
public import Finsler.Loop.MappedPrismCapSimplex

/-! Transport arbitrary word fronts and tails through the actual
singular product classifying map. The cap coefficients are literal
Alexander--Whitney front evaluations. -/

@[expose] public section
namespace Finsler.MappedShuffleWordCap

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.ShuffleWords
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

def simplex (X Y : TopCat.{0}) (p j N : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool) :
    TopCat.toSSet.obj (X ⊗ Y) _⦋N⦌ :=
  (ProductSimplexCarrier.model X Y σ τ).app _ (ShuffleWordSimplex.simplex p j N w)

theorem front_projection (X Y : TopCat.{0}) (p j N a : ℕ) (ha : a ≤ N)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool) :
    (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app _
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p j N σ τ w)) =
    (SSet.yonedaEquiv.symm σ).app _ (ShuffleWordCapFront.front p N a ha w) := by
  dsimp only [simplex]
  rw [← NatTrans.naturality_apply (ProductSimplexCarrier.model X Y σ τ)]
  change ((ProductSimplexCarrier.model X Y σ τ ≫ TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app _
    (((Δ[p] : SSet.{0}) ⊗ Δ[j]).map (SimplexCategory.subinterval 0 a (by omega)).op
      (ShuffleWordSimplex.simplex p j N w))) = _
  rw [MappedPrismCapSimplex.model_fst]
  rfl

theorem front_coefficient (X Y : TopCat.{0}) (p j N a : ℕ) (ha : a ≤ N)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool)
    (φ : singularCochainGroup (ZMod 2) X a) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p j N σ τ w)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) a φ =
    (TopCat.toSSet.obj X).ιChainComplex
      ((SSet.yonedaEquiv.symm σ).app _ (ShuffleWordCapFront.front p N a ha w)) ≫ φ := by
  change _ ≫ ((SSet.chainComplexMap (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)) coeff).f a ≫ φ) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, front_projection]

theorem bad_coefficient_zero (X Y : TopCat.{0}) (p j N a : ℕ) (ha : a ≤ N)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool)
    (hw : w.take a ≠ List.replicate a false)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p j N σ τ w)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) a φ = 0 := by
  rw [front_coefficient X Y p j N a ha σ τ w φ]
  exact ShuffleWordCapFront.normalized_front_zero p N a ha w hw X (SSet.yonedaEquiv.symm σ) φ hφ

theorem prefix_coefficient (X Y : TopCat.{0}) (a p j N : ℕ) (ha : a ≤ N)
    (σ : TopCat.toSSet.obj X _⦋a + p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool)
    (φ : singularCochainGroup (ZMod 2) X a) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y (a + p) j N σ τ (List.replicate a false ++ w))) ≫
          cochainPullback (CartesianMonoidalCategory.fst X Y) a φ =
    (TopCat.toSSet.obj X).ιChainComplex
      ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 a (by omega)).op σ) ≫ φ := by
  rw [front_coefficient X Y (a + p) j N a ha σ τ (List.replicate a false ++ w) φ]
  dsimp only [ShuffleWordCapFront.front]
  rw [ShuffleWordSimplex.horizontal_front a p N ha w]
  rfl

theorem model_tail (X Y : TopCat.{0}) (a p j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) :
    (SSet.stdSimplex.map (SimplexCategory.subinterval a p (by omega)) ▷ (Δ[j] : SSet.{0})) ≫
      ProductSimplexCarrier.model X Y σ τ =
    ProductSimplexCarrier.model X Y
      ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a p (by omega)).op σ) τ := by
  rw [← tensorHom_id]
  dsimp only [ProductSimplexCarrier.model]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    SSet.yonedaEquiv_symm_naturality_left]

theorem prefix_tail (X Y : TopCat.{0}) (a p j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool) :
    (TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval a (p + j) (by omega)).op
      (simplex X Y (a + p) j ((a + p) + j) σ τ (List.replicate a false ++ w)) =
    simplex X Y p j (p + j)
      ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a p (by omega)).op σ) τ w := by
  have aux : ∀ (N : ℕ) (hN : a + (p + j) = N),
      (TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval a (p + j) (by omega)).op
        (simplex X Y (a + p) j N σ τ (List.replicate a false ++ w)) =
      simplex X Y p j (p + j)
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a p (by omega)).op σ) τ w := by
    intro N hN
    subst N
    dsimp only [simplex]
    rw [← NatTrans.naturality_apply (ProductSimplexCarrier.model X Y σ τ)]
    rw [ShuffleWordSimplex.horizontal_tail]
    change (((SSet.stdSimplex.map (SimplexCategory.subinterval a p (by omega)) ▷ (Δ[j] : SSet.{0})) ≫
      ProductSimplexCarrier.model X Y σ τ).app _ (ShuffleWordSimplex.simplex p j (p + j) w)) = _
    rw [model_tail]
  exact aux _ (by omega)

end
end Finsler.MappedShuffleWordCap
