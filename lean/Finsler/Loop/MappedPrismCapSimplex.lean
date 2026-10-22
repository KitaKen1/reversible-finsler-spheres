module

public import Finsler.Loop.PrismCapTail
public import Finsler.Loop.NormalizedPrismCapFront
public import Finsler.Topology.ProductSimplexProjection

/-! Transport the concrete prism front and tail through the genuine
singular classifying product map. The first projection is proved from
the actual monoidal map, and every cap coefficient is the actual AW
front evaluation. No projection or model comparison is assumed. -/

@[expose] public section
namespace Finsler.MappedPrismCapSimplex

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

theorem model_fst (X Y : TopCat.{0}) {p k : ℕ}
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋k⦌) :
    ProductSimplexCarrier.model X Y σ τ ≫ TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y) =
      CartesianMonoidalCategory.fst (Δ[p] : SSet.{0}) Δ[k] ≫ SSet.yonedaEquiv.symm σ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply (X.toSSetObjEquiv n).injective
  apply ContinuousMap.ext
  intro t
  change X.toSSetObjEquiv n
    ((TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app n
      ((ProductSimplexCarrier.model X Y σ τ).app n z)) t =
        X.toSSetObjEquiv n ((SSet.yonedaEquiv.symm σ).app n z.1) t
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  exact ProductSimplexCarrier.model_fst X Y σ τ z t

def simplex (X Y : TopCat.{0}) (p : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + 1)) : TopCat.toSSet.obj (X ⊗ Y) _⦋p + 1⦌ :=
  (ProductSimplexCarrier.model X Y σ τ).app _ (PrismShuffle.rect p i)

theorem front_projection (X Y : TopCat.{0}) (p a : ℕ) (ha : a ≤ p + 1)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) (i : Fin (p + 1)) :
    (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app _
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p σ τ i)) =
      (SSet.yonedaEquiv.symm σ).app _ (PrismCapFront.front p a ha i) := by
  dsimp only [simplex]
  rw [← NatTrans.naturality_apply (ProductSimplexCarrier.model X Y σ τ)]
  change ((ProductSimplexCarrier.model X Y σ τ ≫
    TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app _
      (((Δ[p] : SSet.{0}) ⊗ Δ[1]).map (SimplexCategory.subinterval 0 a (by omega)).op
        (PrismShuffle.rect p i))) = _
  rw [model_fst]
  rfl

theorem front_coefficient (X Y : TopCat.{0}) (p a : ℕ) (ha : a ≤ p + 1)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) (i : Fin (p + 1))
    (φ : singularCochainGroup (ZMod 2) X a) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p σ τ i)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) a φ =
      (TopCat.toSSet.obj X).ιChainComplex
        ((SSet.yonedaEquiv.symm σ).app _ (PrismCapFront.front p a ha i)) ≫ φ := by
  change _ ≫ ((SSet.chainComplexMap (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)) coeff).f a ≫ φ) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, front_projection X Y p a ha σ τ i]

theorem early_coefficient_zero (X Y : TopCat.{0}) (p a : ℕ) (ha : a ≤ p + 1)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + 1)) (hi : i.val < a)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p σ τ i)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) a φ = 0 := by
  rw [front_coefficient X Y p a ha σ τ i φ]
  exact NormalizedPrismCapFront.early_zero p a ha i hi X (SSet.yonedaEquiv.symm σ) φ hφ

theorem late_coefficient (X Y : TopCat.{0}) (p a : ℕ) (ha : a ≤ p + 1)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + 1)) (hi : a ≤ i.val)
    (φ : singularCochainGroup (ZMod 2) X a) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      ((TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval 0 a (by omega)).op
        (simplex X Y p σ τ i)) ≫ cochainPullback (CartesianMonoidalCategory.fst X Y) a φ =
      (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 a (by omega)).op σ) ≫ φ := by
  rw [front_coefficient X Y p a ha σ τ i φ, PrismCapFront.late_front_eq p a ha i hi]
  rfl

theorem model_tail (X Y : TopCat.{0}) (a q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) :
    (PrismCapTail.embedding a q ⊗ₘ 𝟙 (Δ[1] : SSet.{0})) ≫ ProductSimplexCarrier.model X Y σ τ =
      ProductSimplexCarrier.model X Y
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a q (by omega)).op σ) τ := by
  dsimp only [ProductSimplexCarrier.model, PrismCapTail.embedding]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    SSet.yonedaEquiv_symm_naturality_left]

theorem late_tail (X Y : TopCat.{0}) (a q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (a + q + 1)) (hi : a ≤ i.val) :
    (TopCat.toSSet.obj (X ⊗ Y)).map (SimplexCategory.subinterval a (q + 1) (by omega)).op
      (simplex X Y (a + q) σ τ i) =
      simplex X Y q
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a q (by omega)).op σ) τ
          ⟨i.val - a, by omega⟩ := by
  dsimp only [simplex]
  rw [← NatTrans.naturality_apply (ProductSimplexCarrier.model X Y σ τ)]
  change (ProductSimplexCarrier.model X Y σ τ).app _ (PrismCapTail.tail a q i) = _
  rw [PrismCapTail.late_tail_eq a q i hi]
  change (((PrismCapTail.embedding a q ⊗ₘ 𝟙 (Δ[1] : SSet.{0})) ≫
    ProductSimplexCarrier.model X Y σ τ).app _ (PrismShuffle.rect q ⟨i.val - a, by omega⟩)) = _
  rw [model_tail]

end
end Finsler.MappedPrismCapSimplex
