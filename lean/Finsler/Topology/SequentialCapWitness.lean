module

public import Finsler.Topology.SmallCapCarrier

/-! Nonzero actual successive caps force nonzero evaluations of both
specified front faces, even for arbitrary cochains. These are the two
witnesses needed by whole-parent tested-cut adequacy. -/

@[expose] public section
namespace Finsler.SequentialCapWitness

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def front (X : TopCat.{0}) (p q : ℕ) (σ : TopCat.toSSet.obj X _⦋p + q⦌) :
    TopCat.toSSet.obj X _⦋p⦌ :=
  (TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ

def back (X : TopCat.{0}) (p q : ℕ) (σ : TopCat.toSSet.obj X _⦋p + q⦌) :
    TopCat.toSSet.obj X _⦋q⦌ :=
  (TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ

private theorem cap_zero_of_front_zero (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (σ : TopCat.toSSet.obj X _⦋p + q⦌)
    (h : (TopCat.toSSet.obj X).ιChainComplex (front X p q σ) ≫ φ = 0) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q (p + q) rfl φ = 0 := by
  rw [SmallCapCarrier.cap_simplex]
  have hw : SmallCapCarrier.weight X p q (p + q) rfl φ σ = 0 := by
    unfold SmallCapCarrier.weight
    change (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv ≫
      (((TopCat.toSSet.obj X).ιChainComplex (front X p q σ) ≫ φ) ▷
        (𝟙_ (ModuleCat (ZMod 2)))) ≫ (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = 0
    rw [h, MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
  rw [hw, zero_comp]

theorem cap_nonzero_front (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (σ : TopCat.toSSet.obj X _⦋p + q⦌)
    (h : (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X p q (p + q) rfl φ ≠ 0) :
    (TopCat.toSSet.obj X).ιChainComplex (front X p q σ) ≫ φ ≠ 0 := by
  intro hz
  exact h (cap_zero_of_front_zero X p q φ σ hz)

theorem sequential_nonzero_faces (X : TopCat.{0}) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (σ : TopCat.toSSet.obj X _⦋k + (p + q)⦌)
    (h : ((TopCat.toSSet.obj X).ιChainComplex σ ≫
      absoluteChain X k (p + q) (k + (p + q)) rfl φ) ≫
        absoluteChain X p q (p + q) rfl ψ ≠ 0) :
    ((TopCat.toSSet.obj X).ιChainComplex (front X k (p + q) σ) ≫ φ ≠ 0) ∧
    ((TopCat.toSSet.obj X).ιChainComplex (front X p q (back X k (p + q) σ)) ≫ ψ ≠ 0) := by
  constructor
  · apply cap_nonzero_front X k (p + q) φ σ
    intro hz
    exact h (by rw [hz, zero_comp])
  · apply cap_nonzero_front X p q ψ (back X k (p + q) σ)
    intro hz
    apply h
    rw [SmallCapCarrier.cap_simplex, Category.assoc]
    exact (congrArg (fun t => SmallCapCarrier.weight X k (p + q) (k + (p + q)) rfl φ σ ≫ t) hz).trans
      (comp_zero)

theorem simplex_map_range (X : TopCat.{0}) {p q : ℕ}
    (f : (⦋p⦌ : SimplexCategory) ⟶ ⦋q⦌) (σ : TopCat.toSSet.obj X _⦋q⦌) :
    Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).map f.op σ)) ⊆
      Set.range (X.toSSetObjEquiv _ σ) := by
  have hs : σ ∈ (X.smallSingularSubcomplex (parentFamily.{1} σ)).obj (Opposite.op ⦋q⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff X (parentFamily.{1} σ) σ).mpr
      ⟨PUnit.unit, Set.Subset.rfl⟩
  have ht := ((X.smallSingularSubcomplex (parentFamily.{1} σ) : SSet).map f.op ⟨σ, hs⟩).property
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X (parentFamily.{1} σ)
    ((TopCat.toSSet.obj X).map f.op σ)).mp ht
  exact hi

theorem sequential_faces_range (X : TopCat.{0}) (k p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋k + (p + q)⦌) :
    (Set.range (X.toSSetObjEquiv _ (front X k (p + q) σ)) ⊆ Set.range (X.toSSetObjEquiv _ σ)) ∧
    (Set.range (X.toSSetObjEquiv _ (front X p q (back X k (p + q) σ))) ⊆
      Set.range (X.toSSetObjEquiv _ σ)) := by
  constructor
  · exact simplex_map_range X _ σ
  · exact (simplex_map_range X _ (back X k (p + q) σ)).trans (simplex_map_range X _ σ)

end
end Finsler.SequentialCapWitness
