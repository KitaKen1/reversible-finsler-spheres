module

public import Finsler.Loop.MappedPrismCapSimplex
public import Finsler.Topology.TimeTriangleSplit
public import Mathlib.Algebra.BigOperators.Fin

/-! A genuine normalized cap in the spatial factor commutes exactly
with the actual singular cross with a right-hand one-simplex. Early
prism terms vanish, late terms have the original cap coefficient and
the actual shorter prism tail. The finite sum includes degree zero. -/

@[expose] public section
namespace Finsler.NormalizedCapRightInterval

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MappedPrismCapSimplex
open scoped Simplicial DoldKan BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem early_cap_zero (X Y : TopCat.{0}) (a q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (a + q + 1)) (hi : i.val < a)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (a + q) σ τ i) ≫
      absoluteChain (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) = 0 := by
  rw [SmallCapCarrier.cap_simplex]
  have hw : SmallCapCarrier.weight (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
      (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)
        (simplex X Y (a + q) σ τ i) = 0 := by
    dsimp only [SmallCapCarrier.weight]
    rw [early_coefficient_zero X Y (a + q) a (by omega) σ τ i hi φ hφ,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
  rw [hw, zero_comp]

theorem late_cap (X Y : TopCat.{0}) (a q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (a + q + 1)) (hi : a ≤ i.val)
    (φ : singularCochainGroup (ZMod 2) X a) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (a + q) σ τ i) ≫
      absoluteChain (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
      SmallCapCarrier.weight X a q (a + q) rfl φ σ ≫
        (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
          (simplex X Y q
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a q (by omega)).op σ)
            τ ⟨i.val - a, by omega⟩) := by
  rw [SmallCapCarrier.cap_simplex, late_tail X Y a q σ τ i hi]
  congr 1
  dsimp only [SmallCapCarrier.weight]
  rw [late_coefficient X Y (a + q) a (by omega) σ τ i hi φ]

theorem right_simplex_sum (X Y : TopCat.{0}) (p : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ SingularChainCross.right X Y p 1 τ =
      ∑ i : Fin (p + 1), (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y p σ τ i) := by
  rw [SingularChainCross.right_simplex, PrismShuffle.shuffle_one, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [SSet.ι_chainComplexMap_f]
  rfl

theorem cap_right_simplex (X Y : TopCat.{0}) (a q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      SingularChainCross.right X Y (a + q) 1 τ ≫
        absoluteChain (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
          (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a q (a + q) rfl φ ≫
        SingularChainCross.right X Y q 1 τ := by
  let w := SmallCapCarrier.weight X a q (a + q) rfl φ σ
  let σ' := (TopCat.toSSet.obj X).map (SimplexCategory.subinterval a q (by omega)).op σ
  calc
    _ = ∑ i : Fin (a + q + 1),
        (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (a + q) σ τ i) ≫
          absoluteChain (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
            (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) := by
      rw [← Category.assoc, right_simplex_sum, Preadditive.sum_comp]
    _ = ∑ i : Fin (q + 1), w ≫
        (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y q σ' τ i) := by
      let v := fun i : Fin (a + q + 1) =>
        (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (a + q) σ τ i) ≫
          absoluteChain (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
            (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)
      change (∑ i, v i) = _
      rw [← Fin.sum_congr' v (show a + (q + 1) = a + q + 1 by omega)]
      rw [Fin.sum_univ_add (a := a) (b := q + 1)]
      have hz : (∑ i : Fin a, v
          ((Fin.castAdd (q + 1) i).cast (show a + (q + 1) = a + q + 1 by omega))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact early_cap_zero X Y a q σ τ _ i.isLt φ hφ
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Fin.val_cast, Fin.val_natAdd, Nat.add_sub_cancel_left] using
        late_cap X Y a q σ τ
          ((Fin.natAdd a i).cast (show a + (q + 1) = a + q + 1 by omega))
          (by change a ≤ a + i.val; omega) φ
    _ = w ≫ ((TopCat.toSSet.obj X).ιChainComplex σ' ≫ SingularChainCross.right X Y q 1 τ) := by
      rw [right_simplex_sum, Preadditive.comp_sum]
    _ = _ := by
      symm
      rw [← Category.assoc, SmallCapCarrier.cap_simplex, Category.assoc]

theorem right_cap (X Y : TopCat.{0}) (a q : ℕ)
    (τ : TopCat.toSSet.obj Y _⦋1⦌) (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    SingularChainCross.right X Y (a + q) 1 τ ≫
      absoluteChain (X ⊗ Y) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
      absoluteChain X a q (a + q) rfl φ ≫ SingularChainCross.right X Y q 1 τ := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  simpa only [Category.assoc] using cap_right_simplex X Y a q σ τ φ hφ

theorem interval_cap (X : TopCat.{0}) (a q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    TimeTriangleSplit.interval X (a + q) ≫
      absoluteChain (X ⊗ TopCat.I) a (q + 1) (a + q + 1) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) a φ) =
      absoluteChain X a q (a + q) rfl φ ≫ TimeTriangleSplit.interval X q :=
  right_cap X TopCat.I a q TimeShuffleComparison.intervalSimplex φ hφ

end
end Finsler.NormalizedCapRightInterval
