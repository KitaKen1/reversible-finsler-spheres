module

public import Finsler.Loop.PrismCupRightFaces
public import Finsler.Loop.IntervalCupLeftProjection

/-! Exact RIGHT projection formula for the genuine canonical interval.
The normalized spatial tail kills late jumps; the surviving original
front prism terms are summed using the pinned TauCeti AW cup formula.
No cycle, closure, commutativity or omitted endpoint correction is used. -/
@[expose] public section
namespace Finsler.IntervalCupRightProjection
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MappedPrismCapSimplex Finsler.PrismCupRightFaces
open scoped Simplicial DoldKan BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def pair (u v : coeff ⟶ coeff) : coeff ⟶ coeff :=
  (λ_ coeff).inv ≫ (u ⊗ₘ v) ≫ (ρ_ coeff).hom

theorem pair_sum {J : Type*} (s : Finset J) (f : J → (coeff ⟶ coeff)) (v : coeff ⟶ coeff) :
    pair (∑ j ∈ s, f j) v = ∑ j ∈ s, pair (f j) v := by
  simp only [pair, sum_tensor, Preadditive.sum_comp, Preadditive.comp_sum]

theorem simplex_cup (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p) (A : singularCochainGroup (ZMod 2) X q)
    (σ : TopCat.toSSet.obj X _⦋N⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ CupOne.cup X p q N h T A =
      pair ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ T)
        ((TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ A) :=
  TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal (k := ZMod 2) X
    (λ_ coeff).inv (ρ_ coeff).hom p q N h T A σ

theorem early_term (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + q + 1)) (hi : i.val ≤ p)
    (T : singularCochainGroup (ZMod 2) (X ⊗ Y) (p + 1))
    (A : singularCochainGroup (ZMod 2) X q) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (p + q) σ τ i) ≫
      CupOne.cup (X ⊗ Y) (p + 1) q (p + q + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X Y) q A) =
      pair ((TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
        (simplex X Y p ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ)
          τ ⟨i.val, by omega⟩) ≫ T)
        ((TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ A) := by
  rw [simplex_cup, mapped_front X Y p q σ τ i hi, early_tail_coefficient X Y p q σ τ i hi A]

theorem late_term_zero (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (i : Fin (p + q + 1)) (hi : p < i.val)
    (T : singularCochainGroup (ZMod 2) (X ⊗ Y) (p + 1))
    (A : singularCochainGroup (ZMod 2) X q)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (p + q) σ τ i) ≫
      CupOne.cup (X ⊗ Y) (p + 1) q (p + q + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X Y) q A) = 0 := by
  rw [simplex_cup, late_tail_zero X Y p q σ τ i hi A hA]
  simp only [pair, MonoidalPreadditive.tensor_zero, zero_comp, comp_zero]

theorem right_simplex_cup (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p + q⦌) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (T : singularCochainGroup (ZMod 2) (X ⊗ Y) (p + 1))
    (A : singularCochainGroup (ZMod 2) X q)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ SingularChainCross.right X Y (p + q) 1 τ ≫
      CupOne.cup (X ⊗ Y) (p + 1) q (p + q + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X Y) q A) =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
        CupOne.cup X p q (p + q) rfl (SingularChainCross.right X Y p 1 τ ≫ T) A := by
  let w := (TopCat.toSSet.obj X).ιChainComplex
    ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ A
  let σ' := (TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ
  let v := fun i : Fin (p + q + 1) =>
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (p + q) σ τ i) ≫
      CupOne.cup (X ⊗ Y) (p + 1) q (p + q + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X Y) q A)
  calc
    _ = ∑ i, v i := by
      rw [← Category.assoc, NormalizedCapRightInterval.right_simplex_sum, Preadditive.sum_comp]
    _ = ∑ i : Fin (p + 1), pair
        ((TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y p σ' τ i) ≫ T) w := by
      rw [← Fin.sum_congr' v (show (p + 1) + q = p + q + 1 by omega),
        Fin.sum_univ_add (a := p + 1) (b := q)]
      have hz : (∑ i : Fin q, v ((Fin.natAdd (p + 1) i).cast
          (show (p + 1) + q = p + q + 1 by omega))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact late_term_zero X Y p q σ τ _ (by change p < p + 1 + i.val; omega) T A hA
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      exact early_term X Y p q σ τ ((Fin.castAdd q i).cast (by omega)) (by change i.val ≤ p; omega) T A
    _ = pair ((TopCat.toSSet.obj X).ιChainComplex σ' ≫ SingularChainCross.right X Y p 1 τ ≫ T) w := by
      rw [← Category.assoc, NormalizedCapRightInterval.right_simplex_sum, Preadditive.sum_comp, pair_sum]
    _ = _ := by rw [simplex_cup]

theorem right_cup (X Y : TopCat.{0}) (p q : ℕ) (τ : TopCat.toSSet.obj Y _⦋1⦌)
    (T : singularCochainGroup (ZMod 2) (X ⊗ Y) (p + 1))
    (A : singularCochainGroup (ZMod 2) X q)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A) :
    SingularChainCross.right X Y (p + q) 1 τ ≫
      CupOne.cup (X ⊗ Y) (p + 1) q (p + q + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X Y) q A) =
      CupOne.cup X p q (p + q) rfl (SingularChainCross.right X Y p 1 τ ≫ T) A := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  exact right_simplex_cup X Y p q σ τ T A hA

theorem interval_cup (X : TopCat.{0}) (p q : ℕ)
    (T : singularCochainGroup (ZMod 2) (X ⊗ TopCat.I) (p + 1))
    (A : singularCochainGroup (ZMod 2) X q)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A) :
    TimeTriangleSplit.interval X (p + q) ≫
      CupOne.cup (X ⊗ TopCat.I) (p + 1) q (p + q + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) q A) =
      CupOne.cup X p q (p + q) rfl (TimeTriangleSplit.interval X p ≫ T) A :=
  right_cup X TopCat.I p q TimeShuffleComparison.intervalSimplex T A hA

theorem at_degree (X : TopCat.{0}) (p q N : ℕ) (hN : p + q = N)
    (T : singularCochainGroup (ZMod 2) (X ⊗ TopCat.I) (p + 1))
    (A : singularCochainGroup (ZMod 2) X q)
    (hA : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) A) :
    TimeTriangleSplit.interval X N ≫
      CupOne.cup (X ⊗ TopCat.I) (p + 1) q (N + 1) (by omega) T
        (cochainPullback (CartesianMonoidalCategory.fst X TopCat.I) q A) =
      CupOne.cup X p q N hN (TimeTriangleSplit.interval X p ≫ T) A := by
  subst N
  exact interval_cup X p q T A hA

end
end Finsler.IntervalCupRightProjection
