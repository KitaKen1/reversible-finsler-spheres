module

public import Finsler.Loop.PrismCupEndpointFaces
public import Finsler.Loop.IntervalCupRightProjection

/-! Exact ordinary-cup Leibniz formula for the genuine topological prism
in characteristic two. BOTH endpoint factors appear. The proof sums all
actual AW front/tail terms, without closure or normalization premises. -/
@[expose] public section
namespace Finsler.PrismCupLeibniz
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.IntervalCupRightProjection (pair simplex_cup pair_sum)
open Finsler.PrismCupEndpointFaces
open scoped Simplicial BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem pair_sum_right {J : Type*} (s : Finset J) (u : coeff ⟶ coeff) (v : J → (coeff ⟶ coeff)) :
    pair u (∑ j ∈ s, v j) = ∑ j ∈ s, pair u (v j) := by
  simp only [IntervalCupRightProjection.pair, tensor_sum, Preadditive.sum_comp, Preadditive.comp_sum]

theorem endpoint_eval {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) (T : singularCochainGroup (ZMod 2) Y n) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ cochainPullback f n T =
      (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map f).app _ σ) ≫ T := by
  change _ ≫ ((SSet.chainComplexMap (TopCat.toSSet.map f) coeff).f n ≫ T) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]

theorem prism_sum {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (H.toSSet.chainComplexMap coeff).hom n (n + 1) =
      ∑ i : Fin (n + 1), (TopCat.toSSet.obj Y).ιChainComplex (simplex H.toSSet n σ i) := by
  rw [PrismRectangle.prism_simplex, PrismShuffle.shuffle_one, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [SSet.ι_chainComplexMap_f]
  rfl

variable {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
  (p q N : ℕ) (hN : (p + 1) + q = N)
  (A : singularCochainGroup (ZMod 2) Y (p + 1))
  (B : singularCochainGroup (ZMod 2) Y (q + 1))

theorem early_term (σ : TopCat.toSSet.obj X _⦋N⦌) (i : Fin (N + 1)) (hi : i.val ≤ p) :
    (TopCat.toSSet.obj Y).ιChainComplex (simplex H.toSSet N σ i) ≫
      CupOne.cup Y (p + 1) (q + 1) (N + 1) (by omega) A B =
    pair ((TopCat.toSSet.obj Y).ιChainComplex
      (simplex H.toSSet p ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ)
        ⟨i.val, by omega⟩) ≫ A)
      ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p (q + 1) (by omega)).op σ) ≫ cochainPullback g (q + 1) B) := by
  rw [simplex_cup, early_front H.toSSet p (q + 1) N (by omega) σ i hi,
    early_tail H.toSSet p (q + 1) N (by omega) σ i hi, endpoint_eval]

theorem late_term (σ : TopCat.toSSet.obj X _⦋N⦌) (i : Fin (N + 1)) (hi : p + 1 ≤ i.val) :
    (TopCat.toSSet.obj Y).ιChainComplex (simplex H.toSSet N σ i) ≫
      CupOne.cup Y (p + 1) (q + 1) (N + 1) (by omega) A B =
    pair ((TopCat.toSSet.obj X).ιChainComplex
      ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 (p + 1) (by omega)).op σ) ≫ cochainPullback f (p + 1) A)
      ((TopCat.toSSet.obj Y).ιChainComplex
        (simplex H.toSSet q ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval (p + 1) q (by omega)).op σ)
          ⟨i.val - (p + 1), by omega⟩) ≫ B) := by
  rw [simplex_cup, late_front H.toSSet (p + 1) q N hN σ i hi,
    late_tail H.toSSet (p + 1) q N hN σ i hi, endpoint_eval]

theorem simplex_formula (σ : TopCat.toSSet.obj X _⦋N⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (H.toSSet.chainComplexMap coeff).hom N (N + 1) ≫
      CupOne.cup Y (p + 1) (q + 1) (N + 1) (by omega) A B =
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (CupOne.cup X p (q + 1) N (by omega) ((H.toSSet.chainComplexMap coeff).hom p (p + 1) ≫ A)
        (cochainPullback g (q + 1) B) +
      CupOne.cup X (p + 1) q N hN (cochainPullback f (p + 1) A)
        ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ B)) := by
  let v := fun i : Fin (N + 1) => (TopCat.toSSet.obj Y).ιChainComplex (simplex H.toSSet N σ i) ≫
    CupOne.cup Y (p + 1) (q + 1) (N + 1) (by omega) A B
  rw [← Category.assoc, prism_sum, Preadditive.sum_comp]
  change (∑ i, v i) = _
  rw [← Fin.sum_congr' v (show (p + 1) + (q + 1) = N + 1 by omega), Fin.sum_univ_add]
  rw [Preadditive.comp_add, simplex_cup, simplex_cup]
  rw [← Category.assoc, prism_sum, Preadditive.sum_comp, pair_sum]
  rw [← Category.assoc, prism_sum, Preadditive.sum_comp, pair_sum_right]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact early_term H p q N hN A B σ ((Fin.castAdd (q + 1) i).cast (by omega)) (by change i.val ≤ p; omega)
  · apply Finset.sum_congr rfl
    intro i _
    have he : ((Fin.natAdd (p + 1) i).cast (show (p + 1) + (q + 1) = N + 1 by omega)).val - (p + 1) = i.val := by
      change p + 1 + i.val - (p + 1) = i.val
      omega
    simpa only [he] using late_term H p q N hN A B σ
      ((Fin.natAdd (p + 1) i).cast (by omega)) (by change p + 1 ≤ p + 1 + i.val; omega)

theorem formula : (H.toSSet.chainComplexMap coeff).hom N (N + 1) ≫
    CupOne.cup Y (p + 1) (q + 1) (N + 1) (by omega) A B =
    CupOne.cup X p (q + 1) N (by omega) ((H.toSSet.chainComplexMap coeff).hom p (p + 1) ≫ A)
      (cochainPullback g (q + 1) B) +
    CupOne.cup X (p + 1) q N hN (cochainPullback f (p + 1) A)
      ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ B) := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  exact simplex_formula H p q N hN A B σ

end
end Finsler.PrismCupLeibniz
