module

public import Finsler.Loop.MappedShuffleWordCap
public import Finsler.Loop.ShuffleWordChain
public import Finsler.Loop.ShuffleWordPrefixSum

/-! A normalized first-factor cochain commutes exactly with the
actual singular cross with an arbitrary right-hand simplex. The proof
uses TauCeti's real shuffle sum and its surviving horizontal prefix. -/

@[expose] public section
namespace Finsler.NormalizedCapShuffle

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MappedShuffleWordCap Finsler.ShuffleWords
open scoped Simplicial DoldKan BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem bad_cap_zero (X Y : TopCat.{0}) (a p j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool)
    (hw : w.take a ≠ List.replicate a false)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (a + p) j ((a + p) + j) σ τ w) ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) = 0 := by
  rw [SmallCapCarrier.cap_simplex]
  have hz : SmallCapCarrier.weight (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
      (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)
        (simplex X Y (a + p) j ((a + p) + j) σ τ w) = 0 := by
    dsimp only [SmallCapCarrier.weight]
    rw [bad_coefficient_zero X Y (a + p) j ((a + p) + j) a (by omega) σ τ w hw φ hφ,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
  rw [hz, zero_comp]

theorem prefix_cap (X Y : TopCat.{0}) (a p j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) (w : List Bool)
    (φ : singularCochainGroup (ZMod 2) X a) :
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
      (simplex X Y (a + p) j ((a + p) + j) σ τ (List.replicate a false ++ w)) ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
    SmallCapCarrier.weight X a p (a + p) rfl φ σ ≫
      (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
        (simplex X Y p j (p + j)
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval a p (by omega)).op σ) τ w) := by
  rw [SmallCapCarrier.cap_simplex, prefix_tail X Y a p j σ τ w]
  congr 1
  dsimp only [SmallCapCarrier.weight]
  rw [prefix_coefficient X Y a p j ((a + p) + j) (by omega) σ τ w φ]

theorem right_simplex_sum (X Y : TopCat.{0}) (p j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ SingularChainCross.right X Y p j τ =
      ∑ w ∈ words p j, (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y p j (p + j) σ τ w) := by
  rw [SingularChainCross.right_simplex, ShuffleWordChain.shuffle_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  rw [SSet.ι_chainComplexMap_f]
  rfl

theorem cap_right_simplex (X Y : TopCat.{0}) (a p j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋a + p⦌) (τ : TopCat.toSSet.obj Y _⦋j⦌)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ SingularChainCross.right X Y (a + p) j τ ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a p (a + p) rfl φ ≫
      SingularChainCross.right X Y p j τ := by
  let v : List Bool → (coeff ⟶ (chains (X ⊗ Y)).X (p + j)) := fun w =>
    (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex (simplex X Y (a + p) j ((a + p) + j) σ τ w) ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)
  let wt := SmallCapCarrier.weight X a p (a + p) rfl φ σ
  let σ' := (TopCat.toSSet.obj X).map (SimplexCategory.subinterval a p (by omega)).op σ
  calc
    _ = ∑ w ∈ words (a + p) j, v w := by
      rw [← Category.assoc, right_simplex_sum, Preadditive.sum_comp]
    _ = ∑ w ∈ words p j, v (List.replicate a false ++ w) :=
      ShuffleWordPrefixSum.sum_prefix a p j v (fun w hw => bad_cap_zero X Y a p j σ τ w hw φ hφ)
    _ = ∑ w ∈ words p j, wt ≫ (TopCat.toSSet.obj (X ⊗ Y)).ιChainComplex
        (simplex X Y p j (p + j) σ' τ w) := by
      apply Finset.sum_congr rfl
      intro w _
      exact prefix_cap X Y a p j σ τ w φ
    _ = wt ≫ ((TopCat.toSSet.obj X).ιChainComplex σ' ≫ SingularChainCross.right X Y p j τ) := by
      rw [right_simplex_sum, Preadditive.comp_sum]
    _ = _ := by
      symm
      rw [← Category.assoc, SmallCapCarrier.cap_simplex, Category.assoc]

theorem right_cap (X Y : TopCat.{0}) (a p j : ℕ)
    (τ : TopCat.toSSet.obj Y _⦋j⦌) (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    SingularChainCross.right X Y (a + p) j τ ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
    absoluteChain X a p (a + p) rfl φ ≫ SingularChainCross.right X Y p j τ := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) (R := coeff)
  intro σ
  simpa only [Category.assoc] using cap_right_simplex X Y a p j σ τ φ hφ

end
end Finsler.NormalizedCapShuffle
