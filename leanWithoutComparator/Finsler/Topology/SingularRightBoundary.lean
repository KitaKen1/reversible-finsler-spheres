module

public import Finsler.Topology.SingularChainCross
public import TauCeti.Algebra.Homology.Monoidal.TensorDifferential

/-! Insert an actual chain in the right shuffle factor. On genuine source
cycles its boundary is exactly insertion of that chain's boundary. The
coefficient multiplication and output/source degree zero are retained. -/

@[expose] public section
namespace Finsler.SingularRightBoundary

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

private theorem cycles_d₁ (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (p i j : ℕ) :
    (C.iCycles p ▷ D.X i) ≫ mapBifunctor.d₁ C D (curriedTensor _) (ComplexShape.down ℕ) p i j = 0 := by
  by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
  · simp [mapBifunctor.d₁_eq' _ _ _ _ hp, ← comp_whiskerRight_assoc]
  · simp [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp]

theorem tensor_cycles_boundary (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (p q : ℕ) (c : coeff ⟶ D.X (q + 1)) :
    ((C.iCycles p ⊗ₘ c) ≫ ιTensorObj C D p (q + 1) (p + q + 1) (by omega)) ≫
        (HomologicalComplex.tensorObj C D).d (p + q + 1) (p + q) =
      (C.iCycles p ⊗ₘ (c ≫ D.d (q + 1) q)) ≫ ιTensorObj C D p q (p + q) rfl := by
  have h₁ : ((C.iCycles p ⊗ₘ c) ≫ ιTensorObj C D p (q + 1) (p + q + 1) (by omega)) ≫
      mapBifunctor.D₁ C D (curriedTensor _) (ComplexShape.down ℕ) (p + q + 1) (p + q) = 0 := by
    rw [Category.assoc, mapBifunctor.ι_D₁, tensorHom_def', Category.assoc, cycles_d₁, comp_zero]
  have h₂ : ((C.iCycles p ⊗ₘ c) ≫ ιTensorObj C D p (q + 1) (p + q + 1) (by omega)) ≫
      mapBifunctor.D₂ C D (curriedTensor _) (ComplexShape.down ℕ) (p + q + 1) (p + q) =
      (C.iCycles p ⊗ₘ (c ≫ D.d (q + 1) q)) ≫ ιTensorObj C D p q (p + q) rfl := by
    rw [Category.assoc, ChainComplex.ιTensorObj_D₂_succ, sign_smul, ← Category.assoc]
    congr 1
    simp only [tensorHom_def, Category.assoc, ← whiskerLeft_comp]
  rw [mapBifunctor.d_eq, Preadditive.comp_add, h₁, zero_add, h₂]

def shuffle (X Y : TopCat.{0}) : HomologicalComplex.tensorObj (chains X) (chains Y) ⟶ chains (X ⊗ Y) :=
  TopCat.shuffle X Y coeff coeff ≫
    SingularChainCross.coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom

def rightChain (X Y : TopCat.{0}) (p q : ℕ) (c : coeff ⟶ (chains Y).X q) :
    (chains X).X p ⟶ (chains (X ⊗ Y)).X (p + q) :=
  (ρ_ ((chains X).X p)).inv ≫ (((chains X).X p) ◁ c) ≫
    ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫ (shuffle X Y).f (p + q)

theorem rightChain_simplex (X Y : TopCat.{0}) (p q : ℕ)
    (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    rightChain X Y p q ((TopCat.toSSet.obj Y).ιChainComplex τ) = SingularChainCross.right X Y p q τ := by
  simp only [rightChain, SingularChainCross.right, SingularChainCross.component,
    shuffle, HomologicalComplex.comp_f]

theorem rightChain_add (X Y : TopCat.{0}) (p q : ℕ) (a b : coeff ⟶ (chains Y).X q) :
    rightChain X Y p q (a + b) = rightChain X Y p q a + rightChain X Y p q b := by
  simp only [rightChain, MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add, Preadditive.add_comp]

theorem cycles_rightChain (X Y : TopCat.{0}) (p q : ℕ) (c : coeff ⟶ (chains Y).X q) :
    (chains X).iCycles p ≫ rightChain X Y p q c =
      (ρ_ ((chains X).cycles p)).inv ≫ ((chains X).iCycles p ⊗ₘ c) ≫
        ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫ (shuffle X Y).f (p + q) := by
  unfold rightChain
  rw [← Category.assoc, rightUnitor_inv_naturality]
  simp only [tensorHom_def, Category.assoc]

theorem rightChain_boundary (X Y : TopCat.{0}) (p q : ℕ) (c : coeff ⟶ (chains Y).X (q + 1)) :
    ((chains X).iCycles p ≫ rightChain X Y p (q + 1) c) ≫
        (chains (X ⊗ Y)).d (p + q + 1) (p + q) =
      (chains X).iCycles p ≫ rightChain X Y p q (c ≫ (chains Y).d (q + 1) q) := by
  rw [cycles_rightChain, cycles_rightChain]
  have hi : ιTensorObj (chains X) (chains Y) p (q + 1) (p + (q + 1)) rfl =
      ιTensorObj (chains X) (chains Y) p (q + 1) (p + q + 1) (by omega) := by
    rfl
  have hc := tensor_cycles_boundary (chains X) (chains Y) p q c
  have hs : (shuffle X Y).f (p + (q + 1)) ≫
      (chains (X ⊗ Y)).d (p + q + 1) (p + q) =
      (HomologicalComplex.tensorObj (chains X) (chains Y)).d (p + q + 1) (p + q) ≫
        (shuffle X Y).f (p + q) := (shuffle X Y).comm _ _
  simp only [Category.assoc]
  rw [hs, hi]
  simpa only [Category.assoc] using congrArg
    (fun t => (ρ_ ((chains X).cycles p)).inv ≫ t ≫ (shuffle X Y).f (p + q)) hc

end
end Finsler.SingularRightBoundary
