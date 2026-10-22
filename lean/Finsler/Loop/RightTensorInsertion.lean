module

public import Finsler.Loop.SingularRightFullBoundary

/-! Insert an actual right-factor chain before the shuffle. Its full
tensor differential retains BOTH the source and inserted-chain boundary.
The actual coefficient unitor and tensor degree inclusions are kept. -/
@[expose] public section
namespace Finsler.RightTensorInsertion
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def insert (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p q : ℕ) (c : coeff ⟶ D.X q) :
    C.X p ⟶ (C ⊗ D).X (p + q) :=
  (ρ_ (C.X p)).inv ≫ (C.X p ◁ c) ≫ ιTensorObj C D p q (p + q) rfl

theorem tensor_boundary_one (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ) :
    ιTensorObj C D (p + 1) 1 (p + 2) rfl ≫ (C ⊗ D).d (p + 2) (p + 1) =
      (C.d (p + 1) p ▷ D.X 1) ≫ ιTensorObj C D p 1 (p + 1) rfl +
      (C.X (p + 1) ◁ D.d 1 0) ≫ ιTensorObj C D (p + 1) 0 (p + 1) rfl := by
  change ιTensorObj C D (p + 1) 1 (p + 2) rfl ≫
    (HomologicalComplex.tensorObj C D).d (p + 2) (p + 1) = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, ChainComplex.ιTensorObj_D₁_succ,
    ChainComplex.ιTensorObj_D₂_succ, SingularRightFullBoundary.sign_smul]

theorem boundary_one (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ) (c : coeff ⟶ D.X 1) :
    insert C D (p + 1) 1 c ≫ (C ⊗ D).d (p + 2) (p + 1) =
      C.d (p + 1) p ≫ insert C D p 1 c + insert C D (p + 1) 0 (c ≫ D.d 1 0) := by
  unfold insert
  simp only [Category.assoc]
  rw [tensor_boundary_one]
  simp only [Preadditive.comp_add]
  apply congrArg₂ (fun a b => a + b)
  · simpa only [Category.assoc] using congrArg (fun h => h ≫ ιTensorObj C D p 1 (p + 1) rfl)
      (SingularRightFullBoundary.insertion_natural (C.d (p + 1) p) c)
  · simp only [whiskerLeft_comp, Category.assoc]

theorem naturality (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    {D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : D ⟶ E) (p q : ℕ) (c : coeff ⟶ D.X q) :
    insert C D p q c ≫ (𝟙 C ⊗ₘ f).f (p + q) = insert C E p q (c ≫ f.f q) := by
  unfold insert
  simp only [Category.assoc]
  have hi : ιTensorObj C D p q (p + q) rfl ≫ (𝟙 C ⊗ₘ f).f (p + q) =
      ((𝟙 C : C ⟶ C).f p ⊗ₘ f.f q) ≫ ιTensorObj C E p q (p + q) rfl :=
    HomologicalComplex.ι_tensorHom (𝟙 C) f p q (p + q) rfl
  rw [hi]
  simp only [HomologicalComplex.id_f, id_tensorHom, ← whiskerLeft_comp_assoc]

theorem add (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p q : ℕ) (a b : coeff ⟶ D.X q) :
    insert C D p q (a + b) = insert C D p q a + insert C D p q b := by
  simp only [insert, MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add, Preadditive.add_comp]

theorem shuffle (X Y : TopCat.{0}) (p q : ℕ) (c : coeff ⟶ (chains Y).X q) :
    insert (chains X) (chains Y) p q c ≫ (SingularRightBoundary.shuffle X Y).f (p + q) =
      SingularRightBoundary.rightChain X Y p q c := by
  simp only [insert, SingularRightBoundary.rightChain, Category.assoc]

end
end Finsler.RightTensorInsertion
