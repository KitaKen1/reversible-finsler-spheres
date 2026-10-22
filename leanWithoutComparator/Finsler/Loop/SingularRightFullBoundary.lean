module

public import Finsler.Topology.SingularRightNaturality

/-! FULL source-boundary formula for inserting a genuine singular
2-chain. The source need NOT be a cycle: retain its actual boundary.
This is needed when a moving cut-time triangle acts on the original
northern ROTATION PRISM, whose endpoints cannot silently be dropped. -/
@[expose] public section
namespace Finsler.SingularRightFullBoundary
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

theorem tensor_boundary_two (C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ) :
    ιTensorObj C D (p + 1) 2 (p + 3) rfl ≫ (HomologicalComplex.tensorObj C D).d (p + 3) (p + 2) =
      (C.d (p + 1) p ▷ D.X 2) ≫ ιTensorObj C D p 2 (p + 2) rfl +
      (C.X (p + 1) ◁ D.d 2 1) ≫ ιTensorObj C D (p + 1) 1 (p + 2) rfl := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add, ChainComplex.ιTensorObj_D₁_succ,
    ChainComplex.ιTensorObj_D₂_succ, sign_smul]

theorem insertion_natural {A B D : ModuleCat.{0} (ZMod 2)} (f : A ⟶ B) (c : coeff ⟶ D) :
    (ρ_ A).inv ≫ (A ◁ c) ≫ (f ▷ D) = f ≫ (ρ_ B).inv ≫ (B ◁ c) := by
  calc
    _ = (ρ_ A).inv ≫ (f ⊗ₘ c) := by rw [tensorHom_def']
    _ = ((ρ_ A).inv ≫ (f ▷ coeff)) ≫ (B ◁ c) := by
      rw [tensorHom_def, Category.assoc]
      rfl
    _ = (f ≫ (ρ_ B).inv) ≫ (B ◁ c) :=
      congrArg (fun h => h ≫ (B ◁ c)) (rightUnitor_inv_naturality f).symm
    _ = _ := Category.assoc _ _ _

theorem rightChain_boundary_two (X Y : TopCat.{0}) (p : ℕ) (c : coeff ⟶ (chains Y).X 2) :
    SingularRightBoundary.rightChain X Y (p + 1) 2 c ≫ (chains (X ⊗ Y)).d (p + 3) (p + 2) =
      (chains X).d (p + 1) p ≫ SingularRightBoundary.rightChain X Y p 2 c +
      SingularRightBoundary.rightChain X Y (p + 1) 1 (c ≫ (chains Y).d 2 1) := by
  unfold SingularRightBoundary.rightChain
  have hs : (SingularRightBoundary.shuffle X Y).f (p + 3) ≫
      (chains (X ⊗ Y)).d (p + 3) (p + 2) =
      (HomologicalComplex.tensorObj (chains X) (chains Y)).d (p + 3) (p + 2) ≫
        (SingularRightBoundary.shuffle X Y).f (p + 2) := (SingularRightBoundary.shuffle X Y).comm _ _
  simp only [Category.assoc]
  rw [hs]
  have ht := congrArg (fun h => (ρ_ ((chains X).X (p + 1))).inv ≫
    (((chains X).X (p + 1)) ◁ c) ≫ h ≫ (SingularRightBoundary.shuffle X Y).f (p + 2))
    (tensor_boundary_two (chains X) (chains Y) p)
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc] at ht
  apply ht.trans
  apply congrArg₂ (fun a b => a + b)
  · simpa only [Category.assoc] using congrArg (fun h => h ≫
      ιTensorObj (chains X) (chains Y) p 2 (p + 2) rfl ≫ (SingularRightBoundary.shuffle X Y).f (p + 2))
      (insertion_natural ((chains X).d (p + 1) p) c)
  · simp only [whiskerLeft_comp, Category.assoc]

end
end Finsler.SingularRightFullBoundary
