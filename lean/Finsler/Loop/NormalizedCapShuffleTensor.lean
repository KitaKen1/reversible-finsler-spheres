module

public import Finsler.Loop.NormalizedCapShuffle

/-! The actual all-chain tensor cap/shuffle identity, including
coefficient multiplication and arbitrary chains in both input factors. -/

@[expose] public section
namespace Finsler.NormalizedCapShuffleTensor

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem pair_right (X Y : TopCat.{0}) (p j : ℕ)
    (c : coeff ⟶ (chains X).X p) (τ : TopCat.toSSet.obj Y _⦋j⦌) :
    c ≫ SingularChainCross.right X Y p j τ =
      (ρ_ coeff).inv ≫ (c ⊗ₘ (TopCat.toSSet.obj Y).ιChainComplex τ) ≫
        SingularChainCross.component X Y p j := by
  calc
    _ = (c ≫ (ρ_ ((chains X).X p)).inv) ≫
        (((chains X).X p) ◁ (TopCat.toSSet.obj Y).ιChainComplex τ) ≫
          SingularChainCross.component X Y p j := by
      simp only [SingularChainCross.right, Category.assoc]
    _ = _ := by
      rw [rightUnitor_inv_naturality]
      simp only [tensorHom_def, Category.assoc]

theorem component_cap (X Y : TopCat.{0}) (a p j : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    SingularChainCross.component X Y (a + p) j ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
    (absoluteChain X a p (a + p) rfl φ ▷ (chains Y).X j) ≫
      SingularChainCross.component X Y p j := by
  apply SSet.tensorChainComplexX_hom_ext
  intro σ τ
  apply (cancel_epi (ρ_ coeff).inv).mp
  have hp := pair_right X Y (a + p) j ((TopCat.toSSet.obj X).ιChainComplex σ) τ
  have hq := pair_right X Y p j
    ((TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a p (a + p) rfl φ) τ
  have hc := congrArg (fun f => (TopCat.toSSet.obj X).ιChainComplex σ ≫ f)
    (NormalizedCapShuffle.right_cap X Y a p j τ φ hφ)
  have ht : ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ (TopCat.toSSet.obj Y).ιChainComplex τ) ≫
      (absoluteChain X a p (a + p) rfl φ ▷ (chains Y).X j) =
    ((TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a p (a + p) rfl φ) ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  calc
    _ = ((TopCat.toSSet.obj X).ιChainComplex σ ≫ SingularChainCross.right X Y (a + p) j τ) ≫
        absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
          (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫
        absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
          (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ)) hp.symm
    _ = ((TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a p (a + p) rfl φ) ≫
        SingularChainCross.right X Y p j τ := by simpa only [Category.assoc] using hc
    _ = (ρ_ coeff).inv ≫
        (((TopCat.toSSet.obj X).ιChainComplex σ ≫ absoluteChain X a p (a + p) rfl φ) ⊗ₘ
          (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ SingularChainCross.component X Y p j := hq
    _ = _ := by
      rw [← ht]
      simp only [Category.assoc]

theorem chains_cap (X Y : TopCat.{0}) (a p j : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ)
    (x : coeff ⟶ (chains X).X (a + p)) (y : coeff ⟶ (chains Y).X j) :
    (x ⊗ₘ y) ≫ SingularChainCross.component X Y (a + p) j ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
    ((x ≫ absoluteChain X a p (a + p) rfl φ) ⊗ₘ y) ≫ SingularChainCross.component X Y p j := by
  rw [component_cap X Y a p j φ hφ, ← Category.assoc, ← tensorHom_id,
    tensorHom_comp_tensorHom, Category.comp_id]

theorem normalized_component (X Y : TopCat.{0}) (a p j : ℕ)
    (φ : singularCochainGroup (ZMod 2) X a) :
    SingularChainCross.component X Y (a + p) j ≫
      absoluteChain (X ⊗ Y) a (p + j) ((a + p) + j) (by omega)
        (cochainPullback (CartesianMonoidalCategory.fst X Y) a (SingularNormalization.normalize X a φ)) =
    (absoluteChain X a p (a + p) rfl (SingularNormalization.normalize X a φ) ▷ (chains Y).X j) ≫
      SingularChainCross.component X Y p j :=
  component_cap X Y a p j _ (SingularNormalization.normalize_degeneracies X a φ)

end
end Finsler.NormalizedCapShuffleTensor
