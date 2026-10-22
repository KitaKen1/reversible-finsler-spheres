module

public import Finsler.Topology.SingularNormalization

/-! Naturality of the SAME mathlib normalization homotopy, including
its actual cochain primitive. Thus normalization corrections retain
literal zero on every actual carrier, not merely a zero coboundary. -/
@[expose] public section
namespace Finsler.NormalizationPrimitiveNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open scoped Simplicial DoldKan
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem finite_natural {C : Type*} [Category* C] [Preadditive C]
    {X Y : SimplicialObject C} (f : X ⟶ Y) (q n : ℕ) :
    f.app (Opposite.op ⦋n⦌) ≫ (DoldKan.homotopyPToId Y q).hom n (n + 1) =
      (DoldKan.homotopyPToId X q).hom n (n + 1) ≫ f.app (Opposite.op ⦋n + 1⦌) := by
  induction q with
  | zero => simp [DoldKan.homotopyPToId]
  | succ q ih =>
    simp only [DoldKan.homotopyPToId, Homotopy.trans_hom, Homotopy.ofEq_hom,
      Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, zero_add, add_zero,
      DoldKan.homotopyHσToZero, Homotopy.nullHomotopy'_hom,
      ComplexShape.down_Rel, dite_true, Preadditive.comp_add, Preadditive.add_comp]
    rw [ih, ← Category.assoc, DoldKan.P_f_naturality, Category.assoc,
      DoldKan.hσ'_naturality, ← Category.assoc]

theorem homotopy_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (push f).f n ≫ (SingularNormalization.projectorHomotopy Y).hom n (n + 1) =
      (SingularNormalization.projectorHomotopy X).hom n (n + 1) ≫ (push f).f (n + 1) := by
  unfold SingularNormalization.projectorHomotopy
  simp only [DoldKan.homotopyPInftyToId_hom]
  change (SingularNormalization.linearMap f).app (Opposite.op ⦋n⦌) ≫ _ =
    _ ≫ (SingularNormalization.linearMap f).app (Opposite.op ⦋n + 1⦌)
  exact finite_natural (SingularNormalization.linearMap f) (n + 1 + 1) n

theorem primitive_zero (X : TopCat.{0}) (n : ℕ) : SingularNormalization.primitive X n 0 = 0 :=
  comp_zero

theorem primitive_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (n + 1)) :
    cochainPullback f n (SingularNormalization.primitive Y n φ) =
      SingularNormalization.primitive X n (cochainPullback f (n + 1) φ) := by
  change (push f).f n ≫ ((SingularNormalization.projectorHomotopy Y).hom n (n + 1) ≫ φ) =
    (SingularNormalization.projectorHomotopy X).hom n (n + 1) ≫ ((push f).f (n + 1) ≫ φ)
  rw [← Category.assoc, homotopy_natural, Category.assoc]

theorem primitive_supported {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (n + 1)) (hf : cochainPullback f (n + 1) φ = 0) :
    cochainPullback f n (SingularNormalization.primitive Y n φ) = 0 := by
  rw [primitive_natural, hf, primitive_zero]

end
end Finsler.NormalizationPrimitiveNaturality
