module

public import Finsler.Topology.ProductThreeCapVanishing

/-! Recover the second-factor map in the actual bounded target by freezing
the first standard-simplex input at its zero vertex. Only monicity of the
actual simplicial subspace inclusion is used. Ambient homology injectivity
and an independently postulated bounded second-factor map are unnecessary. -/

@[expose] public section
namespace Finsler.BoundedSecondFactorDescent

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

def zeroSection (j k : ℕ) : (Δ[k] : SSet.{0}) ⟶ ((Δ[j] : SSet.{0}) ⊗ Δ[k]) :=
  CartesianMonoidalCategory.lift
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (j + 1)))) (𝟙 _)

theorem section_snd (j k : ℕ) : zeroSection j k ≫ CartesianMonoidalCategory.snd _ _ = 𝟙 _ :=
  CartesianMonoidalCategory.lift_snd _ _

theorem descent_inclusion {M N : SSet.{0}} (j k : ℕ)
    (F : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ M) (i : M ⟶ N)
    (g : (Δ[k] : SSet.{0}) ⟶ N)
    (h : F ≫ i = CartesianMonoidalCategory.snd _ _ ≫ g) :
    (zeroSection j k ≫ F) ≫ i = g := by
  rw [Category.assoc, h, ← Category.assoc, section_snd, Category.id_comp]

theorem factor {M N : SSet.{0}} (j k : ℕ)
    (F : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ M) (i : M ⟶ N) [Mono i]
    (g : (Δ[k] : SSet.{0}) ⟶ N)
    (h : F ≫ i = CartesianMonoidalCategory.snd _ _ ≫ g) :
    F = CartesianMonoidalCategory.snd _ _ ≫ (zeroSection j k ≫ F) := by
  apply (cancel_mono i).mp
  have hh := congrArg (fun G => CartesianMonoidalCategory.snd (Δ[j] : SSet.{0}) Δ[k] ≫ G)
    (descent_inclusion j k F i g h)
  simpa only [Category.assoc] using h.trans hh.symm

theorem bounded_factor (Y : TopCat.{0}) (B : Set Y) (j k : ℕ)
    (F : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (TopCat.of B))
    (g : (Δ[k] : SSet.{0}) ⟶ TopCat.toSSet.obj Y)
    (h : F ≫ TopCat.toSSet.map (SupportedCap.subspaceMap Y B) =
      CartesianMonoidalCategory.snd _ _ ≫ g) :
    F = CartesianMonoidalCategory.snd _ _ ≫ (zeroSection j k ≫ F) := by
  haveI : Mono (SupportedCap.subspaceMap Y B) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact factor j k F (TopCat.toSSet.map (SupportedCap.subspaceMap Y B)) g h

end
end Finsler.BoundedSecondFactorDescent
