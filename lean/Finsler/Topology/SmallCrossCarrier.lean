module

public import Finsler.Topology.SmallRectangleCross

/-! The genuine coefficient-multiplied cross of two carried chains is
carried by the product family. This applies to arbitrary chains, including
the actual subdivision prisms, rather than only simplex generators. -/

@[expose] public section
namespace Finsler.SmallCrossCarrier

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti
open Finsler.SmallRectangleShuffle Finsler.SmallRectangleCross
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)

theorem component_inclusion (p q : ℕ) :
    (ιTensorObj (small X U) (small Y V) p q (p + q) rfl ≫ (cross U V).f (p + q)) ≫
        (inclusion (X ⊗ Y) (rectangles U V)).f (p + q) =
      ((inclusion X U).f p ⊗ₘ (inclusion Y V).f q) ≫ SingularChainCross.component X Y p q := by
  have h := congrArg (fun f =>
    ιTensorObj (small X U) (small Y V) p q (p + q) rfl ≫ f.f (p + q))
    (cross_inclusion U V)
  simpa only [HomologicalComplex.comp_f, Category.assoc, tensorHom_eq_mapBifunctorMap,
    ι_tensorHom, ι_tensorHom_assoc, SingularChainCross.component, ambient] using h

theorem cross_preserves (p q : ℕ)
    {c : coeff ⟶ (chains X).X p} {d : coeff ⟶ (chains Y).X q}
    (hc : c ∈ supported X U p) (hd : d ∈ supported Y V q) :
    (λ_ coeff).inv ≫ (c ⊗ₘ d) ≫ SingularChainCross.component X Y p q ∈
      supported (X ⊗ Y) (rectangles U V) (p + q) := by
  obtain ⟨a, ha⟩ := (mem_smallSingularChains_iff _).mp hc
  obtain ⟨b, hb⟩ := (mem_smallSingularChains_iff _).mp hd
  refine (mem_smallSingularChains_iff _).mpr
    ⟨(λ_ coeff).inv ≫ (a ⊗ₘ b) ≫
      ιTensorObj (small X U) (small Y V) p q (p + q) rfl ≫ (cross U V).f (p + q), ?_⟩
  have ht : (a ⊗ₘ b) ≫ ((inclusion X U).f p ⊗ₘ (inclusion Y V).f q) = c ⊗ₘ d := by
    rw [tensorHom_comp_tensorHom, ha, hb]
  calc
    _ = (λ_ coeff).inv ≫ ((a ⊗ₘ b) ≫ ((inclusion X U).f p ⊗ₘ (inclusion Y V).f q)) ≫
        SingularChainCross.component X Y p q := by
      have h := component_inclusion U V p q
      simpa only [Category.assoc] using congrArg (fun f => (λ_ coeff).inv ≫ (a ⊗ₘ b) ≫ f) h
    _ = _ := by rw [ht]

theorem cross_parent (p q : ℕ) (σ : TopCat.toSSet.obj X _⦋p⦌)
    (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (λ_ coeff).inv ≫ ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
      (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ SingularChainCross.component X Y p q ∈
        supported (X ⊗ Y) (rectangles (parentFamily σ) (parentFamily τ)) (p + q) :=
  cross_preserves (parentFamily σ) (parentFamily τ) p q (simplex_parent σ) (simplex_parent τ)

end
end Finsler.SmallCrossCarrier
