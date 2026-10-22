module

public import Finsler.Topology.SmallCrossNaturality

/-! Component naturality of the actual singular shuffle cross with
its real coefficient multiplication. -/

@[expose] public section
namespace Finsler.SingularCrossComponentNaturality

open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem component {X Y X' Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) :
    ((push f).f p ⊗ₘ (push g).f q) ≫ SingularChainCross.component X' Y' p q =
      SingularChainCross.component X Y p q ≫ (push (f ⊗ₘ g)).f (p + q) := by
  have hn := congrArg (fun h => ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫ h.f (p + q))
    (SmallCrossNaturality.ambient_naturality f g)
  have hi : ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫ (push f ⊗ₘ push g).f (p + q) =
      ((push f).f p ⊗ₘ (push g).f q) ≫ ιTensorObj (chains X') (chains Y') p q (p + q) rfl := by
    rw [HomologicalComplex.tensorHom_eq_mapBifunctorMap]
    exact HomologicalComplex.ι_tensorHom (push f) (push g) p q (p + q) rfl
  simp only [HomologicalComplex.comp_f] at hn
  rw [← Category.assoc, hi] at hn
  simpa only [SingularChainCross.component, SmallRectangleCross.ambient,
    HomologicalComplex.comp_f, Category.assoc] using hn

theorem right_identity {X X' Y : TopCat.{0}} (f : X ⟶ X') (p q : ℕ) :
    ((push f).f p ⊗ₘ 𝟙 ((chains Y).X q)) ≫ SingularChainCross.component X' Y p q =
      SingularChainCross.component X Y p q ≫ (push (f ⊗ₘ 𝟙 Y)).f (p + q) := by
  have hi : push (𝟙 Y) = 𝟙 (chains Y) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 Y)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simpa only [hi, HomologicalComplex.id_f] using component f (𝟙 Y) p q

end
end Finsler.SingularCrossComponentNaturality
