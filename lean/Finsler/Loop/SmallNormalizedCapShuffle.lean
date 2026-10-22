module

public import Finsler.Loop.NormalizedCapShuffleTensor
public import Finsler.Topology.SmallRectangleCross

/-! The normalized cap/shuffle identity in the actual factorwise
small product target. Only chain inclusion monicity is cancelled. -/

@[expose] public section
namespace Finsler.SmallNormalizedCapShuffle

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SmallRectangleShuffle
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {X Y : TopCat.{0}} {ι κ : Type} (U : ι → Set X) (V : κ → Set Y)

def component (p j : ℕ) : (small X U).X p ⊗ (small Y V).X j ⟶
    (small (X ⊗ Y) (rectangles U V)).X (p + j) :=
  ιTensorObj (small X U) (small Y V) p j (p + j) rfl ≫ (SmallRectangleCross.cross U V).f (p + j)

theorem component_inclusion (p j : ℕ) :
    component U V p j ≫ (inclusion (X ⊗ Y) (rectangles U V)).f (p + j) =
      ((inclusion X U).f p ⊗ₘ (inclusion Y V).f j) ≫ SingularChainCross.component X Y p j := by
  dsimp only [component]
  rw [Category.assoc, ← HomologicalComplex.comp_f, SmallRectangleCross.cross_inclusion]
  simp only [HomologicalComplex.comp_f]
  have hi : ιTensorObj (small X U) (small Y V) p j (p + j) rfl ≫
      (inclusion X U ⊗ₘ inclusion Y V).f (p + j) =
    ((inclusion X U).f p ⊗ₘ (inclusion Y V).f j) ≫
      ιTensorObj (chains X) (chains Y) p j (p + j) rfl := by
    rw [HomologicalComplex.tensorHom_eq_mapBifunctorMap]
    exact HomologicalComplex.ι_tensorHom (inclusion X U) (inclusion Y V) p j (p + j) rfl
  rw [← Category.assoc, hi]
  simp only [SingularChainCross.component, SmallRectangleCross.ambient,
    HomologicalComplex.comp_f, Category.assoc]

theorem component_cap (a p j : ℕ) (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    component U V (a + p) j ≫ SmallCapCarrier.smallCap (X ⊗ Y) (rectangles U V)
      a (p + j) ((a + p) + j) (by omega) (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) =
    (SmallCapCarrier.smallCap X U a p (a + p) rfl φ ▷ (small Y V).X j) ≫ component U V p j := by
  haveI : Mono ((inclusion (X ⊗ Y) (rectangles U V)).f (p + j)) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      (((X ⊗ Y).smallSingularSubcomplex (rectangles U V)).ι.app (Opposite.op ⦋p + j⦌))))
  apply (cancel_mono ((inclusion (X ⊗ Y) (rectangles U V)).f (p + j))).mp
  rw [Category.assoc, SmallCapCarrier.smallCap_inclusion, ← Category.assoc,
    component_inclusion U V (a + p) j, Category.assoc, NormalizedCapShuffleTensor.component_cap X Y a p j φ hφ]
  have ht : ((inclusion X U).f (a + p) ⊗ₘ (inclusion Y V).f j) ≫
      (absoluteChain X a p (a + p) rfl φ ▷ (chains Y).X j) =
    (SmallCapCarrier.smallCap X U a p (a + p) rfl φ ▷ (small Y V).X j) ≫
      ((inclusion X U).f p ⊗ₘ (inclusion Y V).f j) := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
    rw [SmallCapCarrier.smallCap_inclusion]
  rw [← Category.assoc, ht]
  rw [Category.assoc, Category.assoc, component_inclusion U V p j]

end
end Finsler.SmallNormalizedCapShuffle
