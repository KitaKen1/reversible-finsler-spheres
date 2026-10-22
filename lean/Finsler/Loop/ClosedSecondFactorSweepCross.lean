module

public import Finsler.Loop.ClosedFirstFactorSweepCross
public import Finsler.Loop.SingularHomologyCrossSwap

/-! Move the ACTUAL second-factor closed sweep through the specified
homology cross, using the proved first-factor result and REAL shuffle
symmetry. The true topological braiding/prism square is retained. -/
@[expose] public section
namespace Finsler.ClosedSecondFactorSweepCross
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {Y Y' : TopCat.{0}} {g : Y ⟶ Y'} (H : TopCat.Homotopy g g)

def productHomotopy : TopCat.Homotopy (𝟙 X ⊗ₘ g) (𝟙 X ⊗ₘ g) where
  toFun z := (z.2.1, H (z.1, z.2.2))
  continuous_toFun := by
    have hp : Continuous (fun z : _root_.unitInterval × (X × Y) => (z.1, z.2.2)) :=
      continuous_fst.prodMk continuous_snd.snd
    have hh := H.continuous.comp hp
    exact (continuous_snd.fst.prodMk hh).congr (fun _ => rfl)
  map_zero_left z := by exact Prod.ext rfl (H.map_zero_left z.2)
  map_one_left z := by exact Prod.ext rfl (H.map_one_left z.2)

theorem prism_swap (q : ℕ) :
    (push (β_ X Y).hom).f q ≫
      ((ClosedFirstFactorSweepCross.productHomotopy H X).toSSet.chainComplexMap coeff).hom q (q + 1) =
      ((productHomotopy X H).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        (push (β_ X Y').hom).f (q + 1) := by
  have he : ((ClosedFirstFactorSweepCross.productHomotopy H X).comp
      (TopCat.Homotopy.refl (β_ X Y).hom)).h =
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl (β_ X Y').hom) (productHomotopy X H)).h := by
    apply TopCat.ext
    intro z
    rfl
  exact ((TimePrismNaturality.prism_pre (ClosedFirstFactorSweepCross.productHomotopy H X) (β_ X Y).hom q).trans
    (TimePrismNaturality.prism_congr _ _ he q)).trans
      (TimePrismNaturality.prism_post (productHomotopy X H) (β_ X Y').hom q).symm

theorem homology_swap (q : ℕ) :
    homologyPushZMod2 (β_ X Y).hom q ≫
      SelfHomotopySweep.homology ((ClosedFirstFactorSweepCross.productHomotopy H X).toSSet.chainComplexMap coeff) q =
      SelfHomotopySweep.homology ((productHomotopy X H).toSSet.chainComplexMap coeff) q ≫
        homologyPushZMod2 (β_ X Y').hom (q + 1) :=
  SelfHomotopySweepNaturality.homology ((productHomotopy X H).toSSet.chainComplexMap coeff)
    ((ClosedFirstFactorSweepCross.productHomotopy H X).toSSet.chainComplexMap coeff)
    (push (β_ X Y).hom) (push (β_ X Y').hom) (prism_swap X H) q

theorem cross_value_of_eq (i j N : ℕ) (h : i + j = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) :
    (SelfHomotopySweep.homology ((productHomotopy X H).toSSet.chainComplexMap coeff) N).hom
      (FilteredBilinearLoopProduct.cross X Y i j N h x y) =
      FilteredBilinearLoopProduct.cross X Y' i (j + 1) (N + 1) (by omega)
        x ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) j).hom y) := by
  have : IsIso (homologyPushZMod2 (β_ X Y').hom (N + 1)) := by
    change IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (N + 1)).obj coeff).map (β_ X Y').hom)
    infer_instance
  have hi : Function.Injective (homologyPushZMod2 (β_ X Y').hom (N + 1)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  have he := ConcreteCategory.congr_hom (homology_swap X H N)
    (FilteredBilinearLoopProduct.cross X Y i j N h x y)
  have hx : (homologyPushZMod2 (β_ X Y).hom N).hom
      (FilteredBilinearLoopProduct.cross X Y i j N h x y) =
      FilteredBilinearLoopProduct.cross Y X j i N (by omega) y x :=
    SingularHomologyCrossSwap.value X Y i j N h x y
  change (SelfHomotopySweep.homology ((ClosedFirstFactorSweepCross.productHomotopy H X).toSSet.chainComplexMap coeff) N).hom
    ((homologyPushZMod2 (β_ X Y).hom N).hom (FilteredBilinearLoopProduct.cross X Y i j N h x y)) = _ at he
  rw [hx, ClosedFirstFactorSweepCross.cross_value_of_eq H X j i N (by omega)] at he
  exact he.symm.trans (SingularHomologyCrossSwap.value X Y' i (j + 1) (N + 1) (by omega)
    x ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) j).hom y)).symm

end
end Finsler.ClosedSecondFactorSweepCross
