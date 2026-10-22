module

public import Finsler.Loop.FirstFactorSingularTimeModelComparison
public import Finsler.Loop.FirstFactorSweepHomologyCross
public import Finsler.Loop.SelfSweepExact
public import Finsler.Loop.SmallCrossHomologyBridge
public import Finsler.Topology.SmallCrossNaturality
public import Finsler.Loop.DoubleClosedSweepProjection

/-! The ORIGINAL ordinary closed homotopy sweep commutes with the
specified singular homology cross in its FIRST factor. The existing
constructed double prism compares product time with tensor time;
actual maps transport its boundary. Shuffle associativity is not
assumed. The formula includes all degrees and real coefficients. -/
@[expose] public section
namespace Finsler.ClosedFirstFactorSweepCross
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.IntervalSobolev
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {X X' : TopCat.{0}} {f : X ⟶ X'} (H : TopCat.Homotopy f f) (Y : TopCat.{0})

def productHomotopy : TopCat.Homotopy (f ⊗ₘ 𝟙 Y) (f ⊗ₘ 𝟙 Y) where
  toFun z := (H (z.1, z.2.1), z.2.2)
  continuous_toFun := by
    have hp : Continuous (fun z : _root_.unitInterval × (X × Y) => (z.1, z.2.1)) :=
      continuous_fst.prodMk continuous_snd.fst
    have hh := H.continuous.comp hp
    exact (hh.prodMk continuous_snd.snd).congr (fun _ => rfl)
  map_zero_left z := by exact Prod.ext (H.map_zero_left z.1) rfl
  map_one_left z := by exact Prod.ext (H.map_one_left z.1) rfl

def modelEvaluation : X ⊗ TopCat.of (ClosedInterval × Y) ⟶ X' ⊗ Y :=
  TopCat.ofHom ⟨fun z => (H (z.2.1, z.1), z.2.2), by
    have hp : Continuous (fun z : X × (ClosedInterval × Y) => (z.2.1, z.1)) :=
      continuous_snd.fst.prodMk continuous_fst
    have hh := H.continuous.comp hp
    exact (hh.prodMk continuous_snd.snd).congr (fun _ => rfl)⟩

theorem product_prism (N : ℕ) :
    ((SingularTimeCylinderMaps.cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) ≫
      (push (modelEvaluation H Y)).f (N + 1) =
        ((productHomotopy H Y).toSSet.chainComplexMap coeff).hom N (N + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (modelEvaluation H Y))
      (SingularTimeCylinderMaps.cylinder X Y)).h = (productHomotopy H Y).h := by
    apply TopCat.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (SingularTimeCylinderMaps.cylinder X Y) (modelEvaluation H Y) N).trans
    (TimePrismNaturality.prism_congr _ _ he N)

theorem evaluation_prism (N : ℕ) :
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).hom N (N + 1) ≫
      (push (DoubleClosedSweepProjection.evaluation H)).f (N + 1) =
        (H.toSSet.chainComplexMap coeff).hom N (N + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (DoubleClosedSweepProjection.evaluation H))
      (AnnularTimeTrim.cylinder X)).h = H.h := by
    apply TopCat.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (AnnularTimeTrim.cylinder X)
    (DoubleClosedSweepProjection.evaluation H) N).trans (TimePrismNaturality.prism_congr _ H he N)

theorem reorder_evaluation : FirstFactorSingularTimeModelComparison.reorder X Y ≫ modelEvaluation H Y =
    DoubleClosedSweepProjection.evaluation H ⊗ₘ 𝟙 Y := by
  apply TopCat.ext
  intro z
  rfl

theorem cross_evaluation :
    FirstFactorSingularTimeModelComparison.cross X Y ≫ push (modelEvaluation H Y) =
      (push (DoubleClosedSweepProjection.evaluation H) ⊗ₘ 𝟙 (chains Y)) ≫ SmallRectangleCross.ambient X' Y := by
  rw [FirstFactorSingularTimeModelComparison.cross, Category.assoc, ← push_comp, reorder_evaluation]
  have he := SmallCrossNaturality.ambient_naturality (DoubleClosedSweepProjection.evaluation H) (𝟙 Y)
  have hid : push (𝟙 Y) = 𝟙 (chains Y) := by
    change ((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map (𝟙 Y) = _
    exact CategoryTheory.Functor.map_id _ _
  simpa only [hid] using he.symm

abbrev tensorPrism := FirstFactorTensorPrismNaturality.prism (H.toSSet.chainComplexMap coeff) (chains Y)

theorem tensor_prism (N : ℕ) :
    (FullFirstFactorTimePrism.prism X Y).hom N (N + 1) ≫
      (push (DoubleClosedSweepProjection.evaluation H) ⊗ₘ 𝟙 (chains Y)).f (N + 1) =
        (tensorPrism H Y).hom N (N + 1) := by
  have he := FirstFactorTensorPrismNaturality.naturality
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) (H.toSSet.chainComplexMap coeff)
    (𝟙 (chains X)) (push (DoubleClosedSweepProjection.evaluation H)) (𝟙 (chains Y))
    (fun k => by rw [HomologicalComplex.id_f, Category.id_comp]; exact (evaluation_prism H k).symm) N
  simpa only [id_tensorHom_id, HomologicalComplex.id_f, Category.id_comp, FullFirstFactorTimePrism.prism] using he.symm

theorem tensor_component (N : ℕ) :
    (FullFirstFactorTimePrism.prism X Y).hom N (N + 1) ≫
      (FirstFactorSingularTimeModelComparison.cross X Y).f (N + 1) ≫
        (push (modelEvaluation H Y)).f (N + 1) =
      (tensorPrism H Y).hom N (N + 1) ≫ (SmallRectangleCross.ambient X' Y).f (N + 1) := by
  have hc := congrArg (fun a => a.f (N + 1)) (cross_evaluation H Y)
  change (FirstFactorSingularTimeModelComparison.cross X Y).f (N + 1) ≫
    (push (modelEvaluation H Y)).f (N + 1) =
      (push (DoubleClosedSweepProjection.evaluation H) ⊗ₘ 𝟙 (chains Y)).f (N + 1) ≫
        (SmallRectangleCross.ambient X' Y).f (N + 1) at hc
  rw [hc, ← Category.assoc, tensor_prism]

def productSweep := ((productHomotopy H Y).toSSet.chainComplexMap coeff).compLeft (SmallRectangleCross.ambient X Y)
def tensorSweep := (tensorPrism H Y).compRight (SmallRectangleCross.ambient X' Y)

def comparison (N : ℕ) := FirstFactorSingularTimeModelComparison.doublePrism X Y N ≫
  (push (modelEvaluation H Y)).f (N + 2)

theorem cycle_boundary (N : ℕ) :
    (chains X ⊗ chains Y).iCycles N ≫
      ((productSweep H Y).hom N (N + 1) - (tensorSweep H Y).hom N (N + 1)) =
      ((chains X ⊗ chains Y).iCycles N ≫ comparison H Y N) ≫ (chains (X' ⊗ Y)).d (N + 2) (N + 1) := by
  have he := congrArg (fun a => a ≫ (push (modelEvaluation H Y)).f (N + 1))
    (FirstFactorSingularTimeModelComparison.cycle_boundary X Y N)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc] at he
  rw [product_prism, tensor_component] at he
  rw [← (push (modelEvaluation H Y)).comm (N + 2) (N + 1)] at he
  simpa only [productSweep, tensorSweep, comparison, Homotopy.compLeft_hom, Homotopy.compRight_hom,
    Preadditive.comp_sub, Category.assoc] using he

theorem sweep_comparison (N : ℕ) :
    SelfHomotopySweep.homology (productSweep H Y) N = SelfHomotopySweep.homology (tensorSweep H Y) N :=
  SelfSweepExact.homology_eq (productSweep H Y) (tensorSweep H Y) N (comparison H Y N) (cycle_boundary H Y N)

theorem homology (N : ℕ) :
    homologyMap (SmallRectangleCross.ambient X Y) N ≫
      SelfHomotopySweep.homology ((productHomotopy H Y).toSSet.chainComplexMap coeff) N =
      SelfHomotopySweep.homology (tensorPrism H Y) N ≫ homologyMap (SmallRectangleCross.ambient X' Y) (N + 1) := by
  have hp := SelfHomotopySweepNaturality.homology (productSweep H Y)
    ((productHomotopy H Y).toSSet.chainComplexMap coeff) (SmallRectangleCross.ambient X Y)
    (𝟙 (chains (X' ⊗ Y))) (fun k => by
      rw [HomologicalComplex.id_f, Category.comp_id]
      rfl) N
  have ht := SelfHomotopySweepNaturality.homology (tensorPrism H Y) (tensorSweep H Y)
    (𝟙 (chains X ⊗ chains Y)) (SmallRectangleCross.ambient X' Y) (fun k => by
      rw [HomologicalComplex.id_f, Category.id_comp]
      rfl) N
  rw [HomologicalComplex.homologyMap_id, Category.comp_id, sweep_comparison H Y N] at hp
  rw [HomologicalComplex.homologyMap_id, Category.id_comp] at ht
  exact hp.trans ht

theorem cross_map (i j : ℕ) :
    FilteredBilinearLoopProduct.crossMap X Y i j (i + j) rfl ≫
      SelfHomotopySweep.homology ((productHomotopy H Y).toSSet.chainComplexMap coeff) (i + j) =
      (SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) i ⊗ₘ 𝟙 (homologyZMod2 Y j)) ≫
        FilteredBilinearLoopProduct.crossMap X' Y (i + 1) j (i + j + 1) (by omega) := by
  rw [← SmallCrossHomologyBridge.ambient, Category.assoc, homology, ← Category.assoc,
    FirstFactorSweepHomologyCross.homology, Category.assoc, SmallCrossHomologyBridge.ambient]
  rfl

theorem cross_value (i j : ℕ) (x : homologyZMod2 X i) (y : homologyZMod2 Y j) :
    (SelfHomotopySweep.homology ((productHomotopy H Y).toSSet.chainComplexMap coeff) (i + j)).hom
      (FilteredBilinearLoopProduct.cross X Y i j (i + j) rfl x y) =
      FilteredBilinearLoopProduct.cross X' Y (i + 1) j (i + j + 1) (by omega)
        ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) i).hom x) y := by
  have he := ConcreteCategory.congr_hom (cross_map H Y i j) (x ⊗ₜ[ZMod 2] y)
  change _ = (FilteredBilinearLoopProduct.crossMap X' Y (i + 1) j (i + j + 1) (by omega)).hom
    ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) i ⊗ₘ 𝟙 (homologyZMod2 Y j)).hom
      (x ⊗ₜ[ZMod 2] y)) at he
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.id_apply] at he
  exact he

theorem cross_value_of_eq (i j N : ℕ) (h : i + j = N)
    (x : homologyZMod2 X i) (y : homologyZMod2 Y j) :
    (SelfHomotopySweep.homology ((productHomotopy H Y).toSSet.chainComplexMap coeff) N).hom
      (FilteredBilinearLoopProduct.cross X Y i j N h x y) =
      FilteredBilinearLoopProduct.cross X' Y (i + 1) j (N + 1) (by omega)
        ((SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) i).hom x) y := by
  subst N
  exact cross_value H Y i j x y

end
end Finsler.ClosedFirstFactorSweepCross
