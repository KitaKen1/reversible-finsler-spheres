module

public import Finsler.Loop.DoubleRelativeTimeCylinder
public import Finsler.Loop.SelfHomotopySweepNaturality

/-! The ACTUAL two-prism square input followed by two CLOSED
homotopies equals the actual relative quotient of their two ordinary
self-sweeps. This is a chain/cycle/homology comparison for every
source degree. It assumes only the real square faces land in the
real target subspace, not that relative cycles lift to absolute ones. -/
@[expose] public section
namespace Finsler.DoubleClosedSweepProjection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {X Y Z : TopCat.{0}} {f : X ⟶ Y} {g : Y ⟶ Z}

def evaluation (H : TopCat.Homotopy f f) : DoubleRelativeTimeCylinder.cylinder X ⟶ Y :=
  TopCat.ofHom ⟨fun z => H z, H.continuous⟩

theorem evaluation_prism (H : TopCat.Homotopy f f) (q : ℕ) :
    ((DoubleRelativeTimeCylinder.homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (push (evaluation H)).f (q + 1) = (H.toSSet.chainComplexMap coeff).hom q (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (evaluation H))
      (DoubleRelativeTimeCylinder.homotopy X)).h = H.h := by
    apply TopCat.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (DoubleRelativeTimeCylinder.homotopy X) (evaluation H) q).trans
    (TimePrismNaturality.prism_congr _ H he q)

def squareEvaluation (H : TopCat.Homotopy f f) (K : TopCat.Homotopy g g) :
    DoubleRelativeTimeCylinder.cylinder (DoubleRelativeTimeCylinder.cylinder X) ⟶ Z :=
  TopCat.ofHom ⟨fun z => K (z.1, H z.2), by
    have hi : Continuous (fun z : DoubleRelativeTimeCylinder.cylinder
        (DoubleRelativeTimeCylinder.cylinder X) => z.2) := continuous_snd
    have hh := H.continuous.comp hi
    have hk := K.continuous.comp (continuous_fst.prodMk hh)
    exact hk.congr (fun _ => rfl)⟩

theorem second_prism (H : TopCat.Homotopy f f) (K : TopCat.Homotopy g g) (q : ℕ) :
    ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (push (squareEvaluation H K)).f (q + 1) =
        (push (evaluation H)).f q ≫ (K.toSSet.chainComplexMap coeff).hom q (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (squareEvaluation H K))
      (DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X))).h =
        (K.comp (TopCat.Homotopy.refl (evaluation H))).h := by
    apply TopCat.ext
    intro z
    rfl
  exact ((TimePrismNaturality.prism_post (DoubleRelativeTimeCylinder.homotopy
    (DoubleRelativeTimeCylinder.cylinder X)) (squareEvaluation H K) q).trans
      (TimePrismNaturality.prism_congr _ _ he q)).trans
        (TimePrismNaturality.prism_pre K (evaluation H) q).symm

theorem raw_component (H : TopCat.Homotopy f f) (K : TopCat.Homotopy g g) (q : ℕ) :
    ((DoubleRelativeTimeCylinder.homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X)).toSSet.chainComplexMap coeff).hom
        (q + 1) (q + 2) ≫ (push (squareEvaluation H K)).f (q + 2) =
      (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) := by
  have hs := second_prism H K (q + 1)
  change ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X)).toSSet.chainComplexMap coeff).hom
      (q + 1) (q + 2) ≫ (push (squareEvaluation H K)).f (q + 2) =
        (push (evaluation H)).f (q + 1) ≫ (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) at hs
  rw [hs, ← Category.assoc, evaluation_prism]

variable (H : TopCat.Homotopy f f) (K : TopCat.Homotopy g g) (B : Set Z)
  (hB : Set.MapsTo (squareEvaluation H K) (DoubleRelativeTimeCylinder.squareBoundary X) B)

abbrev target : TopPair.{0} := TopPair.ofSubset B

def pairMap : DoubleRelativeTimeCylinder.squarePair X ⟶ target B :=
  TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary X) (B' := B)
    (squareEvaluation H K) hB

def relativeMap := TopPair.singularChainComplexMap (pairMap H K B hB) coeff

theorem pairMap_fst : TopPair.Hom.fst (pairMap H K B hB) = squareEvaluation H K := by
  apply TopCat.ext
  intro z
  exact TopPair.ofSubsetMap_fst_apply (B := DoubleRelativeTimeCylinder.squareBoundary X) (B' := B)
    (squareEvaluation H K) hB z

include hB in
theorem component (q : ℕ) :
    DoubleRelativeTimeCylinder.component X q ≫ (relativeMap H K B hB).f (q + 2) =
      (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫
          ((target B).singularChainComplexπ coeff).f (q + 2) := by
  have he := congrArg (fun a => a.f (q + 2))
    (TopPair.singularChainComplexπ_pair_naturality (pairMap H K B hB) coeff)
  change (push (TopPair.Hom.fst (pairMap H K B hB))).f (q + 2) ≫ ((target B).singularChainComplexπ coeff).f (q + 2) =
    ((DoubleRelativeTimeCylinder.squarePair X).singularChainComplexπ coeff).f (q + 2) ≫
      (relativeMap H K B hB).f (q + 2) at he
  rw [pairMap_fst] at he
  calc
    _ = ((DoubleRelativeTimeCylinder.homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X)).toSSet.chainComplexMap coeff).hom
          (q + 1) (q + 2) ≫ (push (squareEvaluation H K)).f (q + 2) ≫
            ((target B).singularChainComplexπ coeff).f (q + 2) := by
      simpa only [DoubleRelativeTimeCylinder.component, Category.assoc] using
        congrArg (fun a => ((DoubleRelativeTimeCylinder.homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
          ((DoubleRelativeTimeCylinder.homotopy (DoubleRelativeTimeCylinder.cylinder X)).toSSet.chainComplexMap coeff).hom
            (q + 1) (q + 2) ≫ a) he.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun a => a ≫ ((target B).singularChainComplexπ coeff).f (q + 2)) (raw_component H K q)

include hB in
theorem cycles (q : ℕ) :
    DoubleRelativeTimeCylinder.cycles X q ≫ HomologicalComplex.cyclesMap (relativeMap H K B hB) (q + 2) =
      SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫
        SelfHomotopySweep.cycles (K.toSSet.chainComplexMap coeff) (q + 1) ≫
          HomologicalComplex.cyclesMap ((target B).singularChainComplexπ coeff) (q + 2) := by
  apply (cancel_mono (((target B).singularChainComplex coeff).iCycles (q + 2))).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, DoubleRelativeTimeCylinder.cycles_i, Category.assoc, component]
  change _ = SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫
    SelfHomotopySweep.cycles (K.toSSet.chainComplexMap coeff) (q + 1) ≫
      (chains Z).iCycles (q + 2) ≫ ((target B).singularChainComplexπ coeff).f (q + 2)
  have hk := SelfHomotopySweep.cycles_i (K.toSSet.chainComplexMap coeff) (q + 1)
  have hh := SelfHomotopySweep.cycles_i (H.toSSet.chainComplexMap coeff) q
  have hh' : (chains X).iCycles q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ ((target B).singularChainComplexπ coeff).f (q + 2) =
      SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫ (chains Y).iCycles (q + 1) ≫
        (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ ((target B).singularChainComplexπ coeff).f (q + 2) := by
    simpa only [Category.assoc, SelfHomotopySweep.component] using
      (congrArg (fun a => a ≫ (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫
        ((target B).singularChainComplexπ coeff).f (q + 2)) hh).symm
  have hk' : SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫ (chains Y).iCycles (q + 1) ≫
      (K.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ ((target B).singularChainComplexπ coeff).f (q + 2) =
      SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫
        SelfHomotopySweep.cycles (K.toSSet.chainComplexMap coeff) (q + 1) ≫
          (chains Z).iCycles (q + 2) ≫ ((target B).singularChainComplexπ coeff).f (q + 2) := by
    simpa only [Category.assoc, SelfHomotopySweep.component] using
      (congrArg (fun a => SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫
        a ≫ ((target B).singularChainComplexπ coeff).f (q + 2)) hk).symm
  simpa only [Category.assoc] using hh'.trans hk'

include hB in
theorem homology (q : ℕ) :
    DoubleRelativeTimeCylinder.homology X q ≫ HomologicalComplex.homologyMap (relativeMap H K B hB) (q + 2) =
      SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫
        SelfHomotopySweep.homology (K.toSSet.chainComplexMap coeff) (q + 1) ≫
          HomologicalComplex.homologyMap ((target B).singularChainComplexπ coeff) (q + 2) := by
  apply (cancel_epi ((chains X).homologyπ q)).mp
  have ha : (chains X).homologyπ q ≫
      (SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫
        SelfHomotopySweep.homology (K.toSSet.chainComplexMap coeff) (q + 1)) =
      (SelfHomotopySweep.cycles (H.toSSet.chainComplexMap coeff) q ≫
        SelfHomotopySweep.cycles (K.toSSet.chainComplexMap coeff) (q + 1)) ≫ (chains Z).homologyπ (q + 2) := by
    rw [← Category.assoc, SelfHomotopySweep.homologyπ_homology, Category.assoc,
      SelfHomotopySweep.homologyπ_homology, ← Category.assoc]
  calc
    _ = (DoubleRelativeTimeCylinder.cycles X q ≫
        HomologicalComplex.cyclesMap (relativeMap H K B hB) (q + 2)) ≫
          ((target B).singularChainComplex coeff).homologyπ (q + 2) := by
      rw [← Category.assoc, DoubleRelativeTimeCylinder.homologyπ_homology,
        Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
    _ = _ := by
      rw [cycles]
      rw [Category.assoc, Category.assoc, ← HomologicalComplex.homologyπ_naturality]
      change _ = ((chains X).homologyπ q ≫
        (SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫
          SelfHomotopySweep.homology (K.toSSet.chainComplexMap coeff) (q + 1))) ≫
            HomologicalComplex.homologyMap ((target B).singularChainComplexπ coeff) (q + 2)
      rw [ha]
      rfl

end
end Finsler.DoubleClosedSweepProjection
