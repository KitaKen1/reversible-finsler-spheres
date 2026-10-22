module

public import Finsler.Loop.RelativePrismSweep
public import TauCeti.Topology.Category.TopPair

/-! TWO genuine interval prisms of an arbitrary source class define
an ACTUAL relative class modulo ALL FOUR time faces. The second
prism descends with pinned TauCeti relative homotopy. The cycles and
homology maps have exact ORIGINAL double-prism component formulas,
including source degreezero. No fundamental class/value is assumed. -/
@[expose] public section
namespace Finsler.DoubleRelativeTimeCylinder
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

abbrev cylinder (X : TopCat.{0}) : TopCat.{0} := TopCat.of (_root_.unitInterval × X)

def atTime (X : TopCat.{0}) (t : _root_.unitInterval) : X ⟶ cylinder X :=
  TopCat.ofHom ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩

def homotopy (X : TopCat.{0}) : TopCat.Homotopy (atTime X 0) (atTime X 1) where
  toFun z := z
  continuous_toFun := continuous_id
  map_zero_left _ := rfl
  map_one_left _ := rfl

def boundary (X : TopCat.{0}) : Set (cylinder X) := {z | z.1 = 0 ∨ z.1 = 1}
abbrev pair (X : TopCat.{0}) : TopPair.{0} := TopPair.ofSubset (X := cylinder X) (boundary X)

def squareBoundary (X : TopCat.{0}) : Set (cylinder (cylinder X)) :=
  {z | (z.1 = 0 ∨ z.1 = 1) ∨ (z.2.1 = 0 ∨ z.2.1 = 1)}
abbrev squarePair (X : TopCat.{0}) : TopPair.{0} :=
  TopPair.ofSubset (X := cylinder (cylinder X)) (squareBoundary X)

def firstSweep (X : TopCat.{0}) :
    _root_.Homotopy (0 : chains X ⟶ (pair X).singularChainComplex coeff) 0 :=
  RelativePrismSweep.ordinary (boundary X) (homotopy X)
    (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)

def insertPair (X : TopCat.{0}) (t : _root_.unitInterval) : pair X ⟶ squarePair X :=
  TopPair.ofSubsetMap (B := boundary X) (B' := squareBoundary X)
    (atTime (cylinder X) t) (fun _ h => Or.inr h)

theorem insertPair_fst (X : TopCat.{0}) (t : _root_.unitInterval) :
    TopPair.Hom.fst (insertPair X t) = atTime (cylinder X) t := by
  ext z : 1
  exact TopPair.ofSubsetMap_fst_apply (B := boundary X) (B' := squareBoundary X)
    (atTime (cylinder X) t) (fun _ h => Or.inr h) z

def secondHomotopy (X : TopCat.{0}) : TopPair.Homotopy (insertPair X 0) (insertPair X 1) where
  fst :=
    { toFun z := z
      continuous_toFun := continuous_id
      map_zero_left x := by
        rw [insertPair_fst]
        rfl
      map_one_left x := by
        rw [insertPair_fst]
        rfl }
  snd :=
    { toFun z := ⟨(z.1, z.2.val), Or.inr z.2.property⟩
      continuous_toFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left x := by
        apply Subtype.ext
        exact (TopPair.ofSubsetMap_snd_apply (B := boundary X) (B' := squareBoundary X)
          (atTime (cylinder X) 0) (fun _ h => Or.inr h) x).symm
      map_one_left x := by
        apply Subtype.ext
        exact (TopPair.ofSubsetMap_snd_apply (B := boundary X) (B' := squareBoundary X)
          (atTime (cylinder X) 1) (fun _ h => Or.inr h) x).symm }

theorem insert_zero_range (X : TopCat.{0}) (x : (pair X).fst) :
    (TopPair.Hom.fst (insertPair X 0)) x ∈ squareBoundary X := by
  rw [insertPair_fst]
  exact Or.inl (Or.inl rfl)

theorem insert_one_range (X : TopCat.{0}) (x : (pair X).fst) :
    (TopPair.Hom.fst (insertPair X 1)) x ∈ squareBoundary X := by
  rw [insertPair_fst]
  exact Or.inl (Or.inr rfl)

def secondSweep (X : TopCat.{0}) :
    _root_.Homotopy (0 : (pair X).singularChainComplex coeff ⟶ (squarePair X).singularChainComplex coeff) 0 :=
  RelativePrismSweep.relative (squareBoundary X) (secondHomotopy X) (insert_zero_range X) (insert_one_range X)

theorem first_component (X : TopCat.{0}) (q : ℕ) :
    SelfHomotopySweep.component (firstSweep X) q =
      ((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        ((pair X).singularChainComplexπ coeff).f (q + 1) :=
  RelativePrismSweep.ordinary_component (boundary X) (homotopy X) _ _ q

theorem second_component (X : TopCat.{0}) (q : ℕ) :
    ((pair X).singularChainComplexπ coeff).f q ≫ SelfHomotopySweep.component (secondSweep X) q =
      ((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        ((squarePair X).singularChainComplexπ coeff).f (q + 1) := by
  have he : (secondHomotopy X).fst.h = (homotopy (cylinder X)).h := by
    ext z : 1
    rfl
  have hc := TimePrismNaturality.prism_congr (secondHomotopy X).fst (homotopy (cylinder X)) he q
  have hr := RelativePrismSweep.relative_component (squareBoundary X) (secondHomotopy X)
    (insert_zero_range X) (insert_one_range X) q
  exact hr.trans (congrArg (fun k => k ≫ ((squarePair X).singularChainComplexπ coeff).f (q + 1)) hc)

def component (X : TopCat.{0}) (q : ℕ) : (chains X).X q ⟶ ((squarePair X).singularChainComplex coeff).X (q + 2) :=
  ((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
    ((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫
      ((squarePair X).singularChainComplexπ coeff).f (q + 2)

def cycles (X : TopCat.{0}) (q : ℕ) :
    (chains X).cycles q ⟶ ((squarePair X).singularChainComplex coeff).cycles (q + 2) :=
  SelfHomotopySweep.cycles (firstSweep X) q ≫ SelfHomotopySweep.cycles (secondSweep X) (q + 1)

theorem cycles_i (X : TopCat.{0}) (q : ℕ) :
    cycles X q ≫ ((squarePair X).singularChainComplex coeff).iCycles (q + 2) =
      (chains X).iCycles q ≫ component X q := by
  unfold cycles
  rw [Category.assoc, SelfHomotopySweep.cycles_i, ← Category.assoc, SelfHomotopySweep.cycles_i,
    Category.assoc, first_component, Category.assoc, second_component]
  rfl

def homology (X : TopCat.{0}) (q : ℕ) :
    homologyZMod2 X q ⟶ (squarePair X).singularHomology coeff (q + 2) :=
  SelfHomotopySweep.homology (firstSweep X) q ≫ SelfHomotopySweep.homology (secondSweep X) (q + 1)

theorem homologyπ_homology (X : TopCat.{0}) (q : ℕ) :
    (chains X).homologyπ q ≫ homology X q =
      cycles X q ≫ ((squarePair X).singularChainComplex coeff).homologyπ (q + 2) := by
  unfold homology
  rw [← Category.assoc, SelfHomotopySweep.homologyπ_homology, Category.assoc,
    SelfHomotopySweep.homologyπ_homology, ← Category.assoc]
  rfl

end
end Finsler.DoubleRelativeTimeCylinder
