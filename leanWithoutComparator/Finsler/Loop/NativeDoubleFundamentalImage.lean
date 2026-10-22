module

public import Finsler.Loop.NativeDoubleAbsoluteSweep
public import Finsler.Loop.ClosedSecondFactorSweepCross

/-! Identify the ACTUAL double-prism graph input with the REAL
relative projection of the EXISTING sphere fundamental cross sphere
fundamental cross remaining equator fundamental. Every sweep/cross
comparison is proved from the constructed double prism, retaining
the true product associators. No numeric cut or relative nonzero
claim follows without its own proof. -/
@[expose] public section
namespace Finsler.NativeDoubleFundamentalImage
open CategoryTheory AlgebraicTopology MonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev equatorSpace {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (equator P)
abbrev full {n : ℕ} (P : Sphere n) (v₀ : equator P) := MeridianRelativeSweep.fullHomotopy P v₀

def firstPairHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  ClosedSecondFactorSweepCross.productHomotopy (equatorSpace P) (full P v₀)
def firstTripleHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  ClosedFirstFactorSweepCross.productHomotopy (firstPairHomotopy P v₀) (equatorSpace P)
def secondPairHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  ClosedFirstFactorSweepCross.productHomotopy (full P v₀) (BorelEvaluation.sphere n)
def secondTripleHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  ClosedFirstFactorSweepCross.productHomotopy (secondPairHomotopy P v₀) (equatorSpace P)

theorem full_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (SelfHomotopySweep.homology ((full P v₀).toSSet.chainComplexMap coeff) m).hom
      (MeridianEquatorHomology.fundamental m hm P) = SphereUnitCandidate.fundamental (m + 1) (by omega) := by
  have he := ConcreteCategory.congr_hom (MeridianRelativeSweep.full_original_homology P v₀ m)
    (MeridianEquatorHomology.fundamental m hm P)
  change _ = MeridianLoopClass.sweepClass m hm P v₀ at he
  exact he.trans (MeridianRotationClasses.sweep_fundamental m hm P v₀)

theorem first_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    ((firstTripleHomotopy P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (push (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom).f (q + 1) =
      ((NativeDoubleAbsoluteSweep.firstHomotopy P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl
      (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom) (firstTripleHomotopy P v₀)).h =
        (NativeDoubleAbsoluteSweep.firstHomotopy P v₀).h := by
    apply TopCat.ext
    intro z
    rfl
  exact (TimePrismNaturality.prism_post (firstTripleHomotopy P v₀)
    (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom q).trans
      (TimePrismNaturality.prism_congr _ _ he q)

theorem first_homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    SelfHomotopySweep.homology ((NativeDoubleAbsoluteSweep.firstHomotopy P v₀).toSSet.chainComplexMap coeff) q =
      SelfHomotopySweep.homology ((firstTripleHomotopy P v₀).toSSet.chainComplexMap coeff) q ≫
        homologyPushZMod2 (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom (q + 1) := by
  have he := SelfHomotopySweepNaturality.homology ((firstTripleHomotopy P v₀).toSSet.chainComplexMap coeff)
    ((NativeDoubleAbsoluteSweep.firstHomotopy P v₀).toSSet.chainComplexMap coeff)
    (𝟙 (chains (NativeDoubleAbsoluteSweep.source P)))
    (push (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom)
    (fun k => by
      rw [HomologicalComplex.id_f]
      exact (Category.id_comp _).trans (first_prism P v₀ k).symm) q
  have hid : HomologicalComplex.homologyMap (𝟙 (chains (NativeDoubleAbsoluteSweep.source P))) q =
      𝟙 ((chains (NativeDoubleAbsoluteSweep.source P)).homology q) := HomologicalComplex.homologyMap_id _ _
  have hl := (congrArg (fun a => a ≫ SelfHomotopySweep.homology
    ((NativeDoubleAbsoluteSweep.firstHomotopy P v₀).toSSet.chainComplexMap coeff) q) hid).trans (Category.id_comp _)
  exact hl.symm.trans he

theorem second_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    (push (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom).f q ≫
      ((NativeDoubleAbsoluteSweep.secondHomotopy P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) =
      ((secondTripleHomotopy P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        (push (α_ (BorelEvaluation.sphere n) (BorelEvaluation.sphere n) (equatorSpace P)).hom).f (q + 1) := by
  have he : ((NativeDoubleAbsoluteSweep.secondHomotopy P v₀).comp (TopCat.Homotopy.refl
      (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom)).h =
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl
      (α_ (BorelEvaluation.sphere n) (BorelEvaluation.sphere n) (equatorSpace P)).hom)
        (secondTripleHomotopy P v₀)).h := by
    apply TopCat.ext
    intro z
    rfl
  exact ((TimePrismNaturality.prism_pre (NativeDoubleAbsoluteSweep.secondHomotopy P v₀)
    (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom q).trans
      (TimePrismNaturality.prism_congr _ _ he q)).trans
        (TimePrismNaturality.prism_post (secondTripleHomotopy P v₀)
          (α_ (BorelEvaluation.sphere n) (BorelEvaluation.sphere n) (equatorSpace P)).hom q).symm

theorem second_homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    homologyPushZMod2 (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom q ≫
      SelfHomotopySweep.homology ((NativeDoubleAbsoluteSweep.secondHomotopy P v₀).toSSet.chainComplexMap coeff) q =
      SelfHomotopySweep.homology ((secondTripleHomotopy P v₀).toSSet.chainComplexMap coeff) q ≫
        homologyPushZMod2 (α_ (BorelEvaluation.sphere n) (BorelEvaluation.sphere n) (equatorSpace P)).hom (q + 1) :=
  SelfHomotopySweepNaturality.homology ((secondTripleHomotopy P v₀).toSSet.chainComplexMap coeff)
    ((NativeDoubleAbsoluteSweep.secondHomotopy P v₀).toSSet.chainComplexMap coeff)
    (push (α_ (equatorSpace P) (BorelEvaluation.sphere n) (equatorSpace P)).hom)
    (push (α_ (BorelEvaluation.sphere n) (BorelEvaluation.sphere n) (equatorSpace P)).hom)
    (second_prism P v₀) q

theorem absolute_homology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    NativeDoubleAbsoluteSweep.absoluteHomology P v₀ q =
      SelfHomotopySweep.homology ((firstTripleHomotopy P v₀).toSSet.chainComplexMap coeff) q ≫
        SelfHomotopySweep.homology ((secondTripleHomotopy P v₀).toSSet.chainComplexMap coeff) (q + 1) ≫
          homologyPushZMod2 (α_ (BorelEvaluation.sphere n) (BorelEvaluation.sphere n) (equatorSpace P)).hom (q + 2) := by
  dsimp only [NativeDoubleAbsoluteSweep.absoluteHomology]
  rw [first_homology, Category.assoc, second_homology]

def firstPairClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  FilteredBilinearLoopProduct.cross (equatorSpace P) (BorelEvaluation.sphere (m + 1)) m (m + 1) (2 * m + 1) (by omega)
    (MeridianEquatorHomology.fundamental m hm P) (SphereUnitCandidate.fundamental (m + 1) (by omega))
def firstTripleClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  FilteredBilinearLoopProduct.cross (equatorSpace P ⊗ BorelEvaluation.sphere (m + 1)) (equatorSpace P)
    (2 * m + 1) m (3 * m + 1) (by omega) (firstPairClass m hm P) (MeridianEquatorHomology.fundamental m hm P)
def spherePairClass (m : ℕ) (_P : Sphere (m + 1)) :=
  FilteredBilinearLoopProduct.cross (BorelEvaluation.sphere (m + 1)) (BorelEvaluation.sphere (m + 1))
    (m + 1) (m + 1) (2 * m + 2) (by omega)
    (SphereUnitCandidate.fundamental (m + 1) (by omega)) (SphereUnitCandidate.fundamental (m + 1) (by omega))
def sphereTripleClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  FilteredBilinearLoopProduct.cross (BorelEvaluation.sphere (m + 1) ⊗ BorelEvaluation.sphere (m + 1)) (equatorSpace P)
    (2 * m + 2) m (3 * m + 2) (by omega) (spherePairClass m P) (MeridianEquatorHomology.fundamental m hm P)
def fundamentalImage (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :=
  (homologyPushZMod2 (α_ (BorelEvaluation.sphere (m + 1)) (BorelEvaluation.sphere (m + 1)) (equatorSpace P)).hom
    (3 * m + 2)).hom (sphereTripleClass m hm P)

theorem first_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (SelfHomotopySweep.homology ((firstTripleHomotopy P v₀).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P) = firstTripleClass m hm P := by
  change (SelfHomotopySweep.homology ((ClosedFirstFactorSweepCross.productHomotopy (firstPairHomotopy P v₀)
    (equatorSpace P)).toSSet.chainComplexMap coeff) (3 * m)).hom
      (FilteredBilinearLoopProduct.cross (equatorSpace P ⊗ equatorSpace P) (equatorSpace P)
        (2 * m) m (3 * m) (by omega) (BasedMeridianProducts.doubleSource m hm P)
          (MeridianEquatorHomology.fundamental m hm P)) = _
  rw [ClosedFirstFactorSweepCross.cross_value_of_eq]
  change FilteredBilinearLoopProduct.cross (equatorSpace P ⊗ BorelEvaluation.sphere (m + 1)) (equatorSpace P)
    (2 * m + 1) m (3 * m + 1) (by omega)
      ((SelfHomotopySweep.homology ((ClosedSecondFactorSweepCross.productHomotopy (equatorSpace P) (full P v₀)).toSSet.chainComplexMap coeff)
        (2 * m)).hom (FilteredBilinearLoopProduct.cross (equatorSpace P) (equatorSpace P) m m (2 * m) (by omega)
          (MeridianEquatorHomology.fundamental m hm P) (MeridianEquatorHomology.fundamental m hm P)))
      (MeridianEquatorHomology.fundamental m hm P) = _
  rw [ClosedSecondFactorSweepCross.cross_value_of_eq, full_fundamental]
  rfl

theorem second_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (SelfHomotopySweep.homology ((secondTripleHomotopy P v₀).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
      (firstTripleClass m hm P) = sphereTripleClass m hm P := by
  change (SelfHomotopySweep.homology ((ClosedFirstFactorSweepCross.productHomotopy (secondPairHomotopy P v₀)
    (equatorSpace P)).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
      (FilteredBilinearLoopProduct.cross (equatorSpace P ⊗ BorelEvaluation.sphere (m + 1)) (equatorSpace P)
        (2 * m + 1) m (3 * m + 1) (by omega) (firstPairClass m hm P)
          (MeridianEquatorHomology.fundamental m hm P)) = _
  rw [ClosedFirstFactorSweepCross.cross_value_of_eq]
  change FilteredBilinearLoopProduct.cross (BorelEvaluation.sphere (m + 1) ⊗ BorelEvaluation.sphere (m + 1)) (equatorSpace P)
    (2 * m + 2) m (3 * m + 2) (by omega)
      ((SelfHomotopySweep.homology ((ClosedFirstFactorSweepCross.productHomotopy (full P v₀) (BorelEvaluation.sphere (m + 1))).toSSet.chainComplexMap coeff)
        (2 * m + 1)).hom (FilteredBilinearLoopProduct.cross (equatorSpace P) (BorelEvaluation.sphere (m + 1)) m (m + 1) (2 * m + 1) (by omega)
          (MeridianEquatorHomology.fundamental m hm P) (SphereUnitCandidate.fundamental (m + 1) (by omega))))
      (MeridianEquatorHomology.fundamental m hm P) = _
  rw [ClosedFirstFactorSweepCross.cross_value_of_eq, full_fundamental]
  rfl

theorem absoluteInput_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeDoubleAbsoluteSweep.absoluteInputClass m hm P v₀ = fundamentalImage m hm P := by
  have he := ConcreteCategory.congr_hom (absolute_homology P v₀ (3 * m))
    (BasedMeridianProducts.tripleSource m hm P)
  change NativeDoubleAbsoluteSweep.absoluteInputClass m hm P v₀ =
    (homologyPushZMod2 (α_ (BorelEvaluation.sphere (m + 1)) (BorelEvaluation.sphere (m + 1)) (equatorSpace P)).hom
      (3 * m + 2)).hom
      ((SelfHomotopySweep.homology ((secondTripleHomotopy P v₀).toSSet.chainComplexMap coeff) (3 * m + 1)).hom
        ((SelfHomotopySweep.homology ((firstTripleHomotopy P v₀).toSSet.chainComplexMap coeff) (3 * m)).hom
          (BasedMeridianProducts.tripleSource m hm P))) at he
  rw [first_value, second_value] at he
  exact he

theorem graphInput_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    graphInputClass m hm P v₀ = ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (fundamentalImage m hm P) :=
  (NativeDoubleAbsoluteSweep.graphInput_projection m hm P v₀).trans
    (congrArg ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (absoluteInput_fundamental m hm P v₀))

theorem nativeInput_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (TopPair.singularHomologyMap (nativeToGraph P v₀) coeff (3 * m + 2)).hom
      (NativePairDoublePrismSource.inputClass m hm P v₀) =
      ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (fundamentalImage m hm P) :=
  (NativeDoubleAbsoluteSweep.nativeInput_projection m hm P v₀).trans
    (congrArg ((graphPair P v₀).singularHomologyπ coeff (3 * m + 2)).hom (absoluteInput_fundamental m hm P v₀))

theorem relative_pairing_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (a : RelativeCup.cohomology (graphPair P v₀) (3 * m + 2)) :
    RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2) a (graphInputClass m hm P v₀) =
      (kroneckerMap (graphSpace P) (3 * m + 2)).hom
        ((relativeToPool (graphPair P v₀) (3 * m + 2)).hom a) (fundamentalImage m hm P) :=
  (NativeDoubleAbsoluteSweep.relative_pairing m hm P v₀ a).trans
    (congrArg ((kroneckerMap (graphSpace P) (3 * m + 2)).hom
      ((relativeToPool (graphPair P v₀) (3 * m + 2)).hom a)) (absoluteInput_fundamental m hm P v₀))

end
end Finsler.NativeDoubleFundamentalImage
