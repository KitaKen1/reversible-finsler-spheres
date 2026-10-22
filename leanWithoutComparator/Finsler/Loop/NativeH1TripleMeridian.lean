module

public import Finsler.Loop.NativeH1MeridianFamily
public import Finsler.Loop.MeridianRotationClasses
public import Finsler.Loop.MeridianTripleQuarterClocks

/-! Explicit strong-H1 representatives of the ORIGINAL triple
based family, its cube homology class and the actual rotation
sweep Theta candidate. The original H1 cut may now be evaluated
on this same geometric family; no arbitrary smoothing inverse
representative remains. -/
@[expose] public section
namespace Finsler.NativeH1TripleMeridian
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.H1PathRepresentativeCalculus Finsler.NativeH1MeridianFamily
open Finsler.SobolevCircleRepresentative Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev parameters {n : ℕ} (P : Sphere n) := (equator P × equator P) × equator P

def pairData {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : equator P × equator P) : Space n :=
  halfConcat (loopData P v₀ z.1) (loopData P v₀ z.2)

def tripleData {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P) : Space n :=
  halfConcat (pairData P v₀ z.1) (loopData P v₀ z.2)

def triplePath {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P) : Path P P :=
  ((loop P v₀ z.1.1).trans (loop P v₀ z.1.2)).trans (loop P v₀ z.2)

theorem representative_pair {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : equator P × equator P) (t : _root_.unitInterval) :
    continuousRepresentative (pairData P v₀ z) (t : ℝ) =
      ((loop P v₀ z.1).trans (loop P v₀ z.2) t : Ambient n) :=
  represented_concat _ _ _ _ (representative_loop P v₀ z.1) (representative_loop P v₀ z.2) t

theorem representative_triple {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : parameters P) (t : _root_.unitInterval) :
    continuousRepresentative (tripleData P v₀ z) (t : ℝ) = (triplePath P v₀ z t : Ambient n) :=
  represented_concat _ _ _ _ (representative_pair P v₀ z.1) (representative_loop P v₀ z.2) t

theorem continuous_pairData {n : ℕ} (P : Sphere n) (v₀ : equator P) : Continuous (pairData P v₀) := by
  apply continuous_halfConcat _ _ ((continuous_loopData P v₀).comp continuous_fst)
    ((continuous_loopData P v₀).comp continuous_snd)
  intro z
  change continuousRepresentative (loopData P v₀ z.1) 1 = continuousRepresentative (loopData P v₀ z.2) 0
  calc
    _ = (P : Ambient n) := by simpa only [Set.Icc.coe_one, Path.target] using representative_loop P v₀ z.1 1
    _ = _ := by simpa only [Set.Icc.coe_zero, Path.source] using (representative_loop P v₀ z.2 0).symm

theorem continuous_tripleData {n : ℕ} (P : Sphere n) (v₀ : equator P) : Continuous (tripleData P v₀) := by
  apply continuous_halfConcat _ _ ((continuous_pairData P v₀).comp continuous_fst)
    ((continuous_loopData P v₀).comp continuous_snd)
  intro z
  change continuousRepresentative (pairData P v₀ z.1) 1 = continuousRepresentative (loopData P v₀ z.2) 0
  calc
    _ = (P : Ambient n) := by simpa only [Set.Icc.coe_one, Path.target] using representative_pair P v₀ z.1 1
    _ = _ := by simpa only [Set.Icc.coe_zero, Path.source] using (representative_loop P v₀ z.2 0).symm

def native {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P) : SphereLoop n :=
  ⟨⟨tripleData P v₀ z, (mem_periodicSubmodule_iff _).mpr (by
    change continuousRepresentative (tripleData P v₀ z) 1 = continuousRepresentative (tripleData P v₀ z) 0
    calc
      _ = (P : Ambient n) := by simpa only [Set.Icc.coe_one, Path.target] using representative_triple P v₀ z 1
      _ = _ := by simpa only [Set.Icc.coe_zero, Path.source] using (representative_triple P v₀ z 0).symm)⟩,
    fun t => (congrArg norm (representative_triple P v₀ z t)).trans
      (mem_sphere_zero_iff_norm.mp (triplePath P v₀ z t).property)⟩

theorem continuous_native {n : ℕ} (P : Sphere n) (v₀ : equator P) : Continuous (native P v₀) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact sphereLoop_tendsto_iff.mpr (continuous_tripleData P v₀).continuousAt

def family {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (parameters P) ⟶ BorelLoop.Loops n :=
  TopCat.ofHom ⟨native P v₀, continuous_native P v₀⟩

theorem circle_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P)
    (x : SobolevCircleRepresentative.Circle) :
    sphereCircleMap (native P v₀ z) x = ClosedPathCircle.circle (ClosedPathCircle.ofPath (triplePath P v₀ z)) x := by
  rw [sphereCircleMap_point, ClosedPathCircle.circle_apply]
  apply Subtype.ext
  exact representative_triple P v₀ z (circlePoint x)

theorem family_inclusion {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    family P v₀ ≫ ContinuousLoopModel.inclusion n = MeridianRotationClasses.tripleOrdinary P v₀ := by
  ext z : 1
  apply ContinuousMap.ext
  intro x
  exact circle_value P v₀ z x

def cube (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (homologyPushZMod2 (family P v₀) (3 * m)).hom (BasedMeridianProducts.tripleSource m hm P)

theorem cube_original (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    cube m hm P v₀ = MeridianRotationClasses.H1Cube m hm P v₀ := by
  apply (ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m)).injective
  have hn := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (3 * m)).obj coeff).map_comp
      (family P v₀) (ContinuousLoopModel.inclusion (m + 1))) (BasedMeridianProducts.tripleSource m hm P)
  rw [family_inclusion] at hn
  have hc := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (3 * m)).obj coeff).map_comp
      (BasedMeridianProducts.tripleFamily P v₀) (BasedMeridianProducts.forget P)) (BasedMeridianProducts.tripleSource m hm P)
  change _ = (homologyPushZMod2 (BasedMeridianProducts.forget P) (3 * m)).hom
    ((homologyPushZMod2 (BasedMeridianProducts.tripleFamily P v₀) (3 * m)).hom _) at hc
  rw [BasedMeridianProducts.tripleFamily_image] at hc
  change _ = (ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m))
    ((ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m)).symm _)
  rw [LinearEquiv.apply_symm_apply]
  exact hn.symm.trans hc

def rotationHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  (H1LoopRotation.homotopy n).comp (TopCat.Homotopy.refl (family P v₀))

theorem theta_original (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (SelfHomotopySweep.homology ((rotationHomotopy P v₀).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P) = MeridianRotationClasses.H1Theta m hm P v₀ := by
  have hn := SelfHomotopySweepNaturality.homology
    ((rotationHomotopy P v₀).toSSet.chainComplexMap coeff) (H1LoopRotation.chainHomotopy (m + 1))
    (push (family P v₀)) (𝟙 _)
    (fun q => by rw [HomologicalComplex.id_f, Category.comp_id]; exact TimePrismNaturality.prism_pre _ _ q) (3 * m)
  rw [HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  have he := ConcreteCategory.congr_hom hn (BasedMeridianProducts.tripleSource m hm P)
  have hc := congrArg ((H1LoopRotation.BV (m + 1) (3 * m)).hom) (cube_original m hm P v₀)
  exact he.symm.trans hc

end
end Finsler.NativeH1TripleMeridian
