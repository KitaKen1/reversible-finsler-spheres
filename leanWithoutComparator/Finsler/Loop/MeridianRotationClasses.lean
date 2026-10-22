module

public import Finsler.Loop.H1LoopRotation
public import Finsler.Loop.BasedMeridianProducts

/-! The primitive BV image has genuine sphere evaluation ONE.
An explicit triple based-meridian class followed by actual rotation
has the manuscript Theta degree3n-2. Its nonzero/GH/UNIT identities
are the remaining computation, not assumptions or claims here. -/
@[expose] public section
namespace Finsler.MeridianRotationClasses
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.BorelLoop Finsler.MeridianLoopFamily Finsler.MeridianLoopClass
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem sweep_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    sweepClass m hm P v₀ = SphereUnitCandidate.fundamental (m + 1) (by omega) := by
  apply (SphereTopClass.homologyEquiv (m + 1) (by omega)).injective
  rw [SphereUnitCandidate.fundamental, LinearEquiv.apply_symm_apply]
  exact MeridianPrimitiveNonzero.sweep_coefficient_one m hm P v₀

def ordinaryDetected (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (ContinuousLoopModel.space (m + 1)) (m + 1) :=
  (OrdinaryLoopRotation.BV (m + 1) m).hom (ordinaryClass m hm P v₀)

def H1Detected (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) (m + 1) :=
  (H1LoopRotation.BV (m + 1) m).hom (H1Class m hm P v₀)

theorem ordinary_evaluation (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (ContinuousLoopModel.evaluation (m + 1)) (m + 1)).hom
      (ordinaryDetected m hm P v₀) = SphereUnitCandidate.fundamental (m + 1) (by omega) := by
  have h := ConcreteCategory.congr_hom (OrdinaryLoopRotation.BV_evaluation (m + 1) m)
    (ordinaryClass m hm P v₀)
  change _ = sweepClass m hm P v₀ at h
  exact h.trans (sweep_fundamental m hm P v₀)

theorem inclusion_detected (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ContinuousLoopHomologyEquivalence.homology (m + 1) (m + 1) (H1Detected m hm P v₀) =
      ordinaryDetected m hm P v₀ := by
  rw [H1Detected, H1LoopRotation.equivalence_BV, inclusion_H1Class]
  rfl

theorem ordinary_detected_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ordinaryDetected m hm P v₀ ≠ 0 := by
  intro hz
  have h := ordinary_evaluation m hm P v₀
  rw [hz, map_zero] at h
  exact SphereUnitCandidate.fundamental_ne_zero (m + 1) (by omega) h.symm

theorem H1_detected_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    H1Detected m hm P v₀ ≠ 0 := by
  intro hz
  have h := inclusion_detected m hm P v₀
  rw [hz, map_zero] at h
  exact ordinary_detected_ne_zero m hm P v₀ h.symm

def ordinaryCube (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (ContinuousLoopModel.space (m + 1)) (3 * m) :=
  (homologyPushZMod2 (BasedMeridianProducts.forget P) (3 * m)).hom (BasedMeridianProducts.cube m hm P v₀)

def H1Cube (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) (3 * m) :=
  (ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m)).symm (ordinaryCube m hm P v₀)

def ordinaryTheta (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (ContinuousLoopModel.space (m + 1)) (3 * m + 1) :=
  (OrdinaryLoopRotation.BV (m + 1) (3 * m)).hom (ordinaryCube m hm P v₀)

def H1Theta (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) (3 * m + 1) :=
  (H1LoopRotation.BV (m + 1) (3 * m)).hom (H1Cube m hm P v₀)

theorem inclusion_theta (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m + 1) (H1Theta m hm P v₀) =
      ordinaryTheta m hm P v₀ := by
  rw [H1Theta, H1LoopRotation.equivalence_BV]
  change (OrdinaryLoopRotation.BV (m + 1) (3 * m)).hom
    ((ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m))
      ((ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m)).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

def tripleOrdinary {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  BasedMeridianProducts.tripleFamily P v₀ ≫ BasedMeridianProducts.forget P

def thetaHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  (OrdinaryLoopRotation.homotopy n).comp (TopCat.Homotopy.refl (tripleOrdinary P v₀))

theorem theta_sweep (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (SelfHomotopySweep.homology ((thetaHomotopy P v₀).toSSet.chainComplexMap coeff) (3 * m)).hom
      (BasedMeridianProducts.tripleSource m hm P) = ordinaryTheta m hm P v₀ := by
  have hn := SelfHomotopySweepNaturality.homology
    ((thetaHomotopy P v₀).toSSet.chainComplexMap coeff) (OrdinaryLoopRotation.chainHomotopy (m + 1))
    (push (tripleOrdinary P v₀)) (𝟙 _)
    (fun q => by rw [HomologicalComplex.id_f, Category.comp_id]; exact TimePrismNaturality.prism_pre _ _ q)
    (3 * m)
  rw [HomologicalComplex.homologyMap_id, Category.comp_id] at hn
  have he := ConcreteCategory.congr_hom hn (BasedMeridianProducts.tripleSource m hm P)
  have hc := ConcreteCategory.congr_hom
    (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (3 * m)).obj coeff).map_comp
      (BasedMeridianProducts.tripleFamily P v₀) (BasedMeridianProducts.forget P))
        (BasedMeridianProducts.tripleSource m hm P)
  change _ = (homologyPushZMod2 (BasedMeridianProducts.forget P) (3 * m)).hom
    ((homologyPushZMod2 (BasedMeridianProducts.tripleFamily P v₀) (3 * m)).hom _) at hc
  rw [BasedMeridianProducts.tripleFamily_image] at hc
  exact he.symm.trans (congrArg ((OrdinaryLoopRotation.BV (m + 1) (3 * m)).hom) hc)

end
end Finsler.MeridianRotationClasses
