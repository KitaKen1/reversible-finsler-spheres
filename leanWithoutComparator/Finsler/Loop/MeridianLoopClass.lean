module

public import Finsler.Loop.MeridianEquatorHomology
public import Finsler.Loop.ContinuousLoopSweep
public import Finsler.Topology.SphereUnitCandidate
public import Finsler.Loop.FullRelativeSplit

/-! Actual ordinary and H1 meridian-loop homology classes and the
actual transgression of the sphere top class. Their pairing reduces
to ONE concrete sphere sweep coefficient. That coefficient is not
assumed to be one; its geometric computation is the next task. -/

@[expose] public section
namespace Finsler.MeridianLoopClass
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def ordinaryClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (ContinuousLoopModel.space (m + 1)) m :=
  (homologyPushZMod2 (ordinary P v₀) m).hom (MeridianEquatorHomology.fundamental m hm P)

def H1Class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) m :=
  (ContinuousLoopHomologyEquivalence.homology (m + 1) m).symm (ordinaryClass m hm P v₀)

theorem inclusion_H1Class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ContinuousLoopHomologyEquivalence.homology (m + 1) m (H1Class m hm P v₀) =
      ordinaryClass m hm P v₀ :=
  (ContinuousLoopHomologyEquivalence.homology (m + 1) m).apply_symm_apply _

def sweepClass (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (BorelEvaluation.sphere (m + 1)) (m + 1) :=
  (ContinuousLoopSweep.homology (m + 1) m).hom (ordinaryClass m hm P v₀)

def sweepCoefficient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) : ZMod 2 :=
  SphereTopClass.homologyEquiv (m + 1) (by omega) (sweepClass m hm P v₀)

def ordinaryTransgression (m : ℕ) : cohomologyZMod2 (ContinuousLoopModel.space (m + 1)) m :=
  ContinuousLoopSweep.transgression (m + 1) m (SphereTopClass.topClass (m + 1) (by omega))

def H1TransgressionClass (m : ℕ) : cohomologyZMod2 (Loops (m + 1)) m :=
  ContinuousLoopSweep.H1Transgression (m + 1) m (SphereTopClass.topClass (m + 1) (by omega))

theorem sphere_top_evaluation (n : ℕ) (hn : 1 ≤ n) (z : homologyZMod2 (BorelEvaluation.sphere n) n) :
    (kroneckerMap (BorelEvaluation.sphere n) n).hom (SphereTopClass.topClass n hn) z =
      SphereTopClass.homologyEquiv n hn z := by
  let e := SphereTopClass.homologyEquiv n hn
  let φ := (kroneckerMap (BorelEvaluation.sphere n) n).hom (SphereTopClass.topClass n hn)
  have hu : φ (e.symm 1) = 1 := SphereUnitCandidate.top_evaluation_one n hn
  have hz : z = (e z) • e.symm 1 := by
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  change φ z = e z
  calc
    φ z = φ ((e z) • e.symm 1) := congrArg φ hz
    _ = (e z) • φ (e.symm 1) := map_smul φ _ _
    _ = e z := by rw [hu, smul_eq_mul, mul_one]

theorem ordinary_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (ContinuousLoopModel.space (m + 1)) m).hom (ordinaryTransgression m)
      (ordinaryClass m hm P v₀) =
    (kroneckerMap (BorelEvaluation.sphere (m + 1)) (m + 1)).hom
      (SphereTopClass.topClass (m + 1) (by omega)) (sweepClass m hm P v₀) :=
  ContinuousLoopSweep.pairing _ _ _ _

theorem H1_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (Loops (m + 1)) m).hom (H1TransgressionClass m) (H1Class m hm P v₀) =
    (kroneckerMap (BorelEvaluation.sphere (m + 1)) (m + 1)).hom
      (SphereTopClass.topClass (m + 1) (by omega)) (sweepClass m hm P v₀) := by
  change (kroneckerMap (Loops (m + 1)) m).hom
    (ContinuousLoopSweep.H1Transgression (m + 1) m _) (H1Class m hm P v₀) = _
  rw [ContinuousLoopSweep.H1_pairing, inclusion_H1Class]
  rfl

theorem pairing_coefficient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (Loops (m + 1)) m).hom (H1TransgressionClass m) (H1Class m hm P v₀) =
      sweepCoefficient m hm P v₀ := by
  rw [H1_pairing, sphere_top_evaluation]
  rfl

def relativeTransgressionClass (m : ℕ) : RelativeCup.cohomology (fullPair (m + 1)) m :=
  FullRelativeSplit.lift (m + 1) m (H1TransgressionClass m)

theorem relative_absolute (m : ℕ) (hm : 1 ≤ m) :
    FullRelativeSplit.absolute (m + 1) m (relativeTransgressionClass m) = H1TransgressionClass m :=
  FullRelativeSplit.absolute_lift _ _ _
    (ConstantRelativeLift.restriction_zero (m + 1) m hm (by omega) _)

theorem relative_pairing_coefficient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    RelativeKronecker.comparison (fullPair (m + 1)) m (relativeTransgressionClass m)
      (ConstantRelativePairing.homologyToRelative (m + 1) m (H1Class m hm P v₀)) =
      sweepCoefficient m hm P v₀ := by
  rw [relativeTransgressionClass, FullRelativeSplit.pairing _ _ _
    (ConstantRelativeLift.restriction_zero (m + 1) m hm (by omega) _), pairing_coefficient]

end
end Finsler.MeridianLoopClass
