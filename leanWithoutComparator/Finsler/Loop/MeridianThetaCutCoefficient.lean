module

public import Finsler.Loop.MeridianRotationClasses
public import Finsler.Loop.CanonicalGlobalSelfCutFiltered

/-! A concrete NEXT UNIT computation: actual primitive omega,
actual triple-meridian/BV Theta candidate, actual evaluation top
class, and the ORIGINAL genuine self-cut. The coefficient is defined
and all comparison identities are proved; coefficient1 is NOT assumed. -/
@[expose] public section
namespace Finsler.MeridianThetaCutCoefficient
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def evaluation (n : ℕ) : Loops n ⟶ BorelEvaluation.sphere n :=
  FullLoopModel.insert n ≫ BorelEvaluation.fullEval n

def evaluationClass (m : ℕ) : cohomologyZMod2 (Loops (m + 1)) (m + 1) :=
  (cohPullback (evaluation (m + 1)) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))

def thetaInput (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) ((m + m) + (m + 1)) :=
  (eqToHom (congrArg (fun q => homologyZMod2 (Loops (m + 1)) q)
    (by omega : 3 * m + 1 = (m + m) + (m + 1)))).hom (MeridianRotationClasses.H1Theta m hm P v₀)

def testClass (m : ℕ) : cohomologyZMod2 (Loops (m + 1)) ((m + m) + (m + 1)) :=
  CanonicalGlobalTimeCup.product m m (m + 1) (MeridianLoopClass.H1TransgressionClass m) (evaluationClass m)

def coefficient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) : ZMod 2 :=
  (kroneckerMap _ ((m + m) + (m + 1))).hom (testClass m) (thetaInput m hm P v₀)

def cutTheta (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    homologyZMod2 (Loops (m + 1)) (m + 1) :=
  (CanonicalGlobalSelfCut.map m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)).hom
    (thetaInput m hm P v₀)

theorem cut_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap _ (m + 1)).hom (evaluationClass m) (cutTheta m hm P v₀) = coefficient m hm P v₀ :=
  CanonicalGlobalSelfCut.pairing m m (m + 1) _ _ _

theorem evaluation_coefficient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    SphereTopClass.homologyEquiv (m + 1) (by omega)
      ((homologyPushZMod2 (evaluation (m + 1)) (m + 1)).hom (cutTheta m hm P v₀)) =
        coefficient m hm P v₀ := by
  have hn := congrArg (fun φ : homologyDualZMod2 (Loops (m + 1)) (m + 1) => φ (cutTheta m hm P v₀))
    (kroneckerMap_naturality_apply (evaluation (m + 1)) (m + 1) (SphereTopClass.topClass (m + 1) (by omega)))
  have he := MeridianLoopClass.sphere_top_evaluation (m + 1) (by omega)
    ((homologyPushZMod2 (evaluation (m + 1)) (m + 1)).hom (cutTheta m hm P v₀))
  exact he.symm.trans (hn.symm.trans (cut_pairing m hm P v₀))

theorem evaluation_fundamental_multiple (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (homologyPushZMod2 (evaluation (m + 1)) (m + 1)).hom (cutTheta m hm P v₀) =
      coefficient m hm P v₀ • SphereUnitCandidate.fundamental (m + 1) (by omega) := by
  apply (SphereTopClass.homologyEquiv (m + 1) (by omega)).injective
  rw [evaluation_coefficient, map_smul, SphereUnitCandidate.fundamental,
    LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

theorem original_prism_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) m)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) m T = 0)
    (hc : cocycleClass _ m T hT = MeridianLoopClass.H1TransgressionClass m) :
    (kroneckerMap _ (m + 1)).hom (evaluationClass m)
      (((PrismSelfCut.operation m m hρ hρr hr T hT).homology (m + 1)).hom (thetaInput m hm P v₀)) =
        coefficient m hm P v₀ := by
  have h := congrArg (fun f => (kroneckerMap _ (m + 1)).hom (evaluationClass m)
      (f.hom (thetaInput m hm P v₀)))
    (CanonicalGlobalSelfCut.original_prism_eq m hm m (m + 1) hρ hρr hr T hT)
  rw [hc] at h
  exact h.trans (cut_pairing m hm P v₀)

end
end Finsler.MeridianThetaCutCoefficient
