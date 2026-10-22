module

public import Finsler.Loop.OppositeMeridianEvaluationPoint
public import Finsler.Loop.MeridianThetaCutCoefficient
public import Finsler.Loop.GeometricTimeCupCochain

/-! Localize the EXISTING original H1 evaluation class. The actual
retained-loop evaluation is exactly the original start-point map,
throughout the real near-diagonal tube, not only on its center.
Consequently the ORIGINAL split cup is literally zero on every
patch whose start point runs on the fixed meridian, for eta<=1. -/
@[expose] public section
namespace Finsler.LocalizedCutEvaluationCochain
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.CochainComparison
open Finsler.SupportedSelfCut Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def loopCocycle (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {η : ℝ} (hη : 0 < η) :
    singularCochainGroup (ZMod 2) (Loops n) n :=
  cochainPullback (MeridianThetaCutCoefficient.evaluation n) n
    (LocalizedSphereTopCocycle.cocycle n hn Q hη)

theorem loop_closed (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {η : ℝ} (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (Loops n) n (loopCocycle n hn Q hη) = 0 :=
  cochainPullback_cocycle _ n _ (LocalizedSphereTopCocycle.closed n hn Q hη)

theorem loop_class (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {η : ℝ} (hη : 0 < η) :
    cocycleClass (Loops n) n (loopCocycle n hn Q hη) (loop_closed n hn Q hη) =
      (cohPullback (MeridianThetaCutCoefficient.evaluation n) n).hom (SphereTopClass.topClass n hn) := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (BorelEvaluation.sphere n))
    (singularCochainComplexZMod2.map (MeridianThetaCutCoefficient.evaluation n).op) n
    (LocalizedSphereTopCocycle.cocycle n hn Q hη) (LocalizedSphereTopCocycle.closed n hn Q hη)
    (loop_closed n hn Q hη)
  change (cohPullback (MeridianThetaCutCoefficient.evaluation n) n).hom
    (CochainClass.classOf (cochainCxZMod2 (BorelEvaluation.sphere n)) n
      (LocalizedSphereTopCocycle.cocycle n hn Q hη) (LocalizedSphereTopCocycle.closed n hn Q hη)) =
        cocycleClass (Loops n) n (loopCocycle n hn Q hη) (loop_closed n hn Q hη) at he
  rw [LocalizedSphereTopCocycle.top_class] at he
  exact he.symm

def startPoint (n : ℕ) : SelfCutThomCocycle.parameters n ⟶ BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun z => point z.2, continuous_point.comp continuous_snd⟩

def nearStart (n : ℕ) (r : ℝ) : TopCat.of (neighborhood n r) ⟶ BorelEvaluation.sphere n :=
  SupportedCap.subspaceMap (SelfCutThomCocycle.parameters n) (neighborhood n r) ≫ startPoint n

theorem retained_evaluation (n : ℕ) {r : ℝ} (hr : r ≤ 1) :
    TopCat.ofHom (retained n hr) ≫ MeridianThetaCutCoefficient.evaluation n = nearStart n r := by
  ext z : 1
  apply Subtype.ext
  exact basepoint_right (toTube n hr z)

theorem retained_pullback (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {η : ℝ} (hη : 0 < η)
    {r : ℝ} (hr : r ≤ 1) :
    cochainPullback (TopCat.ofHom (retained n hr)) n (loopCocycle n hn Q hη) =
      cochainPullback (nearStart n r) n (LocalizedSphereTopCocycle.cocycle n hn Q hη) := by
  rw [loopCocycle, ← pullback_comp, retained_evaluation]

theorem fixed_meridian_retained_zero {n : ℕ} (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : r ≤ 1) {X : TopCat.{0}}
    (f : X ⟶ TopCat.of (neighborhood n r))
    (hf : ∀ x, ∃ t : _root_.unitInterval, nearStart n r (f x) = meridian P v₀ t) :
    cochainPullback f n (cochainPullback (TopCat.ofHom (retained n hr)) n
      (loopCocycle n hn (OppositeMeridianEvaluationPoint.target v₀) hη)) = 0 := by
  rw [retained_pullback, ← pullback_comp]
  exact OppositeMeridianEvaluationPoint.family_pullback_zero hn P v₀ hη hη1 (f ≫ nearStart n r) hf

theorem fixed_meridian_splitCup_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) {X : TopCat.{0}}
    (f : X ⟶ TopCat.of (neighborhood (m + 1) r))
    (hf : ∀ x, ∃ t : _root_.unitInterval, nearStart (m + 1) r (f x) = meridian P v₀ t) :
    cochainPullback f (p + (m + 1))
      (GeometricTimeCupCochain.splitCup m p hr T (m + 1)
        (loopCocycle (m + 1) (by omega) (OppositeMeridianEvaluationPoint.target v₀) hη)) = 0 := by
  rw [GeometricTimeCupCochain.splitCup, cochainCup_naturality,
    fixed_meridian_retained_zero (by omega) P v₀ hη hη1 hr f hf, cochainCup_zero_right]

end
end Finsler.LocalizedCutEvaluationCochain
