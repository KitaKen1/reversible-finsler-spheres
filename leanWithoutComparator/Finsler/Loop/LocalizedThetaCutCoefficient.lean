module

public import Finsler.Loop.FixedMeridianTimeCupZero

/-! The SAME unresolved global Theta-cut coefficient is represented
by the ORIGINAL geometric time-cup cochain with the EXISTING sphere
evaluation class localized near Q. This preserves the original
tested class, Theta input, auxiliary Thom radii and normalization. -/
@[expose] public section
namespace Finsler.LocalizedThetaCutCoefficient
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.LocalizedCutEvaluationCochain Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

def cochain (m : ℕ) (Q : Sphere (m + 1)) {η ρ r : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    singularCochainGroup (ZMod 2) (Loops (m + 1)) ((m + m) + (m + 1)) :=
  GeometricTimeCupCochain.cochain m m hρ hρr hr
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (m + 1)
    (loopCocycle (m + 1) (by omega) Q hη)

theorem closed (m : ℕ) (Q : Sphere (m + 1)) {η ρ r : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) ((m + m) + (m + 1)) (cochain m Q hη hρ hρr hr) = 0 :=
  GeometricTimeCupCochain.closed m m hρ hρr hr _ (m + 1) _
    (classRepr_isCocycle _ m _) (loop_closed (m + 1) (by omega) Q hη)

theorem class_eq (m : ℕ) (hm : 1 ≤ m) (Q : Sphere (m + 1)) {η ρ r : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    cocycleClass _ _ (cochain m Q hη hρ hρr hr) (closed m Q hη hρ hρr hr) =
      MeridianThetaCutCoefficient.testClass m := by
  have hb := loop_class (m + 1) (by omega) Q hη
  change cocycleClass _ _ (loopCocycle (m + 1) (by omega) Q hη) (loop_closed (m + 1) (by omega) Q hη) =
    MeridianThetaCutCoefficient.evaluationClass m at hb
  have hc := GlobalTimeCupCohomology.product_cocycle m hρ hρr hr m (m + 1)
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (loopCocycle (m + 1) (by omega) Q hη)
    (classRepr_isCocycle _ m _) (loop_closed (m + 1) (by omega) Q hη)
  rw [cocycleClass_classRepr, hb] at hc
  exact hc.symm.trans (CanonicalGlobalTimeCup.product_compare m hm m (m + 1) hρ hρr hr _ _)

theorem coefficient_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (Q : Sphere (m + 1)) {η ρ r : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    (kroneckerMap (Loops (m + 1)) ((m + m) + (m + 1))).hom
      (cocycleClass _ _ (cochain m Q hη hρ hρr hr) (closed m Q hη hρ hρr hr))
      (MeridianThetaCutCoefficient.thetaInput m hm P v₀) = MeridianThetaCutCoefficient.coefficient m hm P v₀ := by
  rw [class_eq m hm Q hη hρ hρr hr]
  rfl

theorem fixed_meridian_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    {X : TopCat.{0}} (f : X ⟶ Loops (m + 1))
    (hf : ∀ x, ∃ t : _root_.unitInterval, H1FiberBase.point (f x) = meridian P v₀ t) :
    cochainPullback f ((m + m) + (m + 1))
      (cochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr) = 0 :=
  FixedMeridianTimeCupZero.original_cochain_zero m m P v₀ hρ hρr hr hη hη1 _ f hf

end
end Finsler.LocalizedThetaCutCoefficient
