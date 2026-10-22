module

public import Finsler.Loop.NativeSameLegOriginalCapClass

/-! The ORIGINAL named localized parameter cut cochain, including
its actual tested transgression and retained evaluation factors,
has ZERO absolute class on the actual same-leg local source patch.
No changed cap, replacement coefficient, or relative/global zero is
asserted by this absolute local class computation. -/
@[expose] public section
namespace Finsler.NativeSameLegLocalizedClass
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def output (m p : ℕ) (Q : Sphere (m + 1)) {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :=
  GeometricTimeCupCochain.splitCup m p hr T (m + 1)
    (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) Q hη)

theorem output_closed (m p : ℕ) (Q : Sphere (m + 1)) {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) (p + (m + 1))
      (output m p Q hr hη T) = 0 :=
  cochainCupZMod2_respects_cocycles p (m + 1) _ _
    (NormalizedSelfCut.testedCocycle_closed (m + 1) p hr T hT)
    (cochainPullback_cocycle (TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr)) (m + 1) _
      (LocalizedCutEvaluationCochain.loop_closed (m + 1) (by omega) Q hη))

theorem original_eq (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (Q : Sphere (m + 1))
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    NativeSameLegOriginalCapClass.original m P v₀ k isLong hρ hρr (p + (m + 1)) (output m p Q hr hη T) =
      cochainPullback (family P v₀ k isLong) ((m + 1) + (p + (m + 1)))
        (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T) := rfl

theorem original_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (Q : Sphere (m + 1))
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (localSpace P v₀ k) ((m + 1) + (p + (m + 1)))
      (cochainPullback (family P v₀ k isLong) ((m + 1) + (p + (m + 1)))
        (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T)) = 0 :=
  pullback_closed _ _ _ (LocalizedParameterCutCochain.closed m p Q hρ hρr hr hη T hT)

theorem original_class_zero (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    (k : Fin 3) (isLong : Bool) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    CochainClass.classOf (cochainCxZMod2 (localSpace P v₀ k)) ((m + 1) + (p + (m + 1)))
      (cochainPullback (family P v₀ k isLong) ((m + 1) + (p + (m + 1)))
        (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T))
      (original_closed m p P v₀ k isLong Q hρ hρr hr hη T hT) = 0 := by
  have he := NativeSameLegOriginalCapClass.original_class_zero m hm P v₀ k isLong hρ hρr hρ1
    (p + (m + 1)) (output m p Q hr hη T) (output_closed m p Q hr hη T hT)
  exact he

end
end Finsler.NativeSameLegLocalizedClass
