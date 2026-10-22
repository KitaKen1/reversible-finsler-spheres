module

public import Finsler.Loop.NativeThetaCoefficientThreeNorth
public import Finsler.Loop.LocalizedParameterCutCochain
public import Finsler.Loop.NativePairDoublePrismSource

/-! Expand the SAME original global time-cup cochain into the ORIGINAL
cut-time prism followed by the ORIGINAL pre-time parameter cochain.
All true degree transports are kept and aligned with the native branch
cochain degree3m+2. No operation or auxiliary radius is replaced. -/
@[expose] public section
namespace Finsler.GlobalCutTimePrismAlignment
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem pre_trans (X : TopCat.{0}) {i j k : ℕ} (h : i = j) (h' : j = k)
    (φ : singularCochainGroup (ZMod 2) X k) :
    CochainDegreeTransport.pre X h (CochainDegreeTransport.pre X h' φ) =
      CochainDegreeTransport.pre X (h.trans h') φ := by
  subst j
  subst k
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem pre_prism {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    {i j : ℕ} (h : i = j) (φ : singularCochainGroup (ZMod 2) Y (j + 1)) :
    CochainDegreeTransport.pre X h ((H.toSSet.chainComplexMap coeff).hom j (j + 1) ≫ φ) =
      (H.toSSet.chainComplexMap coeff).hom i (i + 1) ≫
        CochainDegreeTransport.pre Y (congrArg (· + 1) h) φ := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem original_timecup_prism (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    GeometricTimeCupCochain.cochain m p hρ hρr hr T (m + 1)
      (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) Q hη) =
    SelfCutTimePrism.prism (m + 1) ((m + p) + (m + 1)) ≫
      CochainDegreeTransport.pre (SelfCutThomCocycle.parameters (m + 1))
        (by omega : ((m + p) + (m + 1)) + 1 = (m + 1) + (p + (m + 1)))
        (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T) := by
  unfold GeometricTimeCupCochain.cochain
  rw [TimeShuffleComparison.rectangle_eq_prism]
  rfl

def parameterCochain (m : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) (3 * m + 2) :=
  CochainDegreeTransport.pre (SelfCutThomCocycle.parameters (m + 1))
    (by omega : 3 * m + 2 = (m + 1) + (m + (m + 1)))
    (LocalizedParameterCutCochain.cochain m m Q hρ hρr hr hη
      (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))

theorem parameter_closed (m : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) (3 * m + 2)
      (parameterCochain m Q hρ hρr hr hη) = 0 :=
  CochainDegreeTransport.closed _ _ _ (LocalizedParameterCutCochain.closed m m Q hρ hρr hr hη _ (classRepr_isCocycle _ m _))

theorem original_cast_timecup_prism (m : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    NativeFixedReturnRotationZero.castCochain m Q hη hρ hρr hr =
      SelfCutTimePrism.prism (m + 1) (3 * m + 1) ≫ parameterCochain m Q hρ hρr hr hη := by
  unfold NativeFixedReturnRotationZero.castCochain LocalizedThetaCutCoefficient.cochain
  rw [original_timecup_prism]
  let hK : 3 * m + 1 = (m + m) + (m + 1) := by omega
  let hD : ((m + m) + (m + 1)) + 1 = (m + 1) + (m + (m + 1)) := by omega
  let φ := LocalizedParameterCutCochain.cochain m m Q hρ hρr hr hη
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))
  have he := pre_prism (SelfCutTimePrism.cylinder (m + 1)) hK
    (CochainDegreeTransport.pre (SelfCutThomCocycle.parameters (m + 1)) hD φ)
  have hc := pre_trans (SelfCutThomCocycle.parameters (m + 1)) (congrArg (· + 1) hK) hD φ
  exact he.trans (congrArg (fun a : singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) (3 * m + 2) =>
    SelfCutTimePrism.prism (m + 1) (3 * m + 1) ≫ a) hc)

end
end Finsler.GlobalCutTimePrismAlignment
