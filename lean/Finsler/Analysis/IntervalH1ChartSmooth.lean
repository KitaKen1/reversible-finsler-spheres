module

public import Finsler.Analysis.IntervalH1RadialRetraction
public import Finsler.Analysis.IntervalH1SuperpositionDeriv

/-! The stereographic charts, their transitions and radial normalization are Fréchet
differentiable on the original weak H¹ graph: the rational sphere curve, the stereographic
projection with smooth denominator and the smooth radial normalization are C³, so their
superposition operators are Fréchet differentiable, and chart transitions are compositions
of such operators. Continuity of the derivatives is not asserted. -/

@[expose] public section

namespace Finsler.SobolevChartSmooth

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.RationalSphereCurve
open Finsler.SobolevSphereChart Finsler.SobolevRadialRetraction Finsler.SobolevPairMap
open Finsler.SobolevSuperpositionDeriv
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ}

theorem ratMap_contDiff3 (r : ℝ) : ContDiff ℝ 3 (ratMap (n := n) r) := by
  have hq : ContDiff ℝ 3 (fun w : Ambient n × Ambient n => aFun r w.2) := by
    have h : ContDiff ℝ 3 (fun w : Ambient n × Ambient n => r ^ 2 / 4 * ‖w.2‖ ^ 2) :=
      contDiff_const.mul (contDiff_snd.norm_sq ℝ)
    have hfun : (fun w : Ambient n × Ambient n => aFun r w.2) =
        fun w => r ^ 2 / 4 * ‖w.2‖ ^ 2 := funext fun w => aFun_eq r w.2
    rw [hfun]
    exact h
  have hc : ContDiff ℝ 3 (fun w : Ambient n × Ambient n => (1 + aFun r w.2)⁻¹) :=
    (contDiff_const.add hq).inv fun w => by have := aFun_nonneg r w.2; positivity
  have hV : ContDiff ℝ 3 (fun w : Ambient n × Ambient n => (1 - aFun r w.2) • w.1 + r • w.2) :=
    ((contDiff_const.sub hq).smul contDiff_fst).add (contDiff_snd.const_smul r)
  exact hc.smul hV

theorem denom_contDiff3 : ContDiff ℝ 3 denom := by
  have hθ : ContDiff ℝ 3 (fun s : ℝ => Real.smoothTransition (4 * (s + 3 / 4))) :=
    (Real.smoothTransition.contDiff (n := 3)).comp
      (contDiff_const.mul (contDiff_id.add contDiff_const))
  have h : ContDiff ℝ 3 (fun s : ℝ => Real.smoothTransition (4 * (s + 3 / 4)) * (1 + s) +
      (1 - Real.smoothTransition (4 * (s + 3 / 4))) * (1 / 4)) :=
    (hθ.mul (contDiff_const.add contDiff_id)).add ((contDiff_const.sub hθ).mul contDiff_const)
  exact h

theorem stereoG_contDiff3 :
    ContDiff ℝ 3 (fun p : Ambient n × Ambient n => stereoG p.1 p.2) := by
  have hs : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => ⟪p.2, p.1⟫) :=
    ContDiff.inner ℝ contDiff_snd contDiff_fst
  have hd : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => denom ⟪p.2, p.1⟫) :=
    denom_contDiff3.comp hs
  have hc : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => 2 / denom ⟪p.2, p.1⟫) :=
    contDiff_const.div hd (fun p => (denom_pos _).ne')
  have hv : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => p.2 - ⟪p.2, p.1⟫ • p.1) :=
    contDiff_snd.sub (hs.smul contDiff_fst)
  exact hc.smul hv

theorem sqDenom_contDiff3 : ContDiff ℝ 3 sqDenom := by
  have hθ : ContDiff ℝ 3 (fun s : ℝ => Real.smoothTransition (16 * (s - 3 / 16))) :=
    (Real.smoothTransition.contDiff (n := 3)).comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have h : ContDiff ℝ 3 (fun s : ℝ => Real.smoothTransition (16 * (s - 3 / 16)) * s +
      (1 - Real.smoothTransition (16 * (s - 3 / 16))) * (1 / 16)) :=
    (hθ.mul contDiff_id).add ((contDiff_const.sub hθ).mul contDiff_const)
  exact h

theorem radial_contDiff3 : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => radial p.2) := by
  have hn : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => ‖p.2‖ ^ 2) := contDiff_snd.norm_sq ℝ
  have hd : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => sqDenom (‖p.2‖ ^ 2)) :=
    sqDenom_contDiff3.comp hn
  have hs : ContDiff ℝ 3 (fun p : Ambient n × Ambient n => Real.sqrt (sqDenom (‖p.2‖ ^ 2))) :=
    hd.sqrt fun p => (sqDenom_pos _).ne'
  have hi : ContDiff ℝ 3
      (fun p : Ambient n × Ambient n => (Real.sqrt (sqDenom (‖p.2‖ ^ 2)))⁻¹) :=
    hs.inv fun p => (Real.sqrt_pos.mpr (sqDenom_pos _)).ne'
  exact hi.smul contDiff_snd

/-- The chart map on the whole graph. -/
theorem chartData_hasFDerivAt (u : SphereLoop n) (h : Space n) :
    HasFDerivAt (chartData u) (derivL (ratMap_contDiff3 1) (u.data : Space n) h) h :=
  superposition_hasFDerivAt (ratMap_contDiff3 1) (u.data : Space n) h

/-- The inverse chart as an operator on the whole graph. -/
def chartInvSpace (u : SphereLoop n) (w : Space n) : Space n :=
  mapData stereoG_contDiff (u.data : Space n) w

theorem chartInvData_eq (u v : SphereLoop n) :
    chartInvData u v = chartInvSpace u (v.data : Space n) := rfl

theorem chartInvSpace_hasFDerivAt (u : SphereLoop n) (w : Space n) :
    HasFDerivAt (chartInvSpace u) (derivL stereoG_contDiff3 (u.data : Space n) w) w :=
  superposition_hasFDerivAt stereoG_contDiff3 (u.data : Space n) w

/-- Chart transitions are Fréchet differentiable. -/
theorem transition_hasFDerivAt (u u' : SphereLoop n) (h : Space n) :
    HasFDerivAt (fun h => chartInvSpace u' (chartData u h))
      ((derivL stereoG_contDiff3 (u'.data : Space n) (chartData u h)).comp
        (derivL (ratMap_contDiff3 1) (u.data : Space n) h)) h :=
  (chartInvSpace_hasFDerivAt u' _).comp h (chartData_hasFDerivAt u h)

/-- Radial normalization is Fréchet differentiable. -/
theorem radialData_hasFDerivAt (v : Space n) :
    HasFDerivAt (radialData (n := n)) (derivL radial_contDiff3 (0 : Space n) v) v :=
  superposition_hasFDerivAt radial_contDiff3 (0 : Space n) v

end

end Finsler.SobolevChartSmooth
