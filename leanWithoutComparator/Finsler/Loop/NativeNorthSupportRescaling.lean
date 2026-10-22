module

public import Finsler.Loop.NativeNorthOrderedCharts
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance

/-! Rescale BOTH original meridian times to their northern halves.
The actual time-stretching homotopy preserves the original support
complement on ALL original boundary faces, even though it need not
preserve the narrower old boundary subset itself. Genuine TopPair
homotopy therefore preserves pullback of the SAME supported cut class. -/
@[expose] public section
namespace Finsler.NativeNorthSupportRescaling
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.NativeMeridianPairCoordinates
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem clock_zero (t : ClosedInterval) : NativeDoubleSweepClosing.clock 0 t = MeridianQuarterIncidence.northTime t := by
  apply Subtype.ext
  change (1 + (0 : ℝ)) * (t : ℝ) / 2 = (t : ℝ) / 2
  ring

theorem meridian_clock_end_excluded {n : ℕ} (P : Sphere n) (v₀ v : equator P) (s : ClosedInterval) :
    meridian P v (NativeDoubleSweepClosing.clock s 1) ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
  apply Or.inr
  apply le_of_not_gt
  intro h
  have ht := MeridianNorthParameterChart.time_lt_half P v (NativeDoubleSweepClosing.clock s 1) h
  change (1 + (s : ℝ)) * 1 / 2 < 1 / 2 at ht
  linarith [s.property.1]

def ambientHomotopy {n : ℕ} (P : Sphere n) :
    TopCat.Homotopy (NativeNorthOrderedCharts.northParameters P) (𝟙 (parameters P)) where
  toFun z := ((NativeDoubleSweepClosing.clock z.1 z.2.1.1, z.2.1.2),
    ((NativeDoubleSweepClosing.clock z.1 z.2.2.1.1, z.2.2.1.2), z.2.2.2))
  continuous_toFun := by
    dsimp [NativeDoubleSweepClosing.clock]
    fun_prop
  map_zero_left z := by
    change ((NativeDoubleSweepClosing.clock 0 z.1.1, z.1.2),
      ((NativeDoubleSweepClosing.clock 0 z.2.1.1, z.2.1.2), z.2.2)) = _
    rw [clock_zero, clock_zero]
    rfl
  map_one_left z := by
    change ((NativeDoubleSweepClosing.clock 1 z.1.1, z.1.2),
      ((NativeDoubleSweepClosing.clock 1 z.2.1.1, z.2.1.2), z.2.2)) = _
    rw [NativeDoubleSweepClosing.clock_one, NativeDoubleSweepClosing.clock_one]
    rfl

private theorem excluded_outside {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P)
    (hz : meridian P z.1.2 z.1.1 ∈ NorthMeridianEvaluationPoint.excluded P v₀ ∨
      meridian P z.2.1.2 z.2.1.1 ∈ NorthMeridianEvaluationPoint.excluded P v₀) : z ∉ NativeQuarterSupport.good P v₀ := by
  intro hg
  rcases hz with h | h
  · have hd := NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨_, h⟩
    linarith [hg.1]
  · have hd := NorthMeridianEvaluationPoint.excluded_distance P v₀ ⟨_, h⟩
    linarith [hg.2]

theorem homotopy_boundary {n : ℕ} (P : Sphere n) (v₀ : equator P) (s : ClosedInterval)
    (z : parameters P) (hz : z ∈ NativePairBoundaryRelativeCut.bad P v₀) :
    ambientHomotopy P (s, z) ∉ NativeQuarterSupport.good P v₀ := by
  apply excluded_outside P v₀
  change meridian P z.1.2 (NativeDoubleSweepClosing.clock s z.1.1) ∈ _ ∨
    meridian P z.2.1.2 (NativeDoubleSweepClosing.clock s z.2.1.1) ∈ _
  rcases hz with h | h | h | h | h | h
  · left
    rw [h, NativeDoubleSweepClosing.clock_at_zero]
    simpa only [Path.source] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 0
  · left
    rw [h]
    exact meridian_clock_end_excluded P v₀ _ s
  · right
    rw [h, NativeDoubleSweepClosing.clock_at_zero]
    simpa only [Path.source] using NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ 0
  · right
    rw [h]
    exact meridian_clock_end_excluded P v₀ _ s
  · left
    rw [h]
    exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ _
  · right
    rw [h]
    exact NorthMeridianEvaluationPoint.fixed_meridian_excluded P v₀ _

def northPair {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativePairBoundaryRelativeCut.pair P v₀ ⟶ NativeQuarterSupport.supportPair P v₀ :=
  TopPair.ofSubsetMap (B := NativePairBoundaryRelativeCut.bad P v₀)
    (B' := (NativeQuarterSupport.good P v₀)ᶜ) (NativeNorthOrderedCharts.northParameters P)
    (fun z hz => (ambientHomotopy P).apply_zero z ▸ homotopy_boundary P v₀ 0 z hz)

def pairHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Homotopy (northPair P v₀) (NativeQuarterSupport.boundaryToSupport P v₀) :=
  TopPair.ofSubsetHomotopy (B := NativePairBoundaryRelativeCut.bad P v₀)
    (B' := (NativeQuarterSupport.good P v₀)ᶜ) (ambientHomotopy P) (homotopy_boundary P v₀)

theorem cohomology_equal {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (northPair P v₀) q =
      TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativeQuarterSupport.boundaryToSupport P v₀) q :=
  (pairHomotopy P v₀).congr_singularCohomologyMap coeff (ZMod 2) coeff q

theorem original_support_class_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (northPair P v₀)
      ((m + 1) + (m + (m + 1)))).hom
      (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8) =
      NativePairBoundaryRelativeCut.originalPrimitiveClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) :=
  (congrArg (fun f => f.hom (NativeQuarterSupport.originalPrimitiveSupportClass m P v₀ b hρ hρr hr hη hr8 hη8))
    (cohomology_equal P v₀ _)).trans
      (NativeQuarterSupport.originalPrimitiveSupportClass_pullback m P v₀ b hρ hρr hr hη hr8 hη8)

end
end Finsler.NativeNorthSupportRescaling
