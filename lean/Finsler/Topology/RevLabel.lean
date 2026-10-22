module

public import Finsler.Geometry.LevelField
public import Finsler.Geometry.PolygonDescentK
public import Finsler.Geometry.AmbientDescent
public import Finsler.Topology.CriticalCircles
public import Finsler.Geometry.MilnorEquivariance

/-! Reversal of the ambient label data. The reversal of the vertices of ambient polygons is a
continuous linear involution which keeps the polygons with nonzero vertices; the penalty and the
penalized polygon energy are invariant under it, so it keeps the set where the penalized energy is
continuously differentiable. The global solution of the ODE of a field conjugated by a continuous
linear map is the conjugate of the global solution (uniqueness of solutions), so the flow of the
field conjugated by the reversal is the conjugate of the flow, also on the polygons with nonzero
vertices; and the samples of the negative critical circle of a prime image are the reversals of
the samples of the positive one. These are the first steps of transporting the data of a label
(s, true) by the reversal to data of the label (s, false), for descents equivariant under the
reversal. -/

@[expose] public section

namespace Finsler.RevLabel

open Set Filter Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientPenalty Finsler.PolygonDescentK
open Finsler.LevelField Finsler.AmbientDescent Finsler.CriticalCircles Finsler.SobolevReverse
open Finsler.PolygonSampling Finsler.PolygonLoop Finsler.MilnorEquivariance
open scoped ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- The penalty is invariant under the reversal. -/
theorem logPen_revA (Q : ZMod N → Ambient n) : logPen (revA N Q) = logPen Q :=
  Equiv.sum_comp (Equiv.neg (ZMod N)) fun i => Real.log ‖Q i‖ ^ 2

/-- The penalized polygon energy is invariant under the reversal. -/
theorem pen_revA (F : ReversibleMetric n) (lam : ℝ) (Q : ZMod N → Ambient n) :
    pen F N lam (revA N Q) = pen F N lam Q := by
  unfold pen
  rw [logPen_revA, polyEnergyN_revA]

omit [NeZero N] in
/-- The reversal keeps the polygons with nonzero vertices. -/
theorem revA_ne_zero {Q : ZMod N → Ambient n} (hQ : ∀ j, Q j ≠ 0) (j : ZMod N) :
    revA N Q j ≠ 0 :=
  hQ (-j)

/-- The reversal keeps the set where the penalized energy is continuously differentiable. -/
theorem regSet_revA (F : ReversibleMetric n) (lam : ℝ) {Q : ZMod N → Ambient n}
    (hQ : Q ∈ regSet F N lam) : revA N Q ∈ regSet F N lam := by
  refine ⟨revA_ne_zero hQ.1, ?_⟩
  have e : pen F N lam = pen F N lam ∘ revA N := funext fun P => (pen_revA F lam P).symm
  change ContDiffAt ℝ 1 (pen F N lam) (revA N Q)
  rw [e]
  refine ContDiffAt.comp (revA N Q) ?_ (revA N).contDiff.contDiffAt
  rw [revA_revA]
  exact hQ.2

/-- The global solution of the ODE of a field w with w ∘ L = L ∘ v is the image under L of the
global solution of v. -/
theorem globalSolution_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v w : E → E) {K K' : ℝ≥0} (hv : LipschitzWith K v) (hw : LipschitzWith K' w)
    (L : E →L[ℝ] E) (hL : ∀ y, w (L y) = L (v y)) (x : E) (t : ℝ) :
    ODE.globalSolution w hw (L x) t = L (ODE.globalSolution v hv x t) := by
  have hder : ∀ s, HasDerivAt (fun s => L (ODE.globalSolution v hv x s))
      (w ((fun s => L (ODE.globalSolution v hv x s)) s)) s := by
    intro s
    have h := L.hasFDerivAt.comp_hasDerivAt s (ODE.hasDerivAt_globalSolution v hv x s)
    rw [hL]
    exact h
  have h := ODE.eq_globalSolution w hw hder
  have h0 : L (ODE.globalSolution v hv x 0) = L x := by rw [ODE.globalSolution_zero]
  rw [h0] at h
  exact (congrFun h t).symm

/-- The field conjugated by the reversal. -/
def revField (V : (ZMod N → Ambient n) → (ZMod N → Ambient n)) (Q : ZMod N → Ambient n) :
    ZMod N → Ambient n :=
  revA N (V (revA N Q))

omit [NeZero N] in
theorem revField_revA (V : (ZMod N → Ambient n) → (ZMod N → Ambient n)) (Q : ZMod N → Ambient n) :
    revField V (revA N Q) = revA N (V Q) := by
  unfold revField
  rw [revA_revA]

/-- The flow of the conjugated field is the conjugate of the flow. -/
theorem globalSolution_revField (V : (ZMod N → Ambient n) → (ZMod N → Ambient n)) {K K' : ℝ≥0}
    (hV : LipschitzWith K V) (hW : LipschitzWith K' (revField V)) (Q : ZMod N → Ambient n)
    (t : ℝ) :
    ODE.globalSolution (revField V) hW (revA N Q) t = revA N (ODE.globalSolution V hV Q t) :=
  globalSolution_conj V (revField V) hV hW (revA N) (revField_revA V) Q t

/-- The reversal does not increase the norm of ambient polygons. -/
theorem norm_revA_le (Q : ZMod N → Ambient n) : ‖revA N Q‖ ≤ ‖Q‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg Q)).mpr fun i => norm_le_pi_norm Q (-i)

theorem lipschitz_revA : LipschitzWith 1 (revA (n := n) N) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact norm_revA_le _

/-- The conjugated field is Lipschitz with the same constant. -/
theorem lipschitz_revField {V : (ZMod N → Ambient n) → (ZMod N → Ambient n)} {K : ℝ≥0}
    (hV : LipschitzWith K V) : LipschitzWith K (revField V) := by
  have h := (lipschitz_revA (n := n) (N := N)).comp (hV.comp (lipschitz_revA (n := n) (N := N)))
  rwa [one_mul, mul_one] at h

omit [NeZero N] in
/-- The conjugated field vanishes outside the reversal of the support. -/
theorem revField_ne_zero {V : (ZMod N → Ambient n) → (ZMod N → Ambient n)}
    (hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0) (P : ZMod N → Ambient n)
    (hP : revField V P ≠ 0) (j : ZMod N) : P j ≠ 0 := by
  have hV : V (revA N P) ≠ 0 := fun h => hP (by rw [revField, h, map_zero])
  have h := hV0 _ hV (-j)
  rwa [revA_apply, neg_neg] at h

/-- The reversal of ambient polygons with nonzero vertices. -/
def revOm (Q : Om n N) : Om n N := ⟨revA N Q.1, revA_ne_zero Q.2⟩

/-- **The flow of the conjugated field is the conjugate of the flow** on the polygons with nonzero
vertices. -/
theorem flowOm_revField {V : (ZMod N → Ambient n) → (ZMod N → Ambient n)} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0) (t : ℝ)
    (Q : Om n N) :
    flowOm (lipschitz_revField hV) (revField_ne_zero hV0) t (revOm Q) =
      revOm (flowOm hV hV0 t Q) := by
  apply Subtype.ext
  change ODE.globalSolution (revField V) (lipschitz_revField hV) (revA N Q.1) (max t 0) =
    revA N (ODE.globalSolution V hV Q.1 (max t 0))
  exact globalSolution_revField V hV (lipschitz_revField hV) Q.1 _

/-- **The samples of the negative circle are the reversals of the samples of the positive
circle.** -/
theorem sample_negCircle (F : ReversibleMetric n) (c : ℝ) (s : Set (Sphere n)) :
    samplePoly N '' negCircle F c s = reversePolygon '' (samplePoly N '' posCircle F c s) := by
  rw [negCircle, Set.image_image, Set.image_image]
  exact Set.image_congr fun u _ => samplePoly_reverse u

end

end Finsler.RevLabel
