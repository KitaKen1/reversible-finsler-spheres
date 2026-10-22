module

public import Finsler.Analysis.H1TraceClosedGraph
public import Finsler.Analysis.IntervalH1Concat

/-! Strong H¹ continuity of fixed-split concatenation by the closed graph theorem.
The domain is the genuine closed linear subspace of matching endpoint pairs. -/

@[expose] public section

namespace Finsler.H1ConcatContinuity

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevConcat
open Finsler.SobolevSpherePath Finsler.H1TraceClosedGraph
open Set
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000

def traceDifference (n : ℕ) : (Space n × Space n) →L[ℝ] Ambient n :=
  (traceOneL n).comp (ContinuousLinearMap.fst ℝ (Space n) (Space n)) -
    (traceZeroL n).comp (ContinuousLinearMap.snd ℝ (Space n) (Space n))

def matching (n : ℕ) : Submodule ℝ (Space n × Space n) := (traceDifference n).ker

instance : CompleteSpace (matching n) :=
  (traceDifference n).isClosed_ker.isComplete.completeSpace_coe

theorem matching_trace (p : matching n) :
    continuousRepresentative p.val.1 1 = continuousRepresentative p.val.2 0 := by
  have h : continuousRepresentative p.val.1 1 - continuousRepresentative p.val.2 0 = 0 :=
    p.property
  exact sub_eq_zero.mp h

theorem left_time_mem {a τ : ℝ} (ha0 : 0 < a) (hτ : τ ∈ Icc (0 : ℝ) 1) (h : τ ≤ a) :
    a⁻¹ * τ ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (inv_nonneg.mpr ha0.le) hτ.1
  · calc
      a⁻¹ * τ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha0.le)
      _ = 1 := inv_mul_cancel₀ ha0.ne'

theorem right_time_mem {a τ : ℝ} (ha1 : a < 1) (hτ : τ ∈ Icc (0 : ℝ) 1) (h : a ≤ τ) :
    rightMap a τ ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 < 1 - a := sub_pos.mpr ha1
  have he : rightMap a τ = (τ - a) / (1 - a) := by
    unfold rightMap
    field_simp
    ring
  rw [he]
  exact ⟨div_nonneg (sub_nonneg.mpr h) hp.le,
    (div_le_one hp).mpr (by linarith [hτ.2])⟩

def firstL (n : ℕ) : matching n →L[ℝ] Space n :=
  (ContinuousLinearMap.fst ℝ (Space n) (Space n)).comp (matching n).subtypeL

def secondL (n : ℕ) : matching n →L[ℝ] Space n :=
  (ContinuousLinearMap.snd ℝ (Space n) (Space n)).comp (matching n).subtypeL

def evaluation (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (t : ClosedInterval) :
    matching n →L[ℝ] Ambient n := by
  classical
  exact if h : (t : ℝ) ≤ a then
    (traceL n ⟨a⁻¹ * t, left_time_mem ha0 t.property h⟩).comp (firstL n)
  else
    (traceL n ⟨rightMap a t, right_time_mem ha1 t.property (lt_of_not_ge h).le⟩).comp
      (secondL n)

theorem evaluation_apply (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (p : matching n) (t : ClosedInterval) :
    evaluation (n := n) a ha0 ha1 t p = continuousRepresentative (concat p.val.1 p.val.2 ha0 ha1) t := by
  classical
  by_cases h : (t : ℝ) ≤ a
  · simp only [evaluation, dite_eq_left h]
    change continuousRepresentative p.val.1 (a⁻¹ * t) = _
    exact (representative_concat_left p.val.1 p.val.2 ha0 ha1 ⟨t.property.1, h⟩).symm
  · simp only [evaluation, dite_eq_right h]
    change continuousRepresentative p.val.2 (rightMap a t) = _
    exact (representative_concat_right p.val.1 p.val.2 ha0 ha1 (matching_trace p)
      ⟨(lt_of_not_ge h).le, t.property.2⟩).symm

def concatenationLinear (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : matching n →ₗ[ℝ] Space n where
  toFun p := concat p.val.1 p.val.2 ha0 ha1
  map_add' p q := by
    apply eq_of_representative_eqOn
    intro τ hτ
    let t : ClosedInterval := ⟨τ, hτ⟩
    calc
      _ = evaluation (n := n) a ha0 ha1 t (p + q) := (evaluation_apply (n := n) a ha0 ha1 (p + q) t).symm
      _ = evaluation (n := n) a ha0 ha1 t p + evaluation (n := n) a ha0 ha1 t q := map_add _ _ _
      _ = continuousRepresentative (concat p.val.1 p.val.2 ha0 ha1) τ +
          continuousRepresentative (concat q.val.1 q.val.2 ha0 ha1) τ :=
        congrArg₂ (fun x y : Ambient n => x + y)
          (evaluation_apply (n := n) a ha0 ha1 p t) (evaluation_apply (n := n) a ha0 ha1 q t)
      _ = _ := (continuousRepresentative_add _ _ hτ).symm
  map_smul' c p := by
    apply eq_of_representative_eqOn
    intro τ hτ
    let t : ClosedInterval := ⟨τ, hτ⟩
    calc
      _ = evaluation (n := n) a ha0 ha1 t (c • p) := (evaluation_apply (n := n) a ha0 ha1 (c • p) t).symm
      _ = c • evaluation (n := n) a ha0 ha1 t p := map_smul _ _ _
      _ = c • continuousRepresentative (concat p.val.1 p.val.2 ha0 ha1) τ :=
        congrArg (fun x : Ambient n => c • x) (evaluation_apply (n := n) a ha0 ha1 p t)
      _ = _ := (continuousRepresentative_smul _ _ hτ).symm

theorem continuous_concatenation (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Continuous (concatenationLinear (n := n) a ha0 ha1) := by
  letI : NormedSpace ℝ (matching n) := Submodule.normedSpace (matching n)
  apply continuous_of_traces (n := n) (concatenationLinear (n := n) a ha0 ha1)
  intro t
  exact (evaluation (n := n) a ha0 ha1 t).continuous.congr
    (fun p => evaluation_apply (n := n) a ha0 ha1 p t)

def concatenationCLM (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : matching n →L[ℝ] Space n where
  toLinearMap := concatenationLinear (n := n) a ha0 ha1
  cont := continuous_concatenation (n := n) a ha0 ha1


end
end Finsler.H1ConcatContinuity
