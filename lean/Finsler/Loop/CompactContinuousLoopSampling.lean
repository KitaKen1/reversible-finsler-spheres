module

public import Finsler.Loop.ContinuousLoopModel
public import Finsler.Geometry.PolygonSampling
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Sets.Compacts

/-! A SINGLE subdivision samples every loop of an actual compact
ordinary continuous-loop family into genuine short polygons. No H1
energy bound is assumed on the ordinary continuous loops. -/

@[expose] public section
namespace Finsler.CompactContinuousLoopSampling
open CategoryTheory TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevCircleRepresentative
open Finsler.PolygonCritical Finsler.PolygonLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
local notation "Circ" => SobolevCircleRepresentative.Circle

def sample {n : ℕ} (N : ℕ) (u : ContinuousLoopModel.space n) : ZMod N → Sphere n :=
  fun i => u (((sampleTime N i : ℝ)) : Circ)

theorem sample_continuous (n N : ℕ) : Continuous (sample (n := n) N) := by
  apply continuous_pi
  intro i
  exact continuous_eval_const _

theorem sample_H1 (n N : ℕ) (u : SphereLoop n) :
    sample N (ContinuousLoopModel.inclusion n u) = PolygonSampling.samplePoly N u := by
  funext i
  exact sphereCircleMap_coe u (sampleTime N i)

theorem sample_natCast {n N : ℕ} [NeZero N] (u : ContinuousLoopModel.space n)
    {k : ℕ} (hk : k < N) : sample N u (k : ZMod N) = u (((k : ℝ) / N : ℝ) : Circ) := by
  simp only [sample, sampleTime, ZMod.val_natCast_of_lt hk]

theorem sample_natCast_succ {n N : ℕ} [NeZero N] (u : ContinuousLoopModel.space n)
    {k : ℕ} (hk : k < N) :
    sample N u ((k : ZMod N) + 1) = u ((((k : ℝ) + 1) / N : ℝ) : Circ) := by
  have hN := Nat.pos_of_neZero N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk1 | hk1
  · have h := sample_natCast u hk1
    push_cast at h
    exact h
  · have hz : (k : ZMod N) + 1 = (0 : ZMod N) := by
      rw [show (k : ZMod N) + 1 = ((k + 1 : ℕ) : ZMod N) by push_cast; rfl,
        show k + 1 = N from hk1, ZMod.natCast_self]
    rw [hz, ← Nat.cast_zero, sample_natCast u hN]
    have h1 : ((k : ℝ) + 1) / N = 1 := by
      rw [show ((k : ℝ) + 1) = N by exact_mod_cast hk1, div_self hNR.ne']
    rw [h1]
    simp only [Nat.cast_zero, zero_div, AddCircle.coe_zero]
    rw [AddCircle.coe_period]

theorem exists_spacing {n : ℕ} (K : Compacts (ContinuousLoopModel.space n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ u : K, ∀ s t : ClosedInterval,
      |(t : ℝ) - s| ≤ 1 / N → dist (u.val ((s : ℝ) : Circ)) (u.val ((t : ℝ) : Circ)) < ε := by
  have hc : Continuous (fun z : K × ClosedInterval => z.1.val ((z.2 : ℝ) : Circ)) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' 1).comp (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨δ, hδ, hu⟩ := (Metric.uniformContinuous_iff (α := K × ClosedInterval) (β := Sphere n)).mp
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  refine ⟨M + 1, by omega, fun N hN u s t hst => ?_⟩
  have hNp : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hbig : 1 / δ < (N : ℝ) := hM.trans_le (by exact_mod_cast (show M ≤ N by omega))
  have hstep : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hδ] at hbig
    rw [div_lt_iff₀ hNR]
    nlinarith
  have hd : dist ((u, s) : K × ClosedInterval) (u, t) < δ := by
    change max (dist u u) (dist s t) < δ
    rw [dist_self, max_eq_right dist_nonneg]
    change |(s : ℝ) - t| < δ
    rw [abs_sub_comm]
    exact hst.trans_lt hstep
  exact hu (a := (u, s)) (b := (u, t)) hd

theorem exists_short_samples {n : ℕ} (K : Compacts (ContinuousLoopModel.space n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N], ∀ u : K,
      ShortPolygon δ (sample N u.val) := by
  obtain ⟨N₀, hN₀, hs⟩ := exists_spacing K hδ
  refine ⟨N₀, hN₀, fun N hN _ u i => ?_⟩
  have hNp := Nat.pos_of_neZero N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hi : i.val < N := ZMod.val_lt i
  let s := sampleTime N i
  let t : ClosedInterval := ⟨((i.val : ℝ) + 1) / N, by
    constructor
    · positivity
    · rw [div_le_one hNR]; exact_mod_cast hi⟩
  have hst : |(t : ℝ) - s| ≤ 1 / N := by
    change |((i.val : ℝ) + 1) / N - (i.val : ℝ) / N| ≤ 1 / N
    rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
  have h := hs N hN u s t hst
  have hnext : sample N u.val (i + 1) = u.val ((t : ℝ) : Circ) := by
    have he := sample_natCast_succ u.val hi
    rw [ZMod.natCast_zmod_val] at he
    exact he
  change ‖(sample N u.val (i + 1) : Ambient n) - (sample N u.val i : Ambient n)‖ < δ
  rw [hnext]
  change ‖(u.val ((t : ℝ) : Circ) : Ambient n) - (u.val ((s : ℝ) : Circ) : Ambient n)‖ < δ
  simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using h

end
end Finsler.CompactContinuousLoopSampling
