module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Order.IntermediateValue

/-! Uniqueness for an autonomous ODE on a closed interval when the vector field is only known
to be C¹ along one of the solutions. Near each point where the two solutions agree the field
is Lipschitz on a ball containing both, so they agree on a right neighbourhood; the continuous
induction principle on [a, b] propagates the agreement. -/

@[expose] public section

namespace Finsler.OdeUnique

open Set Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem isClosed_eq_inter {f g : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) : IsClosed ({t | f t = g t} ∩ Icc a b) := by
  have h := (hf.sub hg).preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_singleton (x := (0 : E)))
  have he : {t | f t = g t} ∩ Icc a b = Icc a b ∩ (fun t => f t - g t) ⁻¹' {0} := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, sub_eq_zero]
    exact and_comm
  rw [he]
  exact h

/-- Uniqueness for an autonomous ODE whose vector field is C¹ along the first solution. -/
theorem eqOn_of_contDiffAt {v : E → E} {f g : ℝ → E} {a b : ℝ}
    (hv : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 v (f t))
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (v (f t)) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (v (g t)) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have key : Icc a b ⊆ {t | f t = g t} := by
    apply (isClosed_eq_inter hfc hgc).Icc_subset_of_forall_mem_nhdsWithin ha
    rintro x ⟨hx, hxI⟩
    have hxI' : x ∈ Icc a b := Ico_subset_Icc_self hxI
    obtain ⟨K, U, hU, hK⟩ := (hv x hxI').exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    have hfx : ∀ᶠ t in 𝓝 x, f t ∈ ball (f x) δ :=
      (hf x hxI').continuousAt.preimage_mem_nhds (ball_mem_nhds _ hδ)
    have hgx : ∀ᶠ t in 𝓝 x, g t ∈ ball (f x) δ := by
      have h := (hg x hxI').continuousAt.preimage_mem_nhds (ball_mem_nhds (g x) hδ)
      simp only [mem_ofPred_eq] at hx
      rw [← hx] at h
      exact h
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff_ball.mp (hfx.and hgx)
    set c := min (x + ε / 2) b with hc
    have hxc : x < c := lt_min (by linarith) hxI.2
    have hcb : c ≤ b := min_le_right _ _
    have hsub : Icc x c ⊆ Icc a b := Icc_subset_Icc hxI.1 hcb
    have hnear : ∀ t ∈ Icc x c, t ∈ ball x ε := by
      intro t ht
      rw [Real.ball_eq_Ioo]
      constructor
      · linarith [ht.1]
      · have := ht.2.trans (min_le_left _ _)
        linarith
    have heq : EqOn f g (Icc x c) := by
      apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => v)
        (s := fun _ => ball (f x) δ) (K := K)
      · intro t _
        exact hK.mono hball
      · exact hfc.mono hsub
      · intro t ht
        exact (hf t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt
      · intro t ht
        exact (hεsub t (hnear t (Ico_subset_Icc_self ht))).1
      · exact hgc.mono hsub
      · intro t ht
        exact (hg t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt
      · intro t ht
        exact (hεsub t (hnear t (Ico_subset_Icc_self ht))).2
      · exact hx
    filter_upwards [Ioo_mem_nhdsGT hxc] with t ht
    exact heq ⟨ht.1.le, ht.2.le⟩
  exact fun t ht => key ht

end Finsler.OdeUnique
