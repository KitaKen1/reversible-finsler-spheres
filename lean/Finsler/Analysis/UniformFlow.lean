module

public import TauCeti.Analysis.ODE.InitialCondition
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Uniform-time flows of vector fields that are smooth on an open set. Near a compact subset K
of the open set, the field agrees with a globally C^k compactly supported field (a smooth cutoff
equal to one on a thickening of K), which is Lipschitz and has a global C^k flow (TauCeti). Since
that field is bounded by M, the flow moves points by at most M|t|, so for |t| ≤ δ/(2M) every
trajectory from K stays where the cutoff is one and solves the original equation. -/

@[expose] public section

namespace Finsler.UniformFlow

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A field C^k on an open set agrees on a thickening of a compact subset with a globally C^k
compactly supported field. -/
theorem exists_global_extension {X : E → E} {O : Set E} (hO : IsOpen O) {k : ℕ}
    (hX : ContDiffOn ℝ k X O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ g : E → E, ∃ δ : ℝ, 0 < δ ∧ ContDiff ℝ k g ∧ HasCompactSupport g ∧
      cthickening δ K ⊆ O ∧ ∀ z ∈ cthickening δ K, g z = X z := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hO hKO
  have hts : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (by linarith) K
  obtain ⟨f, hf, _hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := k)
    (isOpen_thickening (δ := δ) (E := K)) isClosed_cthickening hts
  have htsupp : tsupport f ⊆ cthickening δ K := by
    rw [tsupport, hsupp]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨fun z => f z • X z, δ / 2, by linarith, ?_, ?_,
    (cthickening_mono (by linarith) K).trans hsub, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ O
    · exact (hf.contDiffAt).smul (hX.contDiffAt (hO.mem_nhds hz))
    · have hnot : z ∉ tsupport f := fun h => hz (hsub (htsupp h))
      have hzero : (fun z => f z • X z) =ᶠ[𝓝 z] fun _ => (0 : E) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with w hw
        simp [hw]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have hcs : HasCompactSupport f :=
      HasCompactSupport.of_support_subset_isCompact (hK.cthickening (r := δ))
        (subset_closure.trans htsupp)
    exact hcs.smul_right
  · intro z hz
    have h1 : f z = 1 := (hone z).mp hz
    simp [h1]

variable [CompleteSpace E]

/-- Uniform-time local flow: for a field C^(k+1) on an open set O and a compact K ⊆ O there are a
globally C^(k+1) map Φ and τ > 0 such that every trajectory from K solves the equation on (−τ, τ)
and stays in O. -/
theorem exists_uniform_flow {X : E → E} {O : Set E} (hO : IsOpen O) (k : ℕ)
    (hX : ContDiffOn ℝ (k + 1) X O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ Φ : E → ℝ → E, ∃ τ : ℝ, 0 < τ ∧
      ContDiff ℝ (k + 1) (fun p : E × ℝ => Φ p.1 p.2) ∧ (∀ z, Φ z 0 = z) ∧
      ∀ z ∈ K, ∀ t : ℝ, |t| < τ → Φ z t ∈ O ∧ HasDerivAt (Φ z) (X (Φ z t)) t := by
  have hX' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) X O := by exact_mod_cast hX
  obtain ⟨g, δ, hδ, hg, hcs, hδO, hgX⟩ := exists_global_extension hO hX' hK hKO
  have hg' : ContDiff ℝ (k + 1) g := by exact_mod_cast hg
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hg (by simp)
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hg.continuous
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨ODE.globalSolution g hC, δ / (2 * M'), by positivity,
    ODE.contDiff_globalSolution k g hC hg', ODE.globalSolution_zero g hC, ?_⟩
  intro z hz t ht
  have hdisp : ‖ODE.globalSolution g hC z t - z‖ ≤ M' * |t| := by
    rw [ODE.globalSolution_eq_integral g hC z t, add_sub_cancel_left]
    calc ‖∫ s in (0 : ℝ)..t, g (ODE.globalSolution g hC z s)‖ ≤ M' * |t - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun s _ => (hM _).trans (le_max_left _ _))
      _ = M' * |t| := by rw [sub_zero]
  have hle : M' * |t| ≤ δ := by
    have h1 : M' * |t| ≤ M' * (δ / (2 * M')) := mul_le_mul_of_nonneg_left ht.le hM'pos.le
    have h2 : M' * (δ / (2 * M')) = δ / 2 := by field_simp
    linarith
  have hin : ODE.globalSolution g hC z t ∈ cthickening δ K := by
    apply mem_cthickening_of_dist_le _ z δ K hz
    rw [dist_eq_norm]
    exact hdisp.trans hle
  refine ⟨hδO hin, ?_⟩
  have hd := ODE.hasDerivAt_globalSolution g hC z t
  rwa [hgX _ hin] at hd

end

end Finsler.UniformFlow
