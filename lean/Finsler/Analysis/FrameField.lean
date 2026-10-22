module

public import Finsler.Algebra.DefiniteFrames
public import Finsler.Analysis.PseudoGradient
public import Mathlib.Topology.MetricSpace.Thickening

/-! Smooth negative frame fields near a closed curve. Let Q_z be bilinear functions on a real
normed space V depending continuously on the point z of an open set 𝒪 of a finite dimensional
space, c a continuous curve with c([0, L]) ⊂ 𝒪 and H a continuous family of frames over [0, L]
such that H(θ) is negative for Q at c(θ), and such that H takes the same value at two parameters
of [0, L] with the same point of the curve (for a closed embedded curve: H(0) = H(L)). Then there
are an open set 𝒪' with c([0, L]) ⊂ 𝒪' ⊂ 𝒪 and a smooth map G from the space to the frames such
that G(z) is negative for Q_z for every z in 𝒪'.

The pairs (z, F) with z in 𝒪 and F negative for Q_z form an open set containing the compact set
of the pairs (c(θ), H(θ)), hence a uniform neighbourhood of radius ε of it. By compactness there
is r > 0 such that parameters whose points are closer than 2r have frames closer than ε/2. For
finitely many parameters whose balls of radius r/2 cover the curve, G is the sum of the frames
multiplied by bump functions of these balls: at a point of the union of the balls it is a
positive multiple of a convex combination of frames within ε/2 of one of them. -/

@[expose] public section

namespace Finsler.FrameField

open Set Metric Topology Finsler.DefiniteFrames Finsler.PseudoGradient
open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : ℕ}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The pairs of a point of an open set and a frame which is negative for the bilinear function
of the point form an open set. -/
theorem isOpen_pairs {𝒪 : Set E} (h𝒪 : IsOpen 𝒪) (Q : E → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ContinuousOn (fun p : E × V × V => Q p.1 p.2.1 p.2.2) (𝒪 ×ˢ univ)) :
    IsOpen {p : E × (Fin b → V) | p.1 ∈ 𝒪 ∧ Neg (Q p.1) p.2} := by
  have hB : Continuous fun p : (𝒪 × (Fin b → V)) × V × V => Q (p.1.1 : E) p.2.1 p.2.2 := by
    refine hQ.comp_continuous (f := fun p : (𝒪 × (Fin b → V)) × V × V =>
      (((p.1.1 : E)), p.2.1, p.2.2)) ?_ (fun p => ⟨p.1.1.2, mem_univ _⟩)
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd
  have h := isOpen_neg (fun p : 𝒪 × (Fin b → V) => Q (p.1 : E)) hB
    (isCompact_univ (X := PUnit.{1})) (fun p => p.1.2) (continuous_snd.comp continuous_fst)
  have hmap : IsOpenMap fun p : 𝒪 × (Fin b → V) => (((p.1 : E)), p.2) :=
    h𝒪.isOpenMap_subtype_val.prodMap IsOpenMap.id
  have himg := hmap _ h
  have heq : (fun p : 𝒪 × (Fin b → V) => (((p.1 : E)), p.2)) ''
      {θ : 𝒪 × (Fin b → V) | ∀ y ∈ (univ : Set PUnit.{1}), Neg (Q (θ.1 : E)) θ.2} =
      {p : E × (Fin b → V) | p.1 ∈ 𝒪 ∧ Neg (Q p.1) p.2} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.2, hq PUnit.unit (mem_univ _)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(⟨p.1, h1⟩, p.2), fun _ _ => h2, rfl⟩
  rw [heq] at himg
  exact himg

/-- A smooth frame field which is negative on a neighbourhood of a curve carrying a continuous
family of negative frames. -/
theorem exists_frame_field {𝒪 : Set E} (h𝒪 : IsOpen 𝒪) (Q : E → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hQ : ContinuousOn (fun p : E × V × V => Q p.1 p.2.1 p.2.2) (𝒪 ×ˢ univ))
    {c : ℝ → E} (hc : Continuous c) {L : ℝ} (hc𝒪 : ∀ θ ∈ Icc 0 L, c θ ∈ 𝒪)
    {H : ℝ → Fin b → V} (hH : Continuous H)
    (hcH : ∀ θ ∈ Icc 0 L, ∀ θ' ∈ Icc 0 L, c θ = c θ' → H θ = H θ')
    (hneg : ∀ θ ∈ Icc 0 L, Neg (Q (c θ)) (H θ)) :
    ∃ 𝒪' : Set E, IsOpen 𝒪' ∧ (∀ θ ∈ Icc 0 L, c θ ∈ 𝒪') ∧ 𝒪' ⊆ 𝒪 ∧
      ∃ G : E → Fin b → V, ContDiff ℝ ∞ G ∧ ∀ z ∈ 𝒪', Neg (Q z) (G z) := by
  -- a uniform neighbourhood of the pairs (c θ, H θ)
  have hKc : IsCompact ((fun θ : ℝ => (c θ, H θ)) '' Icc 0 L) :=
    isCompact_Icc.image (hc.prodMk hH)
  have hKsub : (fun θ : ℝ => (c θ, H θ)) '' Icc 0 L ⊆
      {p : E × (Fin b → V) | p.1 ∈ 𝒪 ∧ Neg (Q p.1) p.2} := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact ⟨hc𝒪 θ hθ, hneg θ hθ⟩
  obtain ⟨ε, hε, hthick⟩ := hKc.exists_thickening_subset_open (isOpen_pairs h𝒪 Q hQ) hKsub
  have hnear : ∀ θ ∈ Icc (0 : ℝ) L, ∀ (z : E) (F : Fin b → V), dist z (c θ) < ε →
      dist F (H θ) < ε → z ∈ 𝒪 ∧ Neg (Q z) F := by
    intro θ hθ z F hz hF
    change (z, F) ∈ {p : E × (Fin b → V) | p.1 ∈ 𝒪 ∧ Neg (Q p.1) p.2}
    apply hthick
    rw [mem_thickening_iff]
    exact ⟨(c θ, H θ), ⟨θ, hθ, rfl⟩, by rw [Prod.dist_eq]; exact max_lt hz hF⟩
  -- parameters with close points have close frames
  have hsep : ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ∀ θ ∈ Icc (0 : ℝ) L, ∀ θ' ∈ Icc (0 : ℝ) L,
      dist (c θ) (c θ') < 2 * r → dist (H θ) (H θ') < ε / 2 := by
    set D : Set (ℝ × ℝ) := {p | p ∈ Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L ∧ ε / 2 ≤ dist (H p.1) (H p.2)}
      with hD
    have hDc : IsCompact D := by
      refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ (fun p hp => hp.1)
      exact (isClosed_Icc.prod isClosed_Icc).inter
        (isClosed_le continuous_const ((hH.comp continuous_fst).dist (hH.comp continuous_snd)))
    by_cases hne : D.Nonempty
    · have hf : ContinuousOn (fun p : ℝ × ℝ => dist (c p.1) (c p.2)) D :=
        ((hc.comp continuous_fst).dist (hc.comp continuous_snd)).continuousOn
      obtain ⟨p₀, hp₀, hmin⟩ := hDc.exists_isMinOn hne hf
      have hpos : 0 < dist (c p₀.1) (c p₀.2) := by
        rw [dist_pos]
        intro heq
        have h1 := hcH p₀.1 hp₀.1.1 p₀.2 hp₀.1.2 heq
        have h2 := hp₀.2
        rw [h1, dist_self] at h2
        linarith
      refine ⟨min ε (dist (c p₀.1) (c p₀.2) / 2), lt_min hε (half_pos hpos), min_le_left _ _, ?_⟩
      intro θ hθ θ' hθ' hd
      by_contra hcon
      have hmem : (θ, θ') ∈ D := ⟨⟨hθ, hθ'⟩, not_lt.mp hcon⟩
      have h1 : dist (c p₀.1) (c p₀.2) ≤ dist (c θ) (c θ') := hmin hmem
      have h2 : 2 * min ε (dist (c p₀.1) (c p₀.2) / 2) ≤ dist (c p₀.1) (c p₀.2) := by
        have := min_le_right ε (dist (c p₀.1) (c p₀.2) / 2)
        linarith
      linarith
    · refine ⟨ε, hε, le_rfl, ?_⟩
      intro θ hθ θ' hθ' _
      by_contra hcon
      exact hne ⟨(θ, θ'), ⟨hθ, hθ'⟩, not_lt.mp hcon⟩
  obtain ⟨r, hr, hrε, hclose⟩ := hsep
  -- finitely many parameters whose balls cover the curve
  obtain ⟨t, ht, hcover⟩ := isCompact_Icc.elim_nhds_subcover
    (fun θ' : ℝ => c ⁻¹' ball (c θ') (r / 2))
    (fun θ' (_ : θ' ∈ Icc (0 : ℝ) L) =>
      (isOpen_ball.preimage hc).mem_nhds (mem_ball_self (half_pos hr)))
  have hbump1 : ∀ θ' : ℝ, ∀ z ∈ ball (c θ') (r / 2), bump (c θ') (r / 2) z = 1 :=
    fun θ' z hz => bump_eq_one (half_pos hr) (ball_subset_closedBall hz)
  have hbump0 : ∀ (θ' : ℝ) (z : E), bump (c θ') (r / 2) z ≠ 0 → dist z (c θ') < r := by
    intro θ' z hz
    by_contra hcon
    apply hz
    apply bump_eq_zero
    rw [mem_ball, show 2 * (r / 2) = r by ring]
    exact hcon
  refine ⟨⋃ θ' ∈ t, ball (c θ') (r / 2), isOpen_biUnion fun _ _ => isOpen_ball, ?_, ?_,
    fun z => ∑ θ' ∈ t, bump (c θ') (r / 2) z • H θ', ?_, ?_⟩
  · intro θ hθ
    obtain ⟨θ', hθ't, hθ'⟩ := mem_iUnion₂.mp (hcover hθ)
    exact mem_iUnion₂.mpr ⟨θ', hθ't, hθ'⟩
  · intro z hz
    obtain ⟨θ', hθ't, hθ'⟩ := mem_iUnion₂.mp hz
    exact (hnear θ' (ht θ' hθ't) z (H θ') (lt_of_lt_of_le (mem_ball.mp hθ') (by linarith))
      (by rw [dist_self]; exact hε)).1
  · exact ContDiff.sum fun θ' _ => (bump_contDiff (c θ') (r / 2)).smul contDiff_const
  · intro z hz
    obtain ⟨θ₀, hθ₀t, hθ₀⟩ := mem_iUnion₂.mp hz
    have hθ₀I := ht θ₀ hθ₀t
    set w : ℝ → ℝ := fun θ' => bump (c θ') (r / 2) z with hw
    have hw0 : ∀ θ', 0 ≤ w θ' := fun θ' => bump_nonneg _ _ _
    set Wt : ℝ := ∑ θ' ∈ t, w θ' with hWt
    have hW1 : 1 ≤ Wt := by
      have h1 : w θ₀ = 1 := hbump1 θ₀ z hθ₀
      rw [← h1]
      exact Finset.single_le_sum (fun θ' _ => hw0 θ') hθ₀t
    have hWpos : 0 < Wt := lt_of_lt_of_le one_pos hW1
    -- the normalized combination is close to the frame of θ₀
    have hbar : dist ((Wt⁻¹) • ∑ θ' ∈ t, w θ' • H θ') (H θ₀) < ε := by
      have hsum1 : ∑ θ' ∈ t, Wt⁻¹ * w θ' = 1 := by
        rw [← Finset.mul_sum, inv_mul_cancel₀ hWpos.ne']
      have hdiff : (Wt⁻¹) • ∑ θ' ∈ t, w θ' • H θ' - H θ₀ =
          ∑ θ' ∈ t, (Wt⁻¹ * w θ') • (H θ' - H θ₀) := by
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum1, one_smul,
          Finset.smul_sum, smul_smul]
      rw [dist_eq_norm, hdiff]
      have hterm : ∀ θ' ∈ t, ‖(Wt⁻¹ * w θ') • (H θ' - H θ₀)‖ ≤ (Wt⁻¹ * w θ') * (ε / 2) := by
        intro θ' hθ't
        have hc0 : 0 ≤ Wt⁻¹ * w θ' := mul_nonneg (inv_nonneg.mpr hWpos.le) (hw0 θ')
        rw [norm_smul, Real.norm_of_nonneg hc0]
        by_cases hz0 : w θ' = 0
        · rw [hz0, mul_zero, zero_mul, zero_mul]
        · have hd1 : dist z (c θ') < r := hbump0 θ' z hz0
          have hd2 : dist (c θ') (c θ₀) < 2 * r := by
            have h3 : dist (c θ') (c θ₀) ≤ dist (c θ') z + dist z (c θ₀) := dist_triangle _ _ _
            rw [dist_comm (c θ') z] at h3
            have h4 := mem_ball.mp hθ₀
            linarith
          have h5 := hclose θ' (ht θ' hθ't) θ₀ hθ₀I hd2
          rw [dist_eq_norm] at h5
          exact mul_le_mul_of_nonneg_left h5.le hc0
      calc ‖∑ θ' ∈ t, (Wt⁻¹ * w θ') • (H θ' - H θ₀)‖
          ≤ ∑ θ' ∈ t, ‖(Wt⁻¹ * w θ') • (H θ' - H θ₀)‖ := norm_sum_le _ _
        _ ≤ ∑ θ' ∈ t, (Wt⁻¹ * w θ') * (ε / 2) := Finset.sum_le_sum hterm
        _ = ε / 2 := by rw [← Finset.sum_mul, hsum1, one_mul]
        _ < ε := half_lt_self hε
    have hzc : dist z (c θ₀) < ε :=
      lt_of_lt_of_le (mem_ball.mp hθ₀) (by linarith)
    have hNeg := (hnear θ₀ hθ₀I z _ hzc hbar).2
    have hfin : (∑ θ' ∈ t, bump (c θ') (r / 2) z • H θ') =
        Wt • ((Wt⁻¹) • ∑ θ' ∈ t, w θ' • H θ') := by
      rw [smul_smul, mul_inv_cancel₀ hWpos.ne', one_smul]
    change Neg (Q z) (∑ θ' ∈ t, bump (c θ') (r / 2) z • H θ')
    rw [hfin]
    exact neg_smul_frame hNeg hWpos

end

end Finsler.FrameField
