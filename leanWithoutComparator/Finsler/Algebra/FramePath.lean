module

public import Finsler.Algebra.DefiniteFrames
public import Finsler.Algebra.MatrixPath
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Continuous negative frames along a parameter interval, and closed frames. Let B_θ be a
continuous family of symmetric bilinear functions on a real normed space, such that every B_θ
has a negative frame of b vectors and the orthogonal complement of a negative frame of b vectors
carries no negative vector (b is the index). A continuous family of frames which is negative up
to a parameter τ can be steered into the span of any frame G which is negative on [τ, τ']: it is
kept up to τ, then moved to G K (K an invertible matrix) along the segment of the projection
during a short parameter interval, and equals G K afterwards. By a Lebesgue number of the open
sets on which chosen frames are negative, every negative frame at 0 extends to a continuous
family of negative frames over any interval [0, ℓ], which can be made to end at G₁ K for a given
negative frame G₁ at ℓ.

Now let T be a continuous linear map with B_{θ+η}(T v, T w) = B_θ(v, w). A family over [0, η]
from G₀ to (T G₀) K₁ is continued by the pieces T^j H(θ − j η) K₁^j, which are joined by adding
the values and subtracting the common value at the junction; this gives a continuous family of
negative frames over [0, j η] ending at (T^j G₀) K₁^j. If T^{2r} G₀ = G₀ ρ for a matrix ρ without
real eigenvalues, the end frame over [0, 2 r η] is G₀ (ρ K₁^{2r}), and this matrix is joined to
the identity by invertible matrices; multiplying the family by the inverse path gives a
continuous family of negative frames over [0, 2 r η] with the same frame at both ends. -/

@[expose] public section

namespace Finsler.FramePath

open Matrix Set Topology Finsler.DefiniteFrames Finsler.MatrixPath

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : ℕ}

/-- A continuous family of symmetric bilinear functions of index b: every member has a negative
frame of b vectors, and the orthogonal complement of such a frame carries no negative vector. -/
structure Family (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : ℕ) : Prop where
  cont : Continuous fun p : ℝ × V × V => B p.1 p.2.1 p.2.2
  symm : ∀ θ v w, B θ v w = B θ w v
  ex : ∀ θ, ∃ G : Fin b → V, Neg (B θ) G
  idx : ∀ θ (G : Fin b → V), Neg (B θ) G → ∀ w, (∀ i, B θ (G i) w = 0) → 0 ≤ B θ w w

variable {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

theorem mulF_continuous :
    Continuous fun p : (Fin b → V) × Matrix (Fin b) (Fin b) ℝ => mulF p.1 p.2 := by
  refine continuous_pi fun j => ?_
  simp only [mulF]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_snd.matrix_elem i j).smul ((continuous_apply i).comp continuous_fst)

/-- The parameters at which a fixed frame is negative form an open set. -/
theorem isOpen_neg_const (hF : Family B b) (G : Fin b → V) : IsOpen {θ : ℝ | Neg (B θ) G} := by
  have h := isOpen_neg B hF.cont (isCompact_univ (X := PUnit.{1})) (fun _ => G) continuous_const
  have he : {θ : ℝ | ∀ y ∈ (univ : Set PUnit.{1}), Neg (B θ) G} = {θ : ℝ | Neg (B θ) G} := by
    ext θ
    exact ⟨fun h => h PUnit.unit (mem_univ _), fun h _ _ => h⟩
  rw [he] at h
  exact h

/-- Steering: a continuous family of frames which is negative on [τ₀, τ] can be changed after τ
so that it stays negative up to τ' and equals G K from τ₁ on, for a frame G which is negative on
[τ, τ']. -/
theorem exists_steer (hF : Family B b) {H : ℝ → Fin b → V} (hH : Continuous H)
    {τ₀ τ τ₁ τ' : ℝ} (hτ₀ : τ₀ ≤ τ) (hτ : τ < τ₁) (hτ' : τ₁ ≤ τ')
    (hneg : ∀ θ ∈ Icc τ₀ τ, Neg (B θ) (H θ)) {G : Fin b → V}
    (hG : ∀ θ ∈ Icc τ τ', Neg (B θ) G) :
    ∃ H' : ℝ → Fin b → V, Continuous H' ∧ (∀ θ, θ ≤ τ → H' θ = H θ) ∧
      (∀ θ ∈ Icc τ₀ τ', Neg (B θ) (H' θ)) ∧
      ∃ K : Matrix (Fin b) (Fin b) ℝ, K.det ≠ 0 ∧ ∀ θ, τ₁ ≤ θ → H' θ = mulF G K := by
  have hHτ : Neg (B τ) (H τ) := hneg τ ⟨hτ₀, le_rfl⟩
  have hGτ : Neg (B τ) G := hG τ ⟨le_rfl, hτ.le.trans hτ'⟩
  obtain ⟨K, hK, hseg⟩ := exists_projection (hF.symm τ) hGτ hHτ (hF.idx τ G hGτ)
  have hΦ : Continuous fun p : ℝ × ℝ => (1 - p.2) • H τ + p.2 • mulF G K :=
    ((continuous_const.sub continuous_snd).smul continuous_const).add
      (continuous_snd.smul continuous_const)
  have hU := isOpen_neg B hF.cont (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (fun p : ℝ × ℝ => (1 - p.2) • H τ + p.2 • mulF G K) hΦ
  have hτU : τ ∈ {θ : ℝ | ∀ s ∈ Icc (0 : ℝ) 1, Neg (B θ) ((1 - s) • H τ + s • mulF G K)} :=
    fun s hs => hseg s hs.1 hs.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU τ hτU
  set e : ℝ := min (ε / 2) (τ₁ - τ) with he
  have he0 : 0 < e := lt_min (half_pos hε) (sub_pos.mpr hτ)
  have hs : Continuous fun θ : ℝ => max 0 (min 1 ((θ - τ) / e)) := by fun_prop
  refine ⟨fun θ => (1 - max 0 (min 1 ((θ - τ) / e))) • H (min θ τ) +
    max 0 (min 1 ((θ - τ) / e)) • mulF G K, ?_, ?_, ?_, K, hK, ?_⟩
  · exact ((continuous_const.sub hs).smul (hH.comp (continuous_id.min continuous_const))).add
      (hs.smul continuous_const)
  · intro θ hθ
    have h1 : (θ - τ) / e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ) he0.le
    have h2 : max 0 (min 1 ((θ - τ) / e)) = 0 :=
      max_eq_left ((min_le_right _ _).trans h1)
    simp only [h2, sub_zero, one_smul, zero_smul, add_zero, min_eq_left hθ]
  · intro θ hθ
    by_cases hle : θ ≤ τ
    · have h1 : (θ - τ) / e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) he0.le
      have h2 : max 0 (min 1 ((θ - τ) / e)) = 0 :=
        max_eq_left ((min_le_right _ _).trans h1)
      simp only [h2, sub_zero, one_smul, zero_smul, add_zero, min_eq_left hle]
      exact hneg θ ⟨hθ.1, hle⟩
    · have hge : τ ≤ θ := (not_le.mp hle).le
      simp only [min_eq_right hge]
      by_cases hlt : θ < τ + e
      · have hmem : θ ∈ Metric.ball τ ε := by
          rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hge)]
          have : e ≤ ε / 2 := min_le_left _ _
          linarith
        exact hball hmem _ ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
      · have h1 : 1 ≤ (θ - τ) / e := by
          rw [le_div_iff₀ he0]
          linarith [not_lt.mp hlt]
        have h2 : max 0 (min 1 ((θ - τ) / e)) = 1 := by
          rw [min_eq_left h1]
          exact max_eq_right zero_le_one
        simp only [h2, sub_self, zero_smul, one_smul, zero_add]
        exact neg_mulF (hG θ ⟨hge, hθ.2⟩) hK
  · intro θ hθ
    have h0 : e ≤ τ₁ - τ := min_le_right _ _
    have h1 : 1 ≤ (θ - τ) / e := by
      rw [le_div_iff₀ he0]
      linarith
    have h2 : max 0 (min 1 ((θ - τ) / e)) = 1 := by
      rw [min_eq_left h1]
      exact max_eq_right zero_le_one
    simp only [h2, sub_self, zero_smul, one_smul, zero_add]

/-- A negative frame at 0 extends to a continuous family of negative frames over [0, ℓ]. -/
theorem exists_path (hF : Family B b) {G₀ : Fin b → V} (hG₀ : Neg (B 0) G₀) (ℓ : ℝ) :
    ∃ H : ℝ → Fin b → V, Continuous H ∧ H 0 = G₀ ∧ ∀ θ ∈ Icc 0 ℓ, Neg (B θ) (H θ) := by
  choose Gf hGf using hF.ex
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ)) (b := ℓ))
    (fun θ => isOpen_neg_const hF (Gf θ)) (fun x _ => mem_iUnion.mpr ⟨x, hGf x⟩)
  have hstep : ∀ k : ℕ, ∃ H : ℝ → Fin b → V, Continuous H ∧ H 0 = G₀ ∧
      ∀ θ ∈ Icc 0 (min ℓ (k * (δ / 2))), Neg (B θ) (H θ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => G₀, continuous_const, rfl, fun θ hθ => ?_⟩
      have h1 : θ ≤ 0 := hθ.2.trans ((min_le_right _ _).trans (by simp))
      have h2 : θ = 0 := le_antisymm h1 hθ.1
      rw [h2]
      exact hG₀
    | succ k ih =>
      obtain ⟨H, hH, hH0, hneg⟩ := ih
      by_cases hℓ : ℓ < 0
      · exact ⟨H, hH, hH0, fun θ hθ => absurd (hθ.1.trans (hθ.2.trans (min_le_left _ _)))
          (not_le.mpr hℓ)⟩
      have hℓ0 : 0 ≤ ℓ := not_lt.mp hℓ
      set τ : ℝ := min ℓ (k * (δ / 2)) with hτ
      have hτ0 : 0 ≤ τ := le_min hℓ0 (by positivity)
      obtain ⟨i, hi⟩ := hleb τ ⟨hτ0, min_le_left _ _⟩
      have hG : ∀ θ ∈ Icc τ (τ + δ / 2), Neg (B θ) (Gf i) := by
        intro θ hθ
        apply hi
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hθ.1)]
        linarith [hθ.2]
      obtain ⟨H', hH', heq, hneg', -⟩ := exists_steer hF hH hτ0 (by linarith : τ < τ + δ / 2)
        le_rfl hneg hG
      refine ⟨H', hH', ?_, fun θ hθ => hneg' θ ⟨hθ.1, hθ.2.trans ?_⟩⟩
      · rw [heq 0 hτ0, hH0]
      · have h1 : ((k + 1 : ℕ) : ℝ) * (δ / 2) = k * (δ / 2) + δ / 2 := by push_cast; ring
        rw [h1]
        rcases le_total ℓ (k * (δ / 2)) with h | h
        · rw [hτ, min_eq_left h]
          exact (min_le_left _ _).trans (by linarith)
        · rw [hτ, min_eq_right h]
          exact min_le_right _ _
  obtain ⟨k, hk⟩ := exists_nat_ge (ℓ / (δ / 2))
  obtain ⟨H, hH, hH0, hneg⟩ := hstep k
  refine ⟨H, hH, hH0, fun θ hθ => hneg θ ⟨hθ.1, hθ.2.trans (le_min le_rfl ?_)⟩⟩
  rwa [div_le_iff₀ (half_pos hδ)] at hk

/-- A negative frame at 0 extends to a continuous family of negative frames over [0, ℓ] which
ends at G₁ K, for a given negative frame G₁ at ℓ. -/
theorem exists_path_to (hF : Family B b) {G₀ : Fin b → V} (hG₀ : Neg (B 0) G₀) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {G₁ : Fin b → V} (hG₁ : Neg (B ℓ) G₁) :
    ∃ H : ℝ → Fin b → V, Continuous H ∧ H 0 = G₀ ∧ (∀ θ ∈ Icc 0 ℓ, Neg (B θ) (H θ)) ∧
      ∃ K : Matrix (Fin b) (Fin b) ℝ, K.det ≠ 0 ∧ H ℓ = mulF G₁ K := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_neg_const hF G₁) ℓ hG₁
  set τ : ℝ := max 0 (ℓ - ε / 2) with hτ
  have hτ0 : 0 ≤ τ := le_max_left _ _
  have hτℓ : τ < ℓ := max_lt hℓ (by linarith)
  obtain ⟨H, hH, hH0, hneg⟩ := exists_path hF hG₀ τ
  have hG : ∀ θ ∈ Icc τ ℓ, Neg (B θ) G₁ := by
    intro θ hθ
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hθ.2)]
    have : ℓ - ε / 2 ≤ τ := le_max_right _ _
    linarith [hθ.1]
  obtain ⟨H', hH', heq, hneg', K, hK, hend⟩ := exists_steer hF hH hτ0 hτℓ le_rfl hneg hG
  exact ⟨H', hH', by rw [heq 0 hτ0, hH0], hneg', K, hK, hend ℓ le_rfl⟩

/-! ### A symmetry of the family and closed frames -/

variable (T : V →L[ℝ] V) {η : ℝ}

theorem comb_map (G : Fin b → V) (u : Fin b → ℝ) :
    comb (fun i => T (G i)) u = T (comb G u) := by
  simp only [comb, map_sum, map_smul]

theorem map_mulF_clm (G : Fin b → V) (K : Matrix (Fin b) (Fin b) ℝ) :
    (fun j => T (mulF G K j)) = mulF (fun j => T (G j)) K := by
  funext j
  simp only [mulF, map_sum, map_smul]

/-- The symmetry maps negative frames to negative frames of the shifted parameter. -/
theorem neg_map (hT : ∀ θ v w, B (θ + η) (T v) (T w) = B θ v w) {θ : ℝ} {G : Fin b → V}
    (hG : Neg (B θ) G) : Neg (B (θ + η)) (fun i => T (G i)) := by
  intro u hu
  rw [comb_map, hT]
  exact hG u hu

theorem neg_pow (hT : ∀ θ v w, B (θ + η) (T v) (T w) = B θ v w) (j : ℕ) {θ : ℝ}
    {G : Fin b → V} (hG : Neg (B θ) G) : Neg (B (θ + j * η)) (fun i => (T ^ j) (G i)) := by
  induction j with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero]
    exact hG
  | succ j ih =>
    have h := neg_map T hT ih
    have h1 : θ + (j : ℝ) * η + η = θ + ((j + 1 : ℕ) : ℝ) * η := by push_cast; ring
    rw [h1] at h
    have h2 : (fun i => T ((T ^ j) (G i))) = fun i => (T ^ (j + 1)) (G i) := by
      funext i
      rw [pow_succ']
      rfl
    rw [h2] at h
    exact h

/-- The family of negative frames over [0, η] from G₀ to (T G₀) K₁ continues over [0, j η], ending
at (T^j G₀) K₁^j. -/
theorem exists_chain (hF : Family B b) (hη : 0 < η)
    (hT : ∀ θ v w, B (θ + η) (T v) (T w) = B θ v w) {G₀ : Fin b → V} (hG₀ : Neg (B 0) G₀) :
    ∃ K₁ : Matrix (Fin b) (Fin b) ℝ, K₁.det ≠ 0 ∧ ∀ j : ℕ, ∃ C : ℝ → Fin b → V,
      Continuous C ∧ C 0 = G₀ ∧ (∀ θ ∈ Icc 0 (((j + 1 : ℕ) : ℝ) * η), Neg (B θ) (C θ)) ∧
        C (((j + 1 : ℕ) : ℝ) * η) = mulF (fun i => (T ^ (j + 1)) (G₀ i)) (K₁ ^ (j + 1)) := by
  have hTG : Neg (B η) (fun i => T (G₀ i)) := by
    have h := neg_map T hT hG₀
    rwa [zero_add] at h
  obtain ⟨H, hH, hH0, hHneg, K₁, hK₁, hHend⟩ := exists_path_to hF hG₀ hη hTG
  refine ⟨K₁, hK₁, fun j => ?_⟩
  induction j with
  | zero =>
    refine ⟨H, hH, hH0, ?_, ?_⟩
    · simpa using hHneg
    · simpa using hHend
  | succ j ih =>
    obtain ⟨C, hC, hC0, hCneg, hCend⟩ := ih
    set t : ℝ := ((j + 1 : ℕ) : ℝ) * η with ht
    have ht0 : 0 < t := mul_pos (by positivity) hη
    have hKp : (K₁ ^ (j + 1)).det ≠ 0 := by
      rw [det_pow]
      exact pow_ne_zero _ hK₁
    -- the next piece
    have hPc : Continuous fun θ : ℝ =>
        mulF (fun i => (T ^ (j + 1)) (H (θ - t) i)) (K₁ ^ (j + 1)) := by
      have h1 : Continuous fun θ : ℝ => (fun i => (T ^ (j + 1)) (H (θ - t) i) : Fin b → V) :=
        continuous_pi fun i => (T ^ (j + 1)).continuous.comp
          ((continuous_apply i).comp (hH.comp (continuous_id.sub continuous_const)))
      exact mulF_continuous.comp (h1.prodMk continuous_const)
    have hPt : mulF (fun i => (T ^ (j + 1)) (H (t - t) i)) (K₁ ^ (j + 1)) = C t := by
      rw [sub_self, hH0, hCend]
    refine ⟨fun θ => C (min θ t) + mulF (fun i => (T ^ (j + 1)) (H (max θ t - t) i))
      (K₁ ^ (j + 1)) - mulF (fun i => (T ^ (j + 1)) (H (t - t) i)) (K₁ ^ (j + 1)), ?_, ?_, ?_, ?_⟩
    · exact ((hC.comp (continuous_id.min continuous_const)).add
        (hPc.comp (continuous_id.max continuous_const))).sub continuous_const
    · simp only [min_eq_left ht0.le, max_eq_right ht0.le, add_sub_cancel_right]
      exact hC0
    · intro θ hθ
      rcases le_total θ t with hle | hge
      · simp only [min_eq_left hle, max_eq_right hle, add_sub_cancel_right]
        exact hCneg θ ⟨hθ.1, hle⟩
      · simp only [min_eq_right hge, max_eq_left hge]
        rw [hPt, add_sub_cancel_left]
        have h1 : θ - t ∈ Icc (0 : ℝ) η := by
          refine ⟨sub_nonneg.mpr hge, ?_⟩
          have h2 : ((j + 1 + 1 : ℕ) : ℝ) * η = t + η := by rw [ht]; push_cast; ring
          have h3 := hθ.2
          rw [h2] at h3
          linarith
        have h4 := neg_pow T hT (j + 1) (hHneg _ h1)
        have h5 : θ - t + ((j + 1 : ℕ) : ℝ) * η = θ := by rw [← ht]; ring
        rw [h5] at h4
        exact neg_mulF h4 hKp
    · have h2 : ((j + 1 + 1 : ℕ) : ℝ) * η = t + η := by rw [ht]; push_cast; ring
      have hge : t ≤ t + η := by linarith
      rw [h2]
      simp only [min_eq_right hge, max_eq_left hge]
      rw [hPt, add_sub_cancel_left, add_sub_cancel_left, hHend]
      have h3 : (fun i => (T ^ (j + 1)) (mulF (fun i => T (G₀ i)) K₁ i)) =
          mulF (fun i => (T ^ (j + 1 + 1)) (G₀ i)) K₁ := by
        rw [map_mulF_clm (T ^ (j + 1))]
        rfl
      rw [h3, mulF_mul, ← pow_succ']

/-- Closed frames: if T^{2r} G₀ = G₀ ρ for a matrix ρ without real eigenvalues, there is a
continuous family of negative frames over [0, 2 r η] with the same frame at both ends. -/
theorem exists_closed_frame (hF : Family B b) (hη : 0 < η)
    (hT : ∀ θ v w, B (θ + η) (T v) (T w) = B θ v w) {G₀ : Fin b → V} (hG₀ : Neg (B 0) G₀)
    {r : ℕ} (hr : 0 < r) {ρ : Matrix (Fin b) (Fin b) ℝ}
    (hρ : (fun i => (T ^ (2 * r)) (G₀ i)) = mulF G₀ ρ)
    (hρ' : ∀ (μ : ℝ) (v : Fin b → ℝ), ρ.mulVec v = μ • v → v = 0) :
    ∃ H : ℝ → Fin b → V, Continuous H ∧ H (((2 * r : ℕ) : ℝ) * η) = H 0 ∧
      ∀ θ ∈ Icc 0 (((2 * r : ℕ) : ℝ) * η), Neg (B θ) (H θ) := by
  obtain ⟨K₁, hK₁, hchain⟩ := exists_chain T hF hη hT hG₀
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j + 1 = 2 * r := ⟨2 * r - 1, by omega⟩
  obtain ⟨C, hC, hC0, hCneg, hCend⟩ := hchain j
  rw [hj] at hCneg hCend
  rw [hρ, mulF_mul] at hCend
  obtain ⟨γ, hγ, hγ0, hγ1, hγd⟩ := conn_mul_pow_even hρ' hK₁ r
  set X : Matrix (Fin b) (Fin b) ℝ := ρ * K₁ ^ (2 * r) with hX
  have hXdet : X.det ≠ 0 := by
    have h := hγd 0
    rwa [hγ0] at h
  have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hXdet
  set L : ℝ := ((2 * r : ℕ) : ℝ) * η with hL
  have hL0 : 0 < L := mul_pos (by positivity) hη
  have hΛ : Continuous fun θ : ℝ => X⁻¹ * γ (θ / L) :=
    continuous_const.matrix_mul (hγ.comp (continuous_id.div_const L))
  have hdet : ∀ θ : ℝ, (X⁻¹ * γ (θ / L)).det ≠ 0 := by
    intro θ
    rw [det_mul]
    refine mul_ne_zero ?_ (hγd _)
    intro h0
    have h1 : (X⁻¹ * X).det = 1 := by rw [Matrix.nonsing_inv_mul X hXu, det_one]
    rw [det_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨fun θ => mulF (C θ) (X⁻¹ * γ (θ / L)), ?_, ?_, ?_⟩
  · exact mulF_continuous.comp (hC.prodMk hΛ)
  · change mulF (C L) (X⁻¹ * γ (L / L)) = mulF (C 0) (X⁻¹ * γ (0 / L))
    rw [div_self hL0.ne', zero_div, hγ0, hγ1, hC0, hCend, mulF_mul, Matrix.mul_one,
      Matrix.mul_nonsing_inv X hXu, Matrix.nonsing_inv_mul X hXu]
  · intro θ hθ
    exact neg_mulF (hCneg θ hθ) (hdet θ)

end

end Finsler.FramePath
