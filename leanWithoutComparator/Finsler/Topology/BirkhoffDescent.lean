module

public import Finsler.Topology.BirkhoffStrict

/-! Descent of the curve shortening map on intervals without critical levels. A shortening of a
sublevel restricts to smaller sublevels. For a polygon model with enough vertices, polygons of
bounded energy have uniformly short edges, so the polygons whose broken geodesic has energy in
a closed interval below the level of the model form a compact set. On it the energy drop of the
staggered straightening is continuous and nonnegative, and it is positive when no tangent
critical loop has energy in the interval (strictness). Hence the drop has a positive lower
bound, every step of the curve shortening map either goes below the interval or lowers the
energy by that bound, and some iterate takes the upper sublevel into the lower one. This is the
descent property of the shortening inputs for intervals on which there are no tangent critical
loops. -/

@[expose] public section

namespace Finsler.BirkhoffDescent

open Set Filter Topology
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevCurveVariation Finsler.PolygonCritical
open Finsler.PolygonSampling Finsler.PolygonLoop Finsler.PolygonModel
open Finsler.SphereDistance (minEnergy minEnergy_nonneg exists_minEnergy_lower
  pathsBetween_nonempty)

noncomputable section

variable {n : ℕ}

section Restrict

variable {F : ReversibleMetric n} {b b₁ : ℝ} (S : Shortening.Data F b₁) (hb : b ≤ b₁)

/-- A shortening of t_{b₁} restricts to a shortening of t_b for b ≤ b₁. -/
def restrict : Shortening.Data F b where
  D := ⟨fun x => ⟨S.D (Set.inclusion (lev_mono F hb) x),
      RegularInterval.mem_lev_of_energy_le F
        (Shortening.energy_D_le S (Set.inclusion (lev_mono F hb) x)) x.2⟩,
    (continuous_subtype_val.comp
      (S.D.continuous.comp (continuous_inclusion (lev_mono F hb)))).subtype_mk _⟩
  G :=
    { toFun := fun p => ⟨S.G (p.1, Set.inclusion (lev_mono F hb) p.2),
        RegularInterval.mem_lev_of_energy_le F
          (S.energy_le p.1 (Set.inclusion (lev_mono F hb) p.2)) p.2.2⟩
      continuous_toFun := (continuous_subtype_val.comp (S.G.continuous.comp
        (continuous_fst.prodMk
          ((continuous_inclusion (lev_mono F hb)).comp continuous_snd)))).subtype_mk _
      map_zero_left := fun x => Subtype.ext
        (congrArg (Subtype.val : lev F b₁ → Loops n)
          (S.G.apply_zero (Set.inclusion (lev_mono F hb) x)))
      map_one_left := fun x => Subtype.ext
        (congrArg (Subtype.val : lev F b₁ → Loops n)
          (S.G.apply_one (Set.inclusion (lev_mono F hb) x))) }
  energy_le := fun τ x => S.energy_le τ (Set.inclusion (lev_mono F hb) x)
  rev := fun x => S.rev (Set.inclusion (lev_mono F hb) x)

/-- The iterates of the restricted shortening are the iterates of the shortening. -/
theorem iter_restrict (k : ℕ) (x : lev F b) :
    ((Shortening.iter (restrict S hb) k x : lev F b) : Loops n) =
      (Shortening.iter S k (Set.inclusion (lev_mono F hb) x) : Loops n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((S.D (Set.inclusion (lev_mono F hb) (Shortening.iter (restrict S hb) k x)) :
      lev F b₁) : Loops n) = (S.D (Shortening.iter S k (Set.inclusion (lev_mono F hb) x)) :
      Loops n)
    exact congrArg (fun y : lev F b₁ => (S.D y : Loops n)) (Subtype.ext ih)

end Restrict

/-- For enough vertices, polygons of bounded energy have short edges. -/
theorem exists_edge_bound (F : ReversibleMetric n) (hn : 1 ≤ n) (A η : ℝ) (hη : 0 < η) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ [NeZero N], ∀ q : ZMod N → Sphere n,
      polyEnergy F N (fun i => (q i : Ambient n)) ≤ A ^ 2 →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ η := by
  obtain ⟨c, hc, hlow⟩ := exists_minEnergy_lower F
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (A ^ 2 / (c * η ^ 2))
  refine ⟨N₁, fun N hN _ q hq i => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hNge : A ^ 2 / (c * η ^ 2) < N := hN₁.trans_le (by exact_mod_cast hN)
  have hnorm : ∀ j : ZMod N, ‖(q j : Ambient n)‖ = 1 := fun j =>
    mem_sphere_zero_iff_norm.mp (q j).2
  have hterm : minEnergy F (q i : Ambient n) (q (i + 1) : Ambient n) ≤
      ∑ k ∈ Finset.range N,
        minEnergy F (q (k : ZMod N) : Ambient n) (q ((k : ZMod N) + 1) : Ambient n) := by
    have hmem : i.val ∈ Finset.range N := Finset.mem_range.mpr (ZMod.val_lt i)
    have h := Finset.single_le_sum (f := fun k : ℕ =>
      minEnergy F (q (k : ZMod N) : Ambient n) (q ((k : ZMod N) + 1) : Ambient n))
      (fun k _ => minEnergy_nonneg F _ _) hmem
    simp only [ZMod.natCast_zmod_val] at h
    exact h
  have hsum : ∑ k ∈ Finset.range N,
      minEnergy F (q (k : ZMod N) : Ambient n) (q ((k : ZMod N) + 1) : Ambient n) ≤
        A ^ 2 / N := by
    rw [le_div_iff₀ hNpos, mul_comm]
    exact hq
  have hlow' := hlow (q i : Ambient n) (q (i + 1) : Ambient n)
    (pathsBetween_nonempty hn (hnorm i) (hnorm (i + 1)))
  have hsq : ‖(q (i + 1) : Ambient n) - q i‖ ^ 2 ≤ η ^ 2 := by
    have h1 : c * ‖(q (i + 1) : Ambient n) - q i‖ ^ 2 ≤ A ^ 2 / N :=
      hlow'.trans (hterm.trans hsum)
    have hcη : 0 < c * η ^ 2 := by positivity
    have h2 : A ^ 2 / N ≤ c * η ^ 2 := by
      rw [div_le_iff₀ hNpos]
      have := (div_lt_iff₀ hcη).mp hNge
      linarith
    have h3 : c * ‖(q (i + 1) : Ambient n) - q i‖ ^ 2 ≤ c * η ^ 2 := h1.trans h2
    exact le_of_mul_le_mul_left h3 hc
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hη.le two_ne_zero).mp hsq

section Core

variable {F : ReversibleMetric n} {b : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F b N)

/-- The energy drop of the staggered straightening at a broken geodesic. -/
def drop (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) : ℝ :=
  energy F (broken M q) - energy F (Birkhoff.stag M 1 (broken M q))

/-- The polygons whose broken geodesic has energy in [lo, hi]. -/
def band (lo hi : ℝ) : Set {q : ZMod N → Sphere n // ShortPolygon M.δ q} :=
  {q | lo ≤ energy F (broken M q) ∧ energy F (broken M q) ≤ hi}

theorem band_isCompact (lo hi : ℝ)
    (hedge : ∀ q : ZMod N → Sphere n, polyEnergy F N (fun i => (q i : Ambient n)) ≤ hi →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2) :
    IsCompact (band M lo hi) := by
  have hCclosed : IsClosed (⋂ i : ZMod N,
      {q : ZMod N → Sphere n | ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2}) := by
    refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
    exact ((continuous_subtype_val.comp (continuous_apply (i + 1))).sub
      (continuous_subtype_val.comp (continuous_apply i))).norm
  have hCrange : (⋂ i : ZMod N,
      {q : ZMod N → Sphere n | ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2}) ⊆
      range (Subtype.val :
        {q : ZMod N → Sphere n // ShortPolygon M.δ q} → ZMod N → Sphere n) := by
    intro q hq
    exact ⟨⟨q, fun i => lt_of_le_of_lt (mem_iInter.mp hq i) (by linarith [M.pos])⟩, rfl⟩
  have hpre := (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hCrange).mpr
    hCclosed.isCompact
  have hclosed : IsClosed (band M lo hi) :=
    isClosed_Icc.preimage
      ((Finsler.SobolevEnergy.energy_continuous F).comp (broken_continuous M))
  refine hpre.of_isClosed_subset hclosed fun q hq => mem_iInter.mpr ?_
  apply hedge q.1
  rw [← energy_broken M q]
  exact hq.2

theorem drop_continuousOn (lo : ℝ) {hi : ℝ} (hhi : hi < b ^ 2) :
    ContinuousOn (drop M) (band M lo hi) := by
  have h0 : Continuous fun q : {q : ZMod N → Sphere n // ShortPolygon M.δ q} =>
      energy F (broken M q) :=
    (Finsler.SobolevEnergy.energy_continuous F).comp (broken_continuous M)
  have hf : Continuous fun q : {q : ZMod N → Sphere n // ShortPolygon M.δ q} =>
      ((1 : ℝ), broken M q) := continuous_const.prodMk (broken_continuous M)
  have hmaps : MapsTo (fun q : {q : ZMod N → Sphere n // ShortPolygon M.δ q} =>
      ((1 : ℝ), broken M q)) (band M lo hi)
      (Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < b ^ 2}) :=
    fun q hq => ⟨⟨zero_le_one, le_rfl⟩, lt_of_le_of_lt hq.2 hhi⟩
  have h1 := (Birkhoff.stag_continuousOn M).comp hf.continuousOn hmaps
  have h2 := (Finsler.SobolevEnergy.energy_continuous F).comp_continuousOn h1
  have h3 := h0.continuousOn.sub h2
  exact h3

theorem drop_pos (hn : 1 ≤ n) {lo hi : ℝ} (hhi : hi < b ^ 2)
    (hreg : ∀ u : SphereLoop n, TangentCritical F u → lo ≤ energy F u → energy F u ≤ hi → False)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hq : q ∈ band M lo hi) :
    0 < drop M q := by
  have hlt : energy F (broken M q) < b ^ 2 := lt_of_le_of_lt hq.2 hhi
  have hle : energy F (Birkhoff.stag M 1 (broken M q)) ≤ energy F (broken M q) :=
    Birkhoff.energy_stag_le M ⟨zero_le_one, le_rfl⟩ hlt
  by_contra hnot
  have heq : energy F (Birkhoff.stag M 1 (broken M q)) = energy F (broken M q) := by
    unfold drop at hnot
    linarith
  exact hreg _ (BirkhoffStrict.tangentCritical_of_stag_energy_eq M hn q hlt heq) hq.1 hq.2

theorem exists_drop_lower (hn : 1 ≤ n) {lo hi : ℝ} (hhi : hi < b ^ 2)
    (hedge : ∀ q : ZMod N → Sphere n, polyEnergy F N (fun i => (q i : Ambient n)) ≤ hi →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2)
    (hreg : ∀ u : SphereLoop n, TangentCritical F u → lo ≤ energy F u → energy F u ≤ hi → False) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ band M lo hi, ε ≤ drop M q := by
  by_cases hne : (band M lo hi).Nonempty
  · obtain ⟨q₀, hq₀, hmin⟩ := (band_isCompact M lo hi hedge).exists_isMinOn hne
      (drop_continuousOn M lo hhi)
    exact ⟨drop M q₀, drop_pos M hn hhi hreg q₀ hq₀, fun q hq => hmin hq⟩
  · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hne⟩

/-- One step of the curve shortening map on a loop of energy at most hi: the energy goes below
lo or drops by ε. -/
theorem step {lo hi ε : ℝ} (hε : ∀ q ∈ band M lo hi, ε ≤ drop M q) {u : SphereLoop n}
    (hu : energy F u < b ^ 2) (hu' : energy F u ≤ hi) :
    energy F (Birkhoff.stag M 1 (deform M (1, u))) < lo ∨
      energy F (Birkhoff.stag M 1 (deform M (1, u))) ≤ energy F u - ε := by
  have h1 : deform M (1, u) = broken M ⟨samplePoly N u, sample_short M hu⟩ := deform_one M hu
  have he : energy F (broken M ⟨samplePoly N u, sample_short M hu⟩) ≤ energy F u := by
    rw [← h1]
    exact energy_deform_le M (p := ((1 : ℝ), u)) ⟨⟨zero_le_one, le_rfl⟩, hu⟩
  rw [h1]
  by_cases hlo : energy F (broken M ⟨samplePoly N u, sample_short M hu⟩) < lo
  · left
    exact lt_of_le_of_lt (Birkhoff.energy_stag_le M ⟨zero_le_one, le_rfl⟩
      (lt_of_le_of_lt he hu)) hlo
  · right
    have hmem : (⟨samplePoly N u, sample_short M hu⟩ :
        {q : ZMod N → Sphere n // ShortPolygon M.δ q}) ∈ band M lo hi :=
      ⟨not_lt.mp hlo, he.trans hu'⟩
    have hd := hε _ hmem
    unfold drop at hd
    linarith

variable (hb : 0 < b)

/-- The iterates of the curve shortening map on loops of energy at most hi: after k steps the
energy is below lo or has dropped by kε. -/
theorem iter_energy {lo hi ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ q ∈ band M lo hi, ε ≤ drop M q)
    (k : ℕ) (x : lev F b) (hx : energy F (x : SphereLoop n) ≤ hi) :
    energy F (Shortening.iter (Birkhoff.shortening M hb) k x : SphereLoop n) < lo ∨
      energy F (Shortening.iter (Birkhoff.shortening M hb) k x : SphereLoop n) ≤
        energy F (x : SphereLoop n) - k * ε := by
  induction k with
  | zero =>
    right
    change energy F (x : SphereLoop n) ≤ energy F (x : SphereLoop n) - ((0 : ℕ) : ℝ) * ε
    rw [Nat.cast_zero, zero_mul, sub_zero]
  | succ k ih =>
    set y := Shortening.iter (Birkhoff.shortening M hb) k x with hy
    have hstep : (Shortening.iter (Birkhoff.shortening M hb) (k + 1) x : SphereLoop n) =
        Birkhoff.stag M 1 (deform M (1, (y : SphereLoop n))) := rfl
    rw [hstep]
    have hyb : energy F (y : SphereLoop n) < b ^ 2 := (Birkhoff.mem_lev_iff hb _).mp y.2
    rcases ih with h | h
    · left
      have hle : energy F (Birkhoff.stag M 1 (deform M (1, (y : SphereLoop n)))) ≤
          energy F (y : SphereLoop n) :=
        Shortening.energy_D_le (Birkhoff.shortening M hb) y
      exact lt_of_le_of_lt hle h
    · have hkε : 0 ≤ (k : ℝ) * ε := mul_nonneg (Nat.cast_nonneg k) hε0
      rcases step M hε hyb (by linarith) with h' | h'
      · exact Or.inl h'
      · right
        push_cast
        linarith

/-- Descent for a polygon model: if no tangent critical loop has energy in [a₀², a'²], a' < b,
and the polygons of energy at most a'² have short edges, some iterate of the curve shortening
map takes t_{a'} into t_{a₀}. -/
theorem descent_of_model (hn : 1 ≤ n) {a₀ a' : ℝ} (ha₀ : 0 < a₀) (h1 : a₀ ≤ a') (h2 : a' < b)
    (hedge : ∀ q : ZMod N → Sphere n,
      polyEnergy F N (fun i => (q i : Ambient n)) ≤ a' ^ 2 →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2)
    (hreg : ∀ u : SphereLoop n, TangentCritical F u → a₀ ^ 2 ≤ energy F u →
      energy F u ≤ a' ^ 2 → False) :
    ∃ k : ℕ, ∀ x : lev F b, (x : Loops n) ∈ lev F a' →
      (Shortening.iter (Birkhoff.shortening M hb) k x : Loops n) ∈ lev F a₀ := by
  have ha' : 0 < a' := ha₀.trans_le h1
  have hhi : a' ^ 2 < b ^ 2 := pow_lt_pow_left₀ h2 ha'.le two_ne_zero
  obtain ⟨ε, hε0, hε⟩ := exists_drop_lower M hn hhi hedge hreg
  obtain ⟨k, hk⟩ := exists_nat_gt ((a' ^ 2 - a₀ ^ 2) / ε)
  refine ⟨k, fun x hx => ?_⟩
  have hxE : energy F (x : SphereLoop n) < a' ^ 2 := (Birkhoff.mem_lev_iff ha' _).mp hx
  have hkε : a' ^ 2 - a₀ ^ 2 < k * ε := (div_lt_iff₀ hε0).mp hk
  apply (Birkhoff.mem_lev_iff ha₀ _).mpr
  rcases iter_energy M hb hε0.le hε k x hxE.le with h | h
  · exact h
  · linarith

end Core

/-- Descent: if no tangent critical loop has energy in [a₀², a'²], then for every b ≥ a' some
shortening of t_b has an iterate taking t_{a'} into t_{a₀}. -/
theorem exists_descent (F : ReversibleMetric n) (hn : 1 ≤ n) {a₀ a' b : ℝ} (ha₀ : 0 < a₀)
    (h1 : a₀ ≤ a') (h2 : a' ≤ b)
    (hreg : ∀ u : SphereLoop n, TangentCritical F u → a₀ ^ 2 ≤ energy F u →
      energy F u ≤ a' ^ 2 → False) :
    ∃ (S : Shortening.Data F b) (k : ℕ), ∀ x : lev F b, (x : Loops n) ∈ lev F a' →
      (Shortening.iter S k x : Loops n) ∈ lev F a₀ := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := b + 1) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn a' (S₀.δ / 2) (half_pos S₀.pos)
  have hb1 : 0 < b + 1 := by linarith
  have hN0 : N₀ ≤ max N₀ N₁ + 1 := (le_max_left _ _).trans (Nat.le_succ _)
  have hN1 : N₁ ≤ max N₀ N₁ + 1 := (le_max_right _ _).trans (Nat.le_succ _)
  let M : PolygonModelData F (b + 1) (max N₀ N₁ + 1) :=
    PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (max N₀ N₁ + 1) hN0 (Nat.succ_pos _) u hu s t hs ht hst
  obtain ⟨k, hk⟩ := descent_of_model M hb1 hn ha₀ h1 (by linarith : a' < b + 1)
    (fun q hq i => hN₁ (max N₀ N₁ + 1) hN1 q hq i) hreg
  refine ⟨restrict (Birkhoff.shortening M hb1) (by linarith : b ≤ b + 1), k, fun x hx => ?_⟩
  rw [iter_restrict]
  exact hk _ hx

end

end Finsler.BirkhoffDescent
