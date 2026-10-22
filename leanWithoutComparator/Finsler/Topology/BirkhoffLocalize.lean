module

public import Finsler.Topology.BirkhoffDescent

/-! Localization of the curve shortening map near a critical level. Loops of bounded energy are
uniformly Hölder, so a loop whose samples at spacing 1/N all stay farther than R/√N from a point
avoids the point. For a polygon model, the polygons whose broken geodesic has energy c² and is
not shortened by the staggered straightening are tangent critical; if every tangent critical
loop of positive energy stays at distance at least ρ from a point p, their vertices are far
from p, and by compactness so are the vertices of all polygons whose energy is close to c² and
whose energy drop is small. Hence, for tight cuts a' < c < b, the loops x of t_b such that the
curve shortening map D satisfies √E(D x) > a' avoid p (with enough vertices in the model). This
is the localization property of the shortening inputs, for a point at positive distance from
all closed geodesics. -/

@[expose] public section

namespace Finsler.BirkhoffLocalize

open Set Filter Topology
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevCurveVariation Finsler.PolygonCritical
open Finsler.PolygonSampling Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonBasics
open Finsler.BirkhoffDescent

noncomputable section

variable {n : ℕ}

/-- Loops of energy below A² are uniformly Hölder with exponent 1/2. -/
theorem exists_holder (F : ReversibleMetric n) {A : ℝ} (hA : 0 < A) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : SphereLoop n, energy F u < A ^ 2 →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        ‖continuousRepresentative (u.data : Space n) t -
          continuousRepresentative (u.data : Space n) s‖ ≤ Real.sqrt |t - s| * R := by
  obtain ⟨c, hc, hv⟩ := exists_velocity_sq_le F
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨A / Real.sqrt c, div_pos hA hsc, fun u hu s t hs ht => ?_⟩
  have h1 := representative_sub_le_sqrt (u.data : Space n) hs ht
  have hvel : ‖velocity (u.data : Space n)‖ ≤ A / Real.sqrt c := by
    have h2 : c * ‖velocity (u.data : Space n)‖ ^ 2 < A ^ 2 := (hv u).trans_lt hu
    rw [le_div_iff₀ hsc]
    have h3 : (‖velocity (u.data : Space n)‖ * Real.sqrt c) ^ 2 ≤ A ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le, mul_comm]
      exact h2.le
    exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) hsc.le) hA.le two_ne_zero).mp h3
  exact h1.trans (mul_le_mul_of_nonneg_left hvel (Real.sqrt_nonneg _))

/-- Every time of the unit interval is within 1/N of a sample time k/N with k < N. -/
theorem exists_near_sample {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < N ∧ |t - (k : ℝ) / N| ≤ 1 / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = min ⌊t * N⌋₊ (N - 1) := ⟨_, rfl⟩
  have hkN : k < N := by
    rw [hkdef]
    exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN one_pos)
  have hk1 : (k : ℝ) ≤ t * N := by
    have h1 : (k : ℝ) ≤ (⌊t * N⌋₊ : ℝ) := by
      rw [hkdef]
      exact_mod_cast min_le_left _ _
    exact h1.trans (Nat.floor_le (mul_nonneg ht.1 hNR.le))
  have hk2 : t * N ≤ (k : ℝ) + 1 := by
    rcases le_total ⌊t * N⌋₊ (N - 1) with h | h
    · rw [hkdef, min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [hkdef, min_eq_right h]
      have h1 : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        rw [Nat.cast_sub (Nat.succ_le_of_lt hN), Nat.cast_one]
        ring
      rw [h1]
      calc t * N ≤ 1 * N := mul_le_mul_of_nonneg_right ht.2 hNR.le
        _ = N := one_mul _
  refine ⟨k, hkN, ?_⟩
  have h3 : (k : ℝ) / N ≤ t := by
    rw [div_le_iff₀ hNR]
    exact hk1
  have h4 : t ≤ (k : ℝ) / N + 1 / N := by
    rw [← add_div, le_div_iff₀ hNR]
    exact hk2
  rw [abs_le]
  constructor
  · have h1N : (0 : ℝ) ≤ 1 / N := by positivity
    linarith
  · linarith

/-- A loop which moves at most r over parameter distance 1/N and whose samples at spacing 1/N
are farther than r from a point avoids the point. -/
theorem mem_avoid_of_vertices {N : ℕ} [NeZero N] (p : Sphere n) (u : SphereLoop n) {r : ℝ}
    (hclose : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ ≤ r)
    (hfar : ∀ i : ZMod N, r < ‖sampleN N u i - (p : Ambient n)‖) :
    u ∈ AvoidPoint.avoid p := by
  intro t heq
  have hN := Nat.pos_of_neZero N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨k, hk, hkt⟩ := exists_near_sample hN t.2
  have hs : ((k : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNR]
    exact_mod_cast hk.le
  have h1 := hclose ((k : ℝ) / N) (t : ℝ) hs t.2 hkt
  have h2 := hfar (k : ZMod N)
  rw [sampleN_natCast u hk] at h2
  have hp : continuousRepresentative (u.data : Space n) (t : ℝ) = (p : Ambient n) :=
    congrArg Subtype.val heq
  have h3 : ‖(p : Ambient n) - continuousRepresentative (u.data : Space n) ((k : ℝ) / N)‖ ≤ r :=
    hp ▸ h1
  rw [norm_sub_rev] at h3
  linarith

section Core

variable {F : ReversibleMetric n} {B : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F B N)

/-- The polygons all of whose vertices are farther than r from p. -/
def far (p : Sphere n) (r : ℝ) : Set {q : ZMod N → Sphere n // ShortPolygon M.δ q} :=
  ⋂ i : ZMod N, {q | r < ‖(q.1 i : Ambient n) - (p : Ambient n)‖}

theorem far_isOpen (p : Sphere n) (r : ℝ) : IsOpen (far M p r) := by
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  exact ((continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_subtype_val)).sub continuous_const).norm

/-- The distance of a polygon from being a non-shortened broken geodesic of energy c². -/
def gap (c : ℝ) (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) : ℝ :=
  |energy F (broken M q) - c ^ 2| + drop M q

theorem gap_continuousOn (c lo : ℝ) {hi : ℝ} (hhi : hi < B ^ 2) :
    ContinuousOn (gap M c) (band M lo hi) := by
  have h0 : Continuous fun q : {q : ZMod N → Sphere n // ShortPolygon M.δ q} =>
      |energy F (broken M q) - c ^ 2| :=
    (((Finsler.SobolevEnergy.energy_continuous F).comp (broken_continuous M)).sub
      continuous_const).abs
  have h1 := h0.continuousOn.add (drop_continuousOn M lo hhi)
  exact h1

theorem drop_nonneg {lo hi : ℝ} (hhi : hi < B ^ 2)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hq : q ∈ band M lo hi) :
    0 ≤ drop M q := by
  have hle : energy F (Birkhoff.stag M 1 (broken M q)) ≤ energy F (broken M q) :=
    Birkhoff.energy_stag_le M ⟨zero_le_one, le_rfl⟩ (lt_of_le_of_lt hq.2 hhi)
  unfold drop
  linarith

/-- A polygon of the band which is not far from p has positive gap, if all tangent critical
loops of positive energy stay at distance at least ρ from p. -/
theorem gap_pos (hn : 1 ≤ n) (p : Sphere n) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u → ∀ t : ClosedInterval,
      ρ ≤ ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖)
    {c : ℝ} (hc : 0 < c) {lo hi : ℝ} (hhi : hi < B ^ 2)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hq : q ∈ band M lo hi)
    (hnot : q ∉ far M p (ρ / 2)) : 0 < gap M c q := by
  have hd := drop_nonneg M hhi q hq
  have habs := abs_nonneg (energy F (broken M q) - c ^ 2)
  by_contra hle
  have hgap : gap M c q = 0 := le_antisymm (not_lt.mp hle) (add_nonneg habs hd)
  unfold gap at hgap
  have hd0 : drop M q = 0 := by linarith
  have ha0 : |energy F (broken M q) - c ^ 2| = 0 := by linarith
  have hE : energy F (broken M q) = c ^ 2 := by
    have := abs_eq_zero.mp ha0
    linarith
  have hlt : energy F (broken M q) < B ^ 2 := lt_of_le_of_lt hq.2 hhi
  have heq : energy F (Birkhoff.stag M 1 (broken M q)) = energy F (broken M q) := by
    unfold drop at hd0
    linarith
  have hcrit := BirkhoffStrict.tangentCritical_of_stag_energy_eq M hn q hlt heq
  have hpos : 0 < energy F (broken M q) := by
    rw [hE]
    positivity
  apply hnot
  refine mem_iInter.mpr fun i => ?_
  have h1 := hρ (broken M q) hcrit hpos (sampleTime N i)
  have h2 : (sphereRepresentative (broken M q) (sampleTime N i) : Ambient n) =
      (q.1 i : Ambient n) := congrArg (fun r : ZMod N → Sphere n => (r i : Ambient n))
    (sample_broken M q)
  rw [h2] at h1
  change ρ / 2 < ‖(q.1 i : Ambient n) - (p : Ambient n)‖
  linarith

/-- By compactness, the polygons of the band with small gap are far from p. -/
theorem exists_gap_lower (hn : 1 ≤ n) (p : Sphere n) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u → ∀ t : ClosedInterval,
      ρ ≤ ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖)
    {c : ℝ} (hc : 0 < c) {lo hi : ℝ} (hhi : hi < B ^ 2)
    (hedge : ∀ q : ZMod N → Sphere n, polyEnergy F N (fun i => (q i : Ambient n)) ≤ hi →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2) :
    ∃ m : ℝ, 0 < m ∧ ∀ q ∈ band M lo hi, gap M c q < m → q ∈ far M p (ρ / 2) := by
  have hK : IsCompact (band M lo hi ∩ (far M p (ρ / 2))ᶜ) :=
    (band_isCompact M lo hi hedge).inter_right (far_isOpen M p (ρ / 2)).isClosed_compl
  by_cases hne : (band M lo hi ∩ (far M p (ρ / 2))ᶜ).Nonempty
  · obtain ⟨q₀, hq₀, hmin⟩ := hK.exists_isMinOn hne
      ((gap_continuousOn M c lo hhi).mono inter_subset_left)
    refine ⟨gap M c q₀, gap_pos M hn p hρ0 hρ hc hhi q₀ hq₀.1 hq₀.2, fun q hq hlt => ?_⟩
    by_contra hnot
    exact absurd (hmin ⟨hq, hnot⟩) (not_le.mpr hlt)
  · refine ⟨1, one_pos, fun q hq _ => ?_⟩
    by_contra hnot
    exact hne ⟨q, hq, hnot⟩

/-- A loop of energy below (c + ε)² whose image under the curve shortening map has energy above
(c − ε)² has all its samples far from p, when small gap implies far. -/
theorem sample_far (p : Sphere n) {r c ε m lo hi : ℝ} (hε : 0 < ε) (hεc : ε ≤ c)
    (hm : 7 * c * ε ≤ m) (hlo : lo ≤ (c - ε) ^ 2) (hhi' : (c + ε) ^ 2 ≤ hi)
    (hfar : ∀ q ∈ band M lo hi, gap M c q < m → q ∈ far M p r) {u : SphereLoop n}
    (hu : energy F u < B ^ 2) (hu' : energy F u < (c + ε) ^ 2)
    (hD : (c - ε) ^ 2 < energy F (Birkhoff.stag M 1 (deform M (1, u)))) (i : ZMod N) :
    r < ‖sampleN N u i - (p : Ambient n)‖ := by
  have h1 : deform M (1, u) = broken M ⟨samplePoly N u, sample_short M hu⟩ := deform_one M hu
  have he : energy F (broken M ⟨samplePoly N u, sample_short M hu⟩) ≤ energy F u := by
    rw [← h1]
    exact energy_deform_le M (p := ((1 : ℝ), u)) ⟨⟨zero_le_one, le_rfl⟩, hu⟩
  rw [h1] at hD
  have hst : energy F (Birkhoff.stag M 1 (broken M ⟨samplePoly N u, sample_short M hu⟩)) ≤
      energy F (broken M ⟨samplePoly N u, sample_short M hu⟩) :=
    Birkhoff.energy_stag_le M ⟨zero_le_one, le_rfl⟩ (lt_of_le_of_lt he hu)
  have hmem : (⟨samplePoly N u, sample_short M hu⟩ :
      {q : ZMod N → Sphere n // ShortPolygon M.δ q}) ∈ band M lo hi :=
    ⟨by linarith, by linarith⟩
  have hc0 : 0 < c := lt_of_lt_of_le hε hεc
  have hcε : 0 < c * ε := mul_pos hc0 hε
  have hεsq : ε ^ 2 ≤ c * ε := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hεc hε.le
  have e1 : (c - ε) ^ 2 = c ^ 2 - 2 * (c * ε) + ε ^ 2 := by ring
  have e2 : (c + ε) ^ 2 = c ^ 2 + 2 * (c * ε) + ε ^ 2 := by ring
  rw [e1] at hD
  rw [e2] at hu'
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hgap : gap M c ⟨samplePoly N u, sample_short M hu⟩ < m := by
    unfold gap drop
    have habs : |energy F (broken M ⟨samplePoly N u, sample_short M hu⟩) - c ^ 2| <
        3 * (c * ε) := by
      rw [abs_lt]
      constructor <;> linarith
    have hm' : 7 * (c * ε) ≤ m := by
      rw [← mul_assoc]
      exact hm
    linarith
  have hq := mem_iInter.mp (hfar _ hmem hgap) i
  exact hq

end Core

/-- Localization: if every tangent critical loop of positive energy stays at distance at least
ρ > 0 from p, then for tight cuts a' < c < b around a positive level c some shortening D of t_b
is such that the loops x of t_b with √E(D x) > a' avoid p. -/
theorem exists_localize (F : ReversibleMetric n) (hn : 1 ≤ n) (p : Sphere n) {ρ : ℝ}
    (hρ0 : 0 < ρ)
    (hρ : ∀ u : SphereLoop n, TangentCritical F u → 0 < energy F u → ∀ t : ClosedInterval,
      ρ ≤ ‖(sphereRepresentative u t : Ambient n) - (p : Ambient n)‖)
    {c : ℝ} (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Shortening.Data F b, ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) →
        (x : Loops n) ∈ AvoidPoint.avoid p := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨R, hR, hhold⟩ := exists_holder F (A := c + 1) (by linarith)
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := c + 2) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn (c + 1) (S₀.δ / 2) (half_pos S₀.pos)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((2 * R / ρ) ^ 2)
  have hB : 0 < c + 2 := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hcne : c ≠ 0 := hc.ne'
  have hN0 : N₀ ≤ max (max N₀ N₁) N₂ + 1 :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (Nat.le_succ _)
  have hN1 : N₁ ≤ max (max N₀ N₁) N₂ + 1 :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (Nat.le_succ _)
  have hN2 : (N₂ : ℝ) ≤ ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right _ _).trans (Nat.le_succ _)
  let M : PolygonModelData F (c + 2) (max (max N₀ N₁) N₂ + 1) :=
    PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (max (max N₀ N₁) N₂ + 1) hN0 (Nat.succ_pos _) u hu s t hs ht hst
  have hhi : (c + 1) ^ 2 < (c + 2) ^ 2 := by nlinarith
  obtain ⟨m, hm, hfar⟩ := exists_gap_lower M hn p hρ0 hρ hc (lo := (c / 2) ^ 2) hhi
    (fun q hq i => hN₁ (max (max N₀ N₁) N₂ + 1) hN1 q hq i)
  -- the modulus of continuity at spacing 1/N is below ρ/2
  have hNpos : (0 : ℝ) < ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) := by positivity
  have hmod : ∀ d : ℝ, d ≤ 1 / ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) →
      Real.sqrt d * R ≤ ρ / 2 := by
    intro d hd
    have h1 : Real.sqrt d ≤ Real.sqrt (1 / ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt hd
    have h2 : (Real.sqrt (1 / ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ)) * R) ^ 2 ≤ (ρ / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), one_div, inv_mul_le_iff₀ hNpos]
      have h3 : (2 * R / ρ) ^ 2 < ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) := hN₂.trans_le hN2
      have h4 : (2 * R / ρ) ^ 2 * ρ ^ 2 = 4 * R ^ 2 := by
        field_simp
        ring
      have h5 : (2 * R / ρ) ^ 2 * ρ ^ 2 < ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) * ρ ^ 2 :=
        mul_lt_mul_of_pos_right h3 (pow_pos hρ0 2)
      have h6 : ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) * (ρ / 2) ^ 2 =
          ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) * ρ ^ 2 / 4 := by ring
      rw [h6]
      linarith
    have h5 := (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg _) hR.le)
      (by positivity) two_ne_zero).mp h2
    exact (mul_le_mul_of_nonneg_right h1 hR.le).trans h5
  refine ⟨min (min 1 (c / 2)) (m / (7 * c)), by positivity, ?_⟩
  intro a' b ha1 ha2 hb1 hb2
  have hε0 : 0 < min (min 1 (c / 2)) (m / (7 * c)) := by positivity
  have hε1 : min (min 1 (c / 2)) (m / (7 * c)) ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : min (min 1 (c / 2)) (m / (7 * c)) ≤ c / 2 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : 7 * c * min (min 1 (c / 2)) (m / (7 * c)) ≤ m := by
    have h := min_le_right (min 1 (c / 2)) (m / (7 * c))
    have h7 : (0 : ℝ) < 7 * c := by positivity
    calc 7 * c * min (min 1 (c / 2)) (m / (7 * c)) ≤ 7 * c * (m / (7 * c)) :=
          mul_le_mul_of_nonneg_left h h7.le
      _ = m := by field_simp
  have hbB : b ≤ c + 2 := by linarith
  have ha'0 : 0 < a' := by linarith
  refine ⟨restrict (Birkhoff.shortening M hB) hbB, fun x hx => ?_⟩
  have hb0 : 0 < b := hc.trans hb1
  have hxb : energy F (x : SphereLoop n) < b ^ 2 := (Birkhoff.mem_lev_iff hb0 _).mp x.2
  have hbε : b ^ 2 < (c + min (min 1 (c / 2)) (m / (7 * c))) ^ 2 :=
    pow_lt_pow_left₀ hb2 hb0.le two_ne_zero
  have hxε : energy F (x : SphereLoop n) < (c + min (min 1 (c / 2)) (m / (7 * c))) ^ 2 :=
    hxb.trans hbε
  have hx1 : energy F (x : SphereLoop n) < (c + 1) ^ 2 := by
    have : (c + min (min 1 (c / 2)) (m / (7 * c))) ^ 2 ≤ (c + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith
  have hxB : energy F (x : SphereLoop n) < (c + 2) ^ 2 := hx1.trans hhi
  have hD : (c - min (min 1 (c / 2)) (m / (7 * c))) ^ 2 <
      energy F (Birkhoff.stag M 1 (deform M (1, (x : SphereLoop n)))) := by
    have h1 : a' ^ 2 < energy F (Birkhoff.stag M 1 (deform M (1, (x : SphereLoop n)))) :=
      (Real.lt_sqrt ha'0.le).mp hx
    have h2 : (c - min (min 1 (c / 2)) (m / (7 * c))) ^ 2 < a' ^ 2 :=
      pow_lt_pow_left₀ ha1 (by linarith) two_ne_zero
    exact h2.trans h1
  have hfarx : ∀ i : ZMod (max (max N₀ N₁) N₂ + 1),
      ρ / 2 < ‖sampleN (max (max N₀ N₁) N₂ + 1) (x : SphereLoop n) i - (p : Ambient n)‖ :=
    fun i => sample_far M p hε0 (by linarith) hε3
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (pow_le_pow_left₀ (by linarith) (by linarith) 2) hfar hxB hxε hD i
  refine mem_avoid_of_vertices p (x : SphereLoop n) (fun s t hs ht hst => ?_) hfarx
  exact (hhold (x : SphereLoop n) hx1 s t hs ht).trans (hmod _ hst)

end

end Finsler.BirkhoffLocalize
