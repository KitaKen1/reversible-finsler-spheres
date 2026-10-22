module

public import Finsler.Topology.BirkhoffLocalize

/-! Uniform localization of the curve shortening map near the critical set. For a polygon
model, a polygon of an energy band with zero gap (its broken geodesic has energy c² and is not
shortened by the staggered straightening) has a tangent critical broken geodesic of energy c².
By compactness, the polygons of the band with small gap lie in any open set containing those
with zero gap, in particular in the set of polygons which are close, vertex by vertex, to a
polygon with zero gap. Loops of bounded energy are uniformly Hölder, so with enough vertices a
loop whose samples are close to the vertices of such a polygon is uniformly close to its broken
geodesic. Hence, for tight cuts a' < c < b around a positive level c and ρ > 0, some shortening
D of t_b is such that every loop x of t_b with √E(D x) > a' is within ρ, uniformly in the
parameter, of a tangent critical loop of energy c². No finiteness assumption is used. -/

@[expose] public section

namespace Finsler.BirkhoffNear

open Set Filter Topology
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevCurveVariation Finsler.PolygonCritical
open Finsler.PolygonSampling Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonBasics
open Finsler.BirkhoffDescent Finsler.BirkhoffLocalize

noncomputable section

variable {n : ℕ}

/-- Triangle inequality through two intermediate points. -/
theorem norm_sub_le_three {E : Type*} [NormedAddCommGroup E] (a b c d : E) :
    ‖a - b‖ ≤ ‖a - c‖ + ‖c - d‖ + ‖b - d‖ := by
  have h : a - b = (a - c) + (c - d) - (b - d) := by abel
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

section Core

variable {F : ReversibleMetric n} {B : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F B N)

theorem gap_nonneg {lo hi : ℝ} (hhi : hi < B ^ 2) (c : ℝ)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hq : q ∈ band M lo hi) :
    0 ≤ gap M c q := by
  unfold gap
  exact add_nonneg (abs_nonneg _) (drop_nonneg M hhi q hq)

/-- A polygon of the band with zero gap: its broken geodesic is tangent critical and has
energy c². -/
theorem critical_of_gap_zero (hn : 1 ≤ n) {c lo hi : ℝ} (hhi : hi < B ^ 2)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hq : q ∈ band M lo hi)
    (hgap : gap M c q = 0) :
    TangentCritical F (broken M q) ∧ energy F (broken M q) = c ^ 2 := by
  have hd := drop_nonneg M hhi q hq
  have habs := abs_nonneg (energy F (broken M q) - c ^ 2)
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
  exact ⟨BirkhoffStrict.tangentCritical_of_stag_energy_eq M hn q hlt heq, hE⟩

/-- By compactness, the polygons of the band with small gap lie in any open set containing the
polygons of the band with zero gap. -/
theorem exists_gap_lower_of_open {c lo hi : ℝ} (hhi : hi < B ^ 2)
    (hedge : ∀ q : ZMod N → Sphere n, polyEnergy F N (fun i => (q i : Ambient n)) ≤ hi →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2)
    (W : Set {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hW : IsOpen W)
    (hzero : ∀ q ∈ band M lo hi, gap M c q = 0 → q ∈ W) :
    ∃ m : ℝ, 0 < m ∧ ∀ q ∈ band M lo hi, gap M c q < m → q ∈ W := by
  have hK : IsCompact (band M lo hi ∩ Wᶜ) :=
    (band_isCompact M lo hi hedge).inter_right hW.isClosed_compl
  by_cases hne : (band M lo hi ∩ Wᶜ).Nonempty
  · obtain ⟨q₀, hq₀, hmin⟩ := hK.exists_isMinOn hne
      ((gap_continuousOn M c lo hhi).mono inter_subset_left)
    have hpos : 0 < gap M c q₀ := by
      rcases (gap_nonneg M hhi c q₀ hq₀.1).lt_or_eq with h | h
      · exact h
      · exact absurd (hzero q₀ hq₀.1 h.symm) hq₀.2
    refine ⟨gap M c q₀, hpos, fun q hq hlt => ?_⟩
    by_contra hnot
    exact absurd (hmin ⟨hq, hnot⟩) (not_le.mpr hlt)
  · refine ⟨1, one_pos, fun q hq _ => ?_⟩
    by_contra hnot
    exact hne ⟨q, hq, hnot⟩

/-- The polygons within r, vertex by vertex, of a polygon of the band with zero gap. -/
def nearZero (c lo hi r : ℝ) : Set {q : ZMod N → Sphere n // ShortPolygon M.δ q} :=
  ⋃ q₀ : {q₀ : {q : ZMod N → Sphere n // ShortPolygon M.δ q} //
      q₀ ∈ band M lo hi ∧ gap M c q₀ = 0},
    ⋂ i : ZMod N, {q | ‖(q.1 i : Ambient n) - (q₀.1.1 i : Ambient n)‖ < r}

theorem nearZero_isOpen (c lo hi r : ℝ) : IsOpen (nearZero M c lo hi r) := by
  refine isOpen_iUnion fun q₀ => isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const
  exact ((continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_subtype_val)).sub continuous_const).norm

theorem mem_nearZero_of_gap_zero {c lo hi r : ℝ} (hr : 0 < r)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) (hq : q ∈ band M lo hi)
    (hgap : gap M c q = 0) : q ∈ nearZero M c lo hi r := by
  refine mem_iUnion.mpr ⟨⟨q, hq, hgap⟩, mem_iInter.mpr fun i => ?_⟩
  change ‖(q.1 i : Ambient n) - (q.1 i : Ambient n)‖ < r
  rw [sub_self, norm_zero]
  exact hr

/-- A loop of energy below (c + ε)² whose image under the curve shortening map has energy above
(c − ε)² has its sample polygon in every set containing the polygons of the band with small
gap. -/
theorem sample_mem {c ε m lo hi : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) (hm : 7 * c * ε ≤ m)
    (hlo : lo ≤ (c - ε) ^ 2) (hhi' : (c + ε) ^ 2 ≤ hi)
    {W : Set {q : ZMod N → Sphere n // ShortPolygon M.δ q}}
    (hW : ∀ q ∈ band M lo hi, gap M c q < m → q ∈ W) {u : SphereLoop n}
    (hu : energy F u < B ^ 2) (hu' : energy F u < (c + ε) ^ 2)
    (hD : (c - ε) ^ 2 < energy F (Birkhoff.stag M 1 (deform M (1, u)))) :
    (⟨samplePoly N u, sample_short M hu⟩ :
      {q : ZMod N → Sphere n // ShortPolygon M.δ q}) ∈ W := by
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
  exact hW _ hmem hgap

/-- The value of the broken geodesic of a polygon at a sample time is the vertex. -/
theorem broken_sample (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) {k : ℕ} (hk : k < N) :
    continuousRepresentative ((broken M q).data : Space n) ((k : ℝ) / N) =
      (q.1 (k : ZMod N) : Ambient n) :=
  (sampleN_natCast (broken M q) hk).symm.trans
    (congrArg (fun r : ZMod N → Sphere n => (r (k : ZMod N) : Ambient n)) (sample_broken M q))

/-- A loop whose samples are within ρ/3 of the vertices of a polygon is uniformly within ρ of
the broken geodesic of the polygon, when both move at most ρ/3 over parameter distance 1/N. -/
theorem near_broken {R ρ : ℝ} (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q})
    (u : SphereLoop n)
    (hu : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ ≤ Real.sqrt |t - s| * R)
    (hb : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ‖continuousRepresentative ((broken M q).data : Space n) t -
        continuousRepresentative ((broken M q).data : Space n) s‖ ≤ Real.sqrt |t - s| * R)
    (hmod : ∀ d : ℝ, d ≤ 1 / (N : ℝ) → Real.sqrt d * R ≤ ρ / 3)
    (hclose : ∀ i : ZMod N, ‖sampleN N u i - (q.1 i : Ambient n)‖ < ρ / 3) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖continuousRepresentative (u.data : Space n) t -
      continuousRepresentative ((broken M q).data : Space n) t‖ ≤ ρ := by
  have hN := Nat.pos_of_neZero N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨k, hk, hkt⟩ := exists_near_sample hN ht
  have hs : ((k : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNR]
    exact_mod_cast hk.le
  have h1 := (hu ((k : ℝ) / N) t hs ht).trans (hmod _ hkt)
  have h2 := (hb ((k : ℝ) / N) t hs ht).trans (hmod _ hkt)
  have h3 : ‖continuousRepresentative (u.data : Space n) ((k : ℝ) / N) -
      continuousRepresentative ((broken M q).data : Space n) ((k : ℝ) / N)‖ < ρ / 3 :=
    (congrArg₂ (fun a b : Ambient n => ‖a - b‖) (sampleN_natCast u hk).symm
      (broken_sample M q hk)).trans_lt (hclose (k : ZMod N))
  have h4 := norm_sub_le_three (continuousRepresentative (u.data : Space n) t)
    (continuousRepresentative ((broken M q).data : Space n) t)
    (continuousRepresentative (u.data : Space n) ((k : ℝ) / N))
    (continuousRepresentative ((broken M q).data : Space n) ((k : ℝ) / N))
  linarith

/-- Uniform localization for a model with enough vertices: a loop of energy below (c + ε)²
whose image under the curve shortening map has energy above (c − ε)² is uniformly within ρ of a
tangent critical loop of energy c². -/
theorem near_of_model {c ρ R : ℝ} (M : PolygonModelData F (c + 2) N) (hn : 1 ≤ n) (hc : 0 < c)
    (hρ0 : 0 < ρ)
    (hhold : ∀ u : SphereLoop n, energy F u < (c + 1) ^ 2 →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        ‖continuousRepresentative (u.data : Space n) t -
          continuousRepresentative (u.data : Space n) s‖ ≤ Real.sqrt |t - s| * R)
    (hmod : ∀ d : ℝ, d ≤ 1 / (N : ℝ) → Real.sqrt d * R ≤ ρ / 3)
    (hedge : ∀ q : ZMod N → Sphere n,
      polyEnergy F N (fun i => (q i : Ambient n)) ≤ (c + 1) ^ 2 →
      ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ c / 2 ∧ ∀ u : SphereLoop n, energy F u < (c + ε) ^ 2 →
      (c - ε) ^ 2 < energy F (Birkhoff.stag M 1 (deform M (1, u))) →
      ∃ γ : SphereLoop n, TangentCritical F γ ∧ energy F γ = c ^ 2 ∧
        ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
          ‖continuousRepresentative (u.data : Space n) t -
            continuousRepresentative (γ.data : Space n) t‖ ≤ ρ := by
  have hhi : (c + 1) ^ 2 < (c + 2) ^ 2 := by nlinarith
  have hcne : c ≠ 0 := hc.ne'
  obtain ⟨m, hm, hW⟩ := exists_gap_lower_of_open M (c := c) (lo := (c / 2) ^ 2) hhi hedge
    (nearZero M c ((c / 2) ^ 2) ((c + 1) ^ 2) (ρ / 3)) (nearZero_isOpen M _ _ _ _)
    (fun q hq hgap => mem_nearZero_of_gap_zero M (by positivity) q hq hgap)
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
  refine ⟨min (min 1 (c / 2)) (m / (7 * c)), hε0, hε1, hε2, fun u hu' hD => ?_⟩
  have hu1 : energy F u < (c + 1) ^ 2 := by
    have : (c + min (min 1 (c / 2)) (m / (7 * c))) ^ 2 ≤ (c + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith
  have huB : energy F u < (c + 2) ^ 2 := hu1.trans hhi
  have hmem := sample_mem M hε0 (by linarith) hε3
    (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    (pow_le_pow_left₀ (by linarith) (by linarith) 2) hW huB hu' hD
  obtain ⟨q₀, hq₀⟩ := mem_iUnion.mp hmem
  have hclose := mem_iInter.mp hq₀
  obtain ⟨hcrit, hE⟩ := critical_of_gap_zero M hn hhi q₀.1 q₀.2.1 q₀.2.2
  have hγ1 : energy F (broken M q₀.1) < (c + 1) ^ 2 := by
    rw [hE]
    nlinarith
  exact ⟨broken M q₀.1, hcrit, hE, fun t ht =>
    near_broken M q₀.1 u (hhold u hu1) (hhold (broken M q₀.1) hγ1) hmod hclose ht⟩

end Core

/-- The Hölder modulus at spacing 1/N is at most ρ/3 when N exceeds (3R/ρ)². -/
theorem sqrt_mul_le {R ρ N d : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hN : (3 * R / ρ) ^ 2 < N)
    (hd : d ≤ 1 / N) : Real.sqrt d * R ≤ ρ / 3 := by
  have hNpos : 0 < N := lt_of_le_of_lt (sq_nonneg _) hN
  have hρne : ρ ≠ 0 := hρ.ne'
  have h1 : Real.sqrt d ≤ Real.sqrt (1 / N) := Real.sqrt_le_sqrt hd
  have h2 : (Real.sqrt (1 / N) * R) ^ 2 ≤ (ρ / 3) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), one_div, inv_mul_le_iff₀ hNpos]
    have h4 : (3 * R / ρ) ^ 2 * ρ ^ 2 = 9 * R ^ 2 := by
      field_simp
      ring
    have h5 : (3 * R / ρ) ^ 2 * ρ ^ 2 < N * ρ ^ 2 := mul_lt_mul_of_pos_right hN (pow_pos hρ 2)
    have h6 : N * (ρ / 3) ^ 2 = N * ρ ^ 2 / 9 := by ring
    rw [h6]
    linarith
  have h5 := (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg _) hR.le)
    (by positivity) two_ne_zero).mp h2
  exact (mul_le_mul_of_nonneg_right h1 hR.le).trans h5

/-- A polygon model of level c + 2 with enough vertices for the edge bound at level c + 1 and
for the Hölder modulus ρ/3. -/
theorem exists_near_model (F : ReversibleMetric n) (hn : 1 ≤ n) {c ρ R : ℝ} (hρ0 : 0 < ρ)
    (hR : 0 < R) :
    ∃ (N' : ℕ) (M : PolygonModelData F (c + 2) (N' + 1)),
      (∀ q : ZMod (N' + 1) → Sphere n,
        polyEnergy F (N' + 1) (fun i => (q i : Ambient n)) ≤ (c + 1) ^ 2 →
        ∀ i : ZMod (N' + 1), ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2) ∧
      ∀ d : ℝ, d ≤ 1 / ((N' + 1 : ℕ) : ℝ) → Real.sqrt d * R ≤ ρ / 3 := by
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := c + 2) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn (c + 1) (S₀.δ / 2) (half_pos S₀.pos)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((3 * R / ρ) ^ 2)
  have hN0 : N₀ ≤ max (max N₀ N₁) N₂ + 1 :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (Nat.le_succ _)
  have hN1 : N₁ ≤ max (max N₀ N₁) N₂ + 1 :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (Nat.le_succ _)
  have hN2 : (N₂ : ℝ) ≤ ((max (max N₀ N₁) N₂ + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right _ _).trans (Nat.le_succ _)
  refine ⟨max (max N₀ N₁) N₂, PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (max (max N₀ N₁) N₂ + 1) hN0 (Nat.succ_pos _) u hu s t hs ht hst, ?_, ?_⟩
  · exact fun q hq i => hN₁ (max (max N₀ N₁) N₂ + 1) hN1 q hq i
  · exact fun d hd => sqrt_mul_le hR hρ0 (hN₂.trans_le hN2) hd

/-- The restricted Birkhoff shortening is the staggered straightening of the straightening. -/
theorem restrict_shortening_D {F : ReversibleMetric n} {B b : ℝ} {N : ℕ} [NeZero N]
    (M : PolygonModelData F B N) (hB : 0 < B) (hbB : b ≤ B) (x : lev F b) :
    ((restrict (Birkhoff.shortening M hB) hbB).D x : SphereLoop n) =
      Birkhoff.stag M 1 (deform M (1, (x : SphereLoop n))) := rfl

/-- Uniform localization: for tight cuts a' < c < b around a positive level c and ρ > 0, some
shortening D of t_b is such that every loop x of t_b with √E(D x) > a' is uniformly within ρ of
a tangent critical loop of energy c². -/
theorem exists_near (F : ReversibleMetric n) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) {ρ : ℝ}
    (hρ0 : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Shortening.Data F b, ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) →
        ∃ γ : SphereLoop n, TangentCritical F γ ∧ energy F γ = c ^ 2 ∧
          ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
            ‖continuousRepresentative ((x : SphereLoop n).data : Space n) t -
              continuousRepresentative (γ.data : Space n) t‖ ≤ ρ := by
  obtain ⟨R, hR, hhold⟩ := exists_holder F (A := c + 1) (by linarith)
  obtain ⟨N', M, hedge, hmod⟩ := exists_near_model F hn (c := c) hρ0 hR
  obtain ⟨ε, hε0, hε1, hε2, hnear⟩ := near_of_model M hn hc hρ0 hhold hmod hedge
  have hB : 0 < c + 2 := by linarith
  refine ⟨ε, hε0, ?_⟩
  intro a' b ha1 ha2 hb1 hb2
  have hbB : b ≤ c + 2 := by linarith
  have ha'0 : 0 < a' := by linarith
  refine ⟨restrict (Birkhoff.shortening M hB) hbB, fun x hx => ?_⟩
  have hb0 : 0 < b := hc.trans hb1
  have hxb : energy F (x : SphereLoop n) < b ^ 2 := (Birkhoff.mem_lev_iff hb0 _).mp x.2
  have hbε : b ^ 2 < (c + ε) ^ 2 := pow_lt_pow_left₀ hb2 hb0.le two_ne_zero
  rw [restrict_shortening_D M hB hbB x] at hx
  have h1 : a' ^ 2 < energy F (Birkhoff.stag M 1 (deform M (1, (x : SphereLoop n)))) :=
    (Real.lt_sqrt ha'0.le).mp hx
  have h2 : (c - ε) ^ 2 < a' ^ 2 := pow_lt_pow_left₀ ha1 (by linarith) two_ne_zero
  exact hnear (x : SphereLoop n) (hxb.trans hbε) (h2.trans h1)

end

end Finsler.BirkhoffNear
