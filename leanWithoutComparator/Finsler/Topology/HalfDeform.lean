module

public import Finsler.Topology.ShorteningK
public import Finsler.Topology.FiniteCut

/-! Deformations of a sublevel commuting with the half rotation, with compact image. The curve
shortening homotopy of a polygon model with an even number of vertices commutes with the half
rotation at all times, and so do the homotopies to its iterates. If the interval [a₀, b] has no
critical levels, some iterate of the curve shortening map takes t_b into t_{a₀}; one more step
maps into the rotated broken geodesics of the polygons of energy at most a₀², a compact set of
loops contained in t_b. Hence t_b carries a map homotopic to the identity, by a homotopy along
which the energy does not increase and which commutes with the half rotation, such that the map
commutes with the reversal and the half rotation and takes values in a compact subset of t_b.
With finitely many prime closed geodesic images this holds at every regular cut b > 0. -/

@[expose] public section

namespace Finsler.HalfDeform

open Set Topology
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SobolevReverse
open Finsler.PolygonModel Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSampling
open Finsler.BorelK Finsler.BirkhoffDescent Finsler.ShorteningK Finsler.CriticalLevels
open Finsler.FiniteCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

/-- At every time, the concatenation of two homotopies is one of the two homotopies at some
time. -/
theorem trans_cases {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ f₂ : C(X, Y)}
    (G₁ : f₀.Homotopy f₁) (G₂ : f₁.Homotopy f₂) (τ : _root_.unitInterval) :
    (∃ σ : _root_.unitInterval, ∀ x : X, (G₁.trans G₂) (τ, x) = G₁ (σ, x)) ∨
      ∃ σ : _root_.unitInterval, ∀ x : X, (G₁.trans G₂) (τ, x) = G₂ (σ, x) := by
  by_cases h : (τ : ℝ) ≤ 1 / 2
  · refine Or.inl ⟨⟨2 * τ, (_root_.unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨τ.2.1, h⟩⟩, fun x => ?_⟩
    rw [ContinuousMap.Homotopy.trans_apply]
    exact dite_eq_left h
  · refine Or.inr ⟨⟨2 * τ - 1, _root_.unitInterval.two_mul_sub_one_mem_iff.2
      ⟨(not_le.1 h).le, τ.2.2⟩⟩, fun x => ?_⟩
    rw [ContinuousMap.Homotopy.trans_apply]
    exact dite_eq_right h

/-- The homotopy of a shortening commutes with the half rotation. -/
def HalfCommG {F : ReversibleMetric n} {b : ℝ} (S : Shortening.Data F b) : Prop :=
  ∀ (τ : _root_.unitInterval) (x : lev F b),
    (S.G (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) : Loops n) =
      half +ᵥ (S.G (τ, x) : SphereLoop n)

theorem halfComm_of_halfCommG {F : ReversibleMetric n} {b : ℝ} {S : Shortening.Data F b}
    (h : HalfCommG S) : HalfComm S := by
  intro x
  have h1 := h 1 x
  rw [S.G.apply_one, S.G.apply_one] at h1
  exact h1

/-- The curve shortening homotopy of a polygon model with an even number of vertices commutes
with the half rotation. -/
theorem halfCommG_shortening {F : ReversibleMetric n} {a : ℝ} (N₁ : ℕ) [NeZero N₁]
    (M : PolygonModelData F a (2 * N₁)) (ha : 0 < a) : HalfCommG (Birkhoff.shortening M ha) := by
  intro τ x
  rcases trans_cases (Birkhoff.g1 M ha) (Birkhoff.g21 M ha) τ with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have e : deform M ((σ : ℝ), ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) +ᵥ
        (x : SphereLoop n)) =
        ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) +ᵥ deform M ((σ : ℝ), (x : SphereLoop n)) :=
      deform_rotate_nat M N₁ ((σ : ℝ), (x : SphereLoop n))
    change ((((Birkhoff.g1 M ha).trans (Birkhoff.g21 M ha))
        (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) : lev F a) : Loops n) =
      half +ᵥ ((((Birkhoff.g1 M ha).trans (Birkhoff.g21 M ha)) (τ, x) : lev F a) : SphereLoop n)
    rw [hσ, hσ]
    change deform M ((σ : ℝ), half +ᵥ (x : SphereLoop n)) =
      half +ᵥ deform M ((σ : ℝ), (x : SphereLoop n))
    rw [half_eq N₁, e]
  · have e : deform M (1, ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) +ᵥ
        (x : SphereLoop n)) =
        ((((N₁ : ℕ) : ℝ) / ((2 * N₁ : ℕ) : ℝ) : ℝ) : Circ) +ᵥ deform M (1, (x : SphereLoop n)) :=
      deform_rotate_nat M N₁ ((1 : ℝ), (x : SphereLoop n))
    change ((((Birkhoff.g1 M ha).trans (Birkhoff.g21 M ha))
        (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) : lev F a) : Loops n) =
      half +ᵥ ((((Birkhoff.g1 M ha).trans (Birkhoff.g21 M ha)) (τ, x) : lev F a) : SphereLoop n)
    rw [hσ, hσ]
    change Birkhoff.stag M (σ : ℝ) (deform M (1, half +ᵥ (x : SphereLoop n))) =
      half +ᵥ Birkhoff.stag M (σ : ℝ) (deform M (1, (x : SphereLoop n)))
    rw [half_eq N₁, e, stag_rotate_nat]

/-- The restriction of a shortening whose homotopy commutes with the half rotation has the same
property. -/
theorem halfCommG_restrict {F : ReversibleMetric n} {b b₁ : ℝ} (S : Shortening.Data F b₁)
    (hb : b ≤ b₁) (h : HalfCommG S) : HalfCommG (restrict S hb) := by
  intro τ x
  exact h τ (Set.inclusion (lev_mono F hb) x)

section Iterates

variable {F : ReversibleMetric n} {b : ℝ} (S : Shortening.Data F b)

/-- The iterates of a shortening commute with the reversal. -/
theorem iter_rev (k : ℕ) (x : lev F b) :
    (Shortening.iter S k ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : Loops n) =
      reverseSphere (Shortening.iter S k x : SphereLoop n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : Shortening.iter S k ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ =
        ⟨reverseSphere (Shortening.iter S k x : SphereLoop n),
          reverse_mem_lev F (Shortening.iter S k x).2⟩ := Subtype.ext ih
    change (S.D (Shortening.iter S k ⟨reverseSphere (x : SphereLoop n),
        reverse_mem_lev F x.2⟩) : Loops n) =
      reverseSphere (S.D (Shortening.iter S k x) : SphereLoop n)
    rw [e]
    exact S.rev (Shortening.iter S k x)

/-- The iterates of a shortening commuting with the half rotation commute with it. -/
theorem iter_half (h : HalfComm S) (k : ℕ) (x : lev F b) :
    (Shortening.iter S k ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : Loops n) =
      half +ᵥ (Shortening.iter S k x : SphereLoop n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : Shortening.iter S k ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ =
        ⟨half +ᵥ (Shortening.iter S k x : SphereLoop n),
          half_mem_lev F (Shortening.iter S k x).2⟩ := Subtype.ext ih
    change (S.D (Shortening.iter S k ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) :
      Loops n) = half +ᵥ (S.D (Shortening.iter S k x) : SphereLoop n)
    rw [e]
    exact h (Shortening.iter S k x)

/-- The homotopies to the iterates commute with the half rotation. -/
theorem iterHomotopy_half (hG : HalfCommG S) (k : ℕ) :
    ∀ (τ : _root_.unitInterval) (x : lev F b),
      (Shortening.iterHomotopy S k (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) :
        Loops n) = half +ᵥ (Shortening.iterHomotopy S k (τ, x) : SphereLoop n) := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    intro τ x
    rcases trans_cases (Shortening.iterHomotopy S k) (Shortening.stepHomotopy S k) τ with
      ⟨σ, hσ⟩ | ⟨σ, hσ⟩
    · change ((((Shortening.iterHomotopy S k).trans (Shortening.stepHomotopy S k))
          (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) : lev F b) : Loops n) =
        half +ᵥ ((((Shortening.iterHomotopy S k).trans (Shortening.stepHomotopy S k)) (τ, x) :
          lev F b) : SphereLoop n)
      rw [hσ, hσ]
      exact ih σ x
    · have e : Shortening.iter S k ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ =
          ⟨half +ᵥ (Shortening.iter S k x : SphereLoop n),
            half_mem_lev F (Shortening.iter S k x).2⟩ :=
        Subtype.ext (iter_half S (halfComm_of_halfCommG hG) k x)
      change ((((Shortening.iterHomotopy S k).trans (Shortening.stepHomotopy S k))
          (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) : lev F b) : Loops n) =
        half +ᵥ ((((Shortening.iterHomotopy S k).trans (Shortening.stepHomotopy S k)) (τ, x) :
          lev F b) : SphereLoop n)
      rw [hσ, hσ]
      change (S.G (σ, Shortening.iter S k ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) :
        Loops n) = half +ᵥ (S.G (σ, Shortening.iter S k x) : SphereLoop n)
      rw [e]
      exact hG σ (Shortening.iter S k x)

end Iterates

/-- A deformation of the sublevel t_b into a compact part of it which commutes with the half
rotation at all times: a map r of t_b homotopic to the identity, by a homotopy along which the
energy does not increase and which commutes with the half rotation, such that r commutes with
the reversal and takes values in a compact subset of t_b. -/
structure Data (F : ReversibleMetric n) (b : ℝ) where
  r : C(lev F b, lev F b)
  H : (ContinuousMap.id (lev F b)).Homotopy r
  energy_le : ∀ (τ : _root_.unitInterval) (x : lev F b),
    energy F (H (τ, x) : SphereLoop n) ≤ energy F (x : SphereLoop n)
  rev : ∀ x : lev F b,
    (r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : Loops n) =
      reverseSphere (r x : SphereLoop n)
  half_H : ∀ (τ : _root_.unitInterval) (x : lev F b),
    (H (τ, ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩) : Loops n) =
      half +ᵥ (H (τ, x) : SphereLoop n)
  P : Set (Loops n)
  compact : IsCompact P
  subset : P ⊆ lev F b
  r_mem : ∀ x : lev F b, (r x : Loops n) ∈ P

/-- The map of the deformation commutes with the half rotation. -/
theorem data_half {F : ReversibleMetric n} {b : ℝ} (d : Data F b) (x : lev F b) :
    (d.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : Loops n) =
      half +ᵥ (d.r x : SphereLoop n) := by
  have h := d.half_H 1 x
  rw [d.H.apply_one, d.H.apply_one] at h
  exact h

/-- On an interval [a₀, b] without critical levels the sublevel t_b has a deformation into a
compact part of it commuting with the half rotation. -/
theorem exists_data (F : ReversibleMetric n) (hn : 1 ≤ n) {a₀ b : ℝ} (ha₀ : 0 < a₀)
    (hab : a₀ < b) (hreg : ∀ x ∈ Icc a₀ b, x ∉ crit F) : Nonempty (Data F b) := by
  have hb : 0 < b := ha₀.trans hab
  have hb1 : 0 < b + 1 := by linarith
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S₀.δ) (a := b + 1) S₀.pos
  obtain ⟨N₁, hN₁⟩ := exists_edge_bound F hn b (S₀.δ / 2) (half_pos S₀.pos)
  have hN0 : N₀ ≤ 2 * (max N₀ N₁ + 1) := by
    have := le_max_left N₀ N₁
    omega
  have hN1 : N₁ ≤ 2 * (max N₀ N₁ + 1) := by
    have := le_max_right N₀ N₁
    omega
  let M : PolygonModelData F (b + 1) (2 * (max N₀ N₁ + 1)) :=
    PolygonModelData.mk S₀ fun u hu s t hs ht hst =>
      hN₀ (2 * (max N₀ N₁ + 1)) hN0 (by omega) u hu s t hs ht hst
  have hedge : ∀ q : ZMod (2 * (max N₀ N₁ + 1)) → Sphere n,
      polyEnergy F (2 * (max N₀ N₁ + 1)) (fun i => (q i : Ambient n)) ≤ b ^ 2 →
      ∀ i : ZMod (2 * (max N₀ N₁ + 1)), ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2 :=
    fun q hq i => hN₁ (2 * (max N₀ N₁ + 1)) hN1 q hq i
  have ha₀b : a₀ ^ 2 < b ^ 2 := pow_lt_pow_left₀ hab ha₀.le two_ne_zero
  have hbb : b ^ 2 < (b + 1) ^ 2 := pow_lt_pow_left₀ (by linarith) hb.le two_ne_zero
  have hedge₀ : ∀ q : ZMod (2 * (max N₀ N₁ + 1)) → Sphere n,
      polyEnergy F (2 * (max N₀ N₁ + 1)) (fun i => (q i : Ambient n)) ≤ a₀ ^ 2 →
      ∀ i : ZMod (2 * (max N₀ N₁ + 1)), ‖(q (i + 1) : Ambient n) - q i‖ ≤ M.δ / 2 :=
    fun q hq i => hedge q (hq.trans ha₀b.le) i
  obtain ⟨k, hk⟩ := descent_of_model M hb1 hn ha₀ hab.le (by linarith : b < b + 1) hedge
    (fun u hu h1 h2 => hreg (Real.sqrt (energy F u))
      ⟨(Real.le_sqrt' ha₀).mpr h1, Real.sqrt_le_iff.mpr ⟨hb.le, h2⟩⟩
      (crit_mem F u hu (lt_of_lt_of_le (pow_pos ha₀ 2) h1)))
  have hGM : HalfCommG (Birkhoff.shortening M hb1) :=
    halfCommG_shortening (max N₀ N₁ + 1) M hb1
  have hle : b ≤ b + 1 := by linarith
  have hG : HalfCommG (restrict (Birkhoff.shortening M hb1) hle) :=
    halfCommG_restrict _ hle hGM
  -- the compact set
  have hcpt : cpt M a₀ ⊆ shortDom M := fun p hp => (cpt_subset_dom M ha₀b hp).1
  have hK : IsCompact (ambBroken M '' cpt M a₀) :=
    (cpt_isCompact M a₀ hedge₀).image_of_continuousOn ((ambBroken_continuousOn M).mono hcpt)
  have hrot : Continuous fun u : SphereLoop n =>
      (((-(1 / (2 * ((2 * (max N₀ N₁ + 1) : ℕ) : ℝ))) : ℝ)) : Circ) +ᵥ u :=
    continuous_const_vadd _
  refine ⟨{ r := Shortening.iter (restrict (Birkhoff.shortening M hb1) hle) (k + 1)
            H := Shortening.iterHomotopy (restrict (Birkhoff.shortening M hb1) hle) (k + 1)
            energy_le := Shortening.energy_iterHomotopy_le _ (k + 1)
            rev := iter_rev _ (k + 1)
            half_H := iterHomotopy_half _ hG (k + 1)
            P := (fun u : SphereLoop n =>
              (((-(1 / (2 * ((2 * (max N₀ N₁ + 1) : ℕ) : ℝ))) : ℝ)) : Circ) +ᵥ u) ''
                (ambBroken M '' cpt M a₀)
            compact := hK.image hrot
            subset := ?_
            r_mem := ?_ }⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine (Birkhoff.mem_lev_iff hb _).mpr ?_
    have h' : energy F (ambBroken M p) < b ^ 2 := (cpt_subset_dom M ha₀b hp).2
    exact (Finsler.SobolevShiftEnergy.energy_vadd F _ (ambBroken M p)).trans_lt h'
  · intro x
    have hD : (Shortening.iter (restrict (Birkhoff.shortening M hb1) hle) (k + 1) x : Loops n) =
        Birkhoff.stag M 1 (deform M (1,
          (Shortening.iter (restrict (Birkhoff.shortening M hb1) hle) k x : SphereLoop n))) :=
      rfl
    have hy : (Shortening.iter (restrict (Birkhoff.shortening M hb1) hle) k x : Loops n) ∈
        lev F a₀ := by
      rw [iter_restrict]
      exact hk _ x.2
    have hyE : energy F (Shortening.iter (restrict (Birkhoff.shortening M hb1) hle) k x :
        SphereLoop n) < a₀ ^ 2 := (Birkhoff.mem_lev_iff ha₀ _).mp hy
    rw [hD]
    generalize (Shortening.iter (restrict (Birkhoff.shortening M hb1) hle) k x : SphereLoop n) =
      y at hyE ⊢
    have hyb : energy F y < (b + 1) ^ 2 := hyE.trans (ha₀b.trans hbb)
    have hz : energy F (deform M (1, y)) ≤ energy F y :=
      energy_deform_le M (p := ((1 : ℝ), y)) ⟨⟨zero_le_one, le_rfl⟩, hyb⟩
    have hz'a : energy F ((((1 / (2 * ((2 * (max N₀ N₁ + 1) : ℕ) : ℝ)) : ℝ)) : Circ) +ᵥ
        deform M (1, y)) < a₀ ^ 2 := by
      rw [Finsler.SobolevShiftEnergy.energy_vadd]
      exact hz.trans_lt hyE
    have hz'b := hz'a.trans (ha₀b.trans hbb)
    exact ⟨deform M (1, (((1 / (2 * ((2 * (max N₀ N₁ + 1) : ℕ) : ℝ)) : ℝ)) : Circ) +ᵥ
        deform M (1, y)), ⟨sampleAmb _, sampleAmb_mem_cpt M hz'b hz'a.le,
      ambBroken_sampleAmb M hz'b⟩, rfl⟩

/-- With finitely many prime closed geodesic images, a regular cut is the upper end of an
interval without critical levels. -/
theorem exists_regular_below (F : ReversibleMetric n) (hfin : (primeImages F).Finite) {b : ℝ}
    (hb : 0 < b) (hbc : b ∉ crit F) : ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < b ∧ ∀ x ∈ Icc a₀ b, x ∉ crit F := by
  have hS : (crit F ∩ Icc 0 b).Finite := crit_finite F hfin 0 b
  have hmem : b ∈ (crit F ∩ Icc 0 b)ᶜ := fun h => hbc h.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl b hmem
  have h3 : 0 < min ε b := lt_min hε hb
  have h1 : min ε b ≤ ε := min_le_left _ _
  have h2 : min ε b ≤ b := min_le_right _ _
  refine ⟨b - min ε b / 2, by linarith, by linarith, fun x hx hxc => ?_⟩
  have hxball : x ∈ Metric.ball b ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact hball hxball ⟨hxc, by linarith [hx.1], hx.2⟩

/-- With finitely many prime closed geodesic images, the sublevel at every regular cut b > 0 has
a deformation into a compact part of it commuting with the half rotation. -/
theorem exists_data_of_regular (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {b : ℝ} (hb : 0 < b) (hbc : b ∉ crit F) :
    Nonempty (Data F b) := by
  obtain ⟨a₀, ha₀, hab, hreg⟩ := exists_regular_below F hfin hb hbc
  exact exists_data F hn ha₀ hab hreg

end

end Finsler.HalfDeform
