module

public import Finsler.Topology.BorelFixed
public import Finsler.Topology.BorelDeformation
public import Finsler.Analysis.IntervalH1RadialRetraction
public import Finsler.Geometry.MilnorContinuity
public import Mathlib.Tactic.Module
public import Mathlib.Topology.Maps.Proper.Basic

/-! A linear retraction of a neighbourhood of the loops fixed by the half rotation. For a loop u
whose half rotation τu is uniformly closer to it than 1, the loops
h_s(u) = normalize((1 − s/2) u + (s/2) τu), 0 ≤ s ≤ 1, are defined; they depend continuously on
(s, u) in the H¹ topology, because the linear combination is continuous in the ambient H¹ space
and the radial normalization is a continuous superposition operator. Pointwise, h_s(u)(t) is the
radial projection of a point of the chord from u(t) to u(t + 1/2). Hence h_0 is the identity,
h_s fixes the loops fixed by the half rotation, h_1 takes values in them, h_s commutes with the
half rotation and with the reversal, h_s(u) is again uniformly closer than 1 to its half
rotation, and h_{s'} ∘ h_s = h_{s + s' − s s'}. For a set X of loops the loops u for which all
h_s(u) lie in X form a set which is open if X is, invariant under reversal and half rotation
if X is, contains the loops of X fixed by the half rotation and deforms onto them inside
itself; so its inclusion is an isomorphism on relative cohomology with the pair of the fixed
loops. No energy estimate is used. -/

@[expose] public section

namespace Finsler.HalfRetract

open Set Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.SobolevRadialRetraction Finsler.SobolevCircleRepresentative
open Finsler.MilnorHomotopy Finsler.MilnorEquivariance Finsler.MilnorContinuity
open Finsler.BorelLoop Finsler.BorelK Finsler.BorelDeformation Finsler.BorelComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### Chords of the unit sphere -/

section Chords

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_comb {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (a b : ℝ) :
    ‖a • x + b • y‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * inner ℝ x y := by
  rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, hx, hy, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

theorem norm_comb_comm {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (a b : ℝ) :
    ‖a • x + b • y‖ = ‖a • y + b • x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_comb hx hy, norm_sq_comb hy hx,
    real_inner_comm x y]

/-- The points of the first half of a chord shorter than 1 have norm greater than 1/2. -/
theorem half_lt_norm_comb {x y : E} (hx : ‖x‖ = 1) (hxy : ‖x - y‖ < 1) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1 / 2) : 1 / 2 < ‖(1 - σ) • x + σ • y‖ := by
  have e : (1 - σ) • x + σ • y = x - σ • (x - y) := by module
  have h := norm_sub_norm_le x (σ • (x - y))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, hx] at h
  have h2 : σ * ‖x - y‖ ≤ 1 / 2 * ‖x - y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  rw [e]
  linarith

theorem norm_comb_le_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1) : ‖(1 - σ) • x + σ • y‖ ≤ 1 := by
  have h := norm_add_le ((1 - σ) • x) (σ • y)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ), hx, hy] at h
  linarith

theorem one_sub_le_norm_comb {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1 / 2) : 1 - 2 * σ ≤ ‖(1 - σ) • x + σ • y‖ := by
  rw [← sq_le_sq₀ (by linarith) (norm_nonneg _), norm_sq_comb hx hy]
  have hin : -1 ≤ inner ℝ x y := by
    have h := abs_real_inner_le_norm x y
    rw [hx, hy, mul_one] at h
    exact (abs_le.mp h).1
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - σ))
    (by linarith : (0 : ℝ) ≤ inner ℝ x y + 1)]

end Chords

variable {n : ℕ}

/-- The radial projection of the point with parameter σ of the chord from x to y. -/
def mid (σ : ℝ) (x y : Ambient n) : Ambient n := radial ((1 - σ) • x + σ • y)

theorem mid_eq {x y : Ambient n} (hx : ‖x‖ = 1) (hxy : ‖x - y‖ < 1) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1 / 2) :
    mid σ x y = ‖(1 - σ) • x + σ • y‖⁻¹ • ((1 - σ) • x + σ • y) :=
  radial_eq (half_lt_norm_comb hx hxy h0 h1).le

theorem mid_self {x : Ambient n} (hx : ‖x‖ = 1) (σ : ℝ) : mid σ x x = x := by
  have e : (1 - σ) • x + σ • x = x := by module
  rw [mid, e, radial_of_norm_one hx]

theorem mid_zero {x : Ambient n} (hx : ‖x‖ = 1) (y : Ambient n) : mid 0 x y = x := by
  have e : (1 - (0 : ℝ)) • x + (0 : ℝ) • y = x := by module
  rw [mid, e, radial_of_norm_one hx]

theorem mid_half_comm (x y : Ambient n) : mid (1 / 2) x y = mid (1 / 2) y x := by
  have e : (1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y =
      (1 - (1 / 2 : ℝ)) • y + (1 / 2 : ℝ) • x := by module
  rw [mid, mid, e]

theorem radial_smul {d : Ambient n} {μ : ℝ} (hμ : 1 ≤ μ) (hd : 1 / 2 ≤ ‖d‖) :
    radial (μ • d) = radial d := by
  have hμ0 : 0 < μ := by linarith
  have hd0 : 0 < ‖d‖ := by linarith
  have hμ' : μ ≠ 0 := hμ0.ne'
  have hd' : ‖d‖ ≠ 0 := hd0.ne'
  have hn : ‖μ • d‖ = μ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ0]
  have h2 : 1 / 2 ≤ ‖μ • d‖ := by
    rw [hn]
    nlinarith
  have h3 : (μ * ‖d‖)⁻¹ * μ = ‖d‖⁻¹ := by field_simp
  rw [radial_eq h2, radial_eq hd, hn, smul_smul, h3]

/-- Two successive projections along the chord are one projection. -/
theorem mid_mid {x y : Ambient n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ < 1)
    {σ σ' : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1 / 2) (h0' : 0 ≤ σ') (h1' : σ' ≤ 1 / 2) :
    mid σ' (mid σ x y) (mid σ y x) = mid (σ + σ' - 2 * σ * σ') x y := by
  have hyx : ‖y - x‖ < 1 := by rwa [norm_sub_rev]
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = ‖(1 - σ) • x + σ • y‖ := ⟨_, rfl⟩
  have hl : 1 / 2 < l := by
    rw [hl_def]
    exact half_lt_norm_comb hx hxy h0 h1
  have hl1 : l ≤ 1 := by
    rw [hl_def]
    exact norm_comb_le_one hx hy h0 (by linarith)
  have e1 : mid σ x y = l⁻¹ • ((1 - σ) • x + σ • y) := by rw [mid_eq hx hxy h0 h1, hl_def]
  have e2 : mid σ y x = l⁻¹ • ((1 - σ) • y + σ • x) := by
    rw [mid_eq hy hyx h0 h1, hl_def, norm_comb_comm hx hy (1 - σ) σ]
  have h0'' : 0 ≤ σ + σ' - 2 * σ * σ' := by
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * σ')]
  have h1'' : σ + σ' - 2 * σ * σ' ≤ 1 / 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * σ) (by linarith : (0 : ℝ) ≤ 1 - 2 * σ')]
  have hd := half_lt_norm_comb hx hxy h0'' h1''
  have e3 : (1 - σ') • (l⁻¹ • ((1 - σ) • x + σ • y)) + σ' • (l⁻¹ • ((1 - σ) • y + σ • x)) =
      l⁻¹ • ((1 - (σ + σ' - 2 * σ * σ')) • x + (σ + σ' - 2 * σ * σ') • y) := by module
  rw [mid, e1, e2, e3, mid]
  exact radial_smul ((one_le_inv₀ (by linarith)).mpr hl1) hd.le

/-- The two projections of a chord shorter than 1 are closer than its end points. -/
theorem norm_mid_sub_le {x y : Ambient n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ < 1)
    {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1 / 2) : ‖mid σ x y - mid σ y x‖ ≤ ‖x - y‖ := by
  have hyx : ‖y - x‖ < 1 := by rwa [norm_sub_rev]
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = ‖(1 - σ) • x + σ • y‖ := ⟨_, rfl⟩
  have hl : 1 / 2 < l := by
    rw [hl_def]
    exact half_lt_norm_comb hx hxy h0 h1
  have hle : 1 - 2 * σ ≤ l := by
    rw [hl_def]
    exact one_sub_le_norm_comb hx hy h0 h1
  have hl0 : 0 < l := by linarith
  have e1 : mid σ x y = l⁻¹ • ((1 - σ) • x + σ • y) := by rw [mid_eq hx hxy h0 h1, hl_def]
  have e2 : mid σ y x = l⁻¹ • ((1 - σ) • y + σ • x) := by
    rw [mid_eq hy hyx h0 h1, hl_def, norm_comb_comm hx hy (1 - σ) σ]
  have e : mid σ x y - mid σ y x = (l⁻¹ * (1 - 2 * σ)) • (x - y) := by
    rw [e1, e2]
    module
  have h3 : l⁻¹ * (1 - 2 * σ) ≤ 1 := by
    rw [inv_mul_le_iff₀ hl0]
    linarith
  rw [e, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hl0.le) (by linarith))]
  exact mul_le_of_le_one_left (norm_nonneg _) h3

/-! ### Points of loops -/

theorem norm_pt (u : SphereLoop n) (t : ℝ) : ‖(pt u t : Ambient n)‖ = 1 :=
  norm_eq_of_mem_sphere (pt u t)

theorem eq_of_pt {u v : SphereLoop n} (h : ∀ t ∈ Icc (0 : ℝ) 1, pt u t = pt v t) : u = v := by
  apply Finsler.SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (u.data : Space n) t =
    continuousRepresentative (v.data : Space n) t
  rw [← pt_coe u t.2, ← pt_coe v t.2, h t t.2]

theorem pt_rev (u : SphereLoop n) (x : ℝ) : pt (reverseSphere u) x = pt u (-x) :=
  Subtype.ext (Finsler.BorelFixed.realMap_reverse u x)

/-- A set of pairs (s, y), s in the unit interval, is open in y uniformly in s. -/
theorem isOpen_forall_unitInterval {Y : Type*} [TopologicalSpace Y]
    {U : Set (_root_.unitInterval × Y)} (hU : IsOpen U) :
    IsOpen {y : Y | ∀ s : _root_.unitInterval, (s, y) ∈ U} := by
  have h : {y : Y | ∀ s : _root_.unitInterval, (s, y) ∈ U}ᶜ = Prod.snd '' Uᶜ := by
    ext y
    constructor
    · intro hy
      by_contra hcon
      apply hy
      intro s
      by_contra hs
      exact hcon ⟨(s, y), hs, rfl⟩
    · rintro ⟨⟨s, y'⟩, hp, rfl⟩ hall
      exact hp (hall s)
  rw [← isClosed_compl_iff, h]
  exact isClosedMap_snd_of_compactSpace _ hU.isClosed_compl

/-! ### Loops close to their half rotation -/

/-- The loops whose half rotation is uniformly closer to them than 1. -/
def near (n : ℕ) : Set (Loops n) :=
  {u | ∀ s : _root_.unitInterval,
    ‖(pt u (s : ℝ) : Ambient n) - (pt u ((s : ℝ) + 1 / 2) : Ambient n)‖ < 1}

theorem near_all {u : SphereLoop n} (hu : u ∈ near n) (t : ℝ) :
    ‖(pt u t : Ambient n) - (pt u (t + 1 / 2) : Ambient n)‖ < 1 := by
  have hfl := Int.floor_le t
  have hfl' := Int.lt_floor_add_one t
  have e1 : pt u t = pt u (t - ⌊t⌋) := pt_eq_of_sub_int u (-⌊t⌋) (by push_cast; ring)
  have e2 : pt u (t + 1 / 2) = pt u (t - ⌊t⌋ + 1 / 2) :=
    pt_eq_of_sub_int u (-⌊t⌋) (by push_cast; ring)
  rw [e1, e2]
  exact hu ⟨t - ⌊t⌋, ⟨by linarith, by linarith⟩⟩

theorem near_isOpen : IsOpen (near n) := by
  have hf : Continuous fun p : _root_.unitInterval × SphereLoop n => ((p.1 : ℝ), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have h1 : Continuous fun q : ℝ × SphereLoop n => (pt q.2 q.1 : Ambient n) :=
    continuous_subtype_val.comp (pt_continuous (g := fun q => q.1) continuous_fst)
  have h2 : Continuous fun q : ℝ × SphereLoop n => (pt q.2 (q.1 + 1 / 2) : Ambient n) :=
    continuous_subtype_val.comp
      (pt_continuous (g := fun q => q.1 + 1 / 2) (continuous_fst.add continuous_const))
  have h3 : Continuous fun q : ℝ × SphereLoop n =>
      ‖(pt q.2 q.1 : Ambient n) - (pt q.2 (q.1 + 1 / 2) : Ambient n)‖ := (h1.sub h2).norm
  have h4 : Continuous ((fun q : ℝ × SphereLoop n =>
      ‖(pt q.2 q.1 : Ambient n) - (pt q.2 (q.1 + 1 / 2) : Ambient n)‖) ∘
      fun p : _root_.unitInterval × SphereLoop n => ((p.1 : ℝ), p.2)) := h3.comp hf
  exact isOpen_forall_unitInterval (isOpen_lt h4 continuous_const)

theorem half_mem_near {u : SphereLoop n} (hu : u ∈ near n) : half +ᵥ u ∈ near n := by
  intro s
  have h1 : pt (half +ᵥ u) (s : ℝ) = pt u ((s : ℝ) + 1 / 2) := pt_vadd u (1 / 2) s
  have h2 : pt (half +ᵥ u) ((s : ℝ) + 1 / 2) = pt u ((s : ℝ) + 1 / 2 + 1 / 2) :=
    pt_vadd u (1 / 2) _
  rw [h1, h2]
  exact near_all hu ((s : ℝ) + 1 / 2)

theorem rev_mem_near {u : SphereLoop n} (hu : u ∈ near n) : reverseSphere u ∈ near n := by
  intro s
  have e : pt u (-((s : ℝ) + 1 / 2)) = pt u (-(s : ℝ) + 1 / 2) :=
    pt_eq_of_sub_int u 1 (by push_cast; ring)
  rw [pt_rev, pt_rev, e]
  exact near_all hu (-(s : ℝ))

theorem fixed_mem_near {u : SphereLoop n} (hu : half +ᵥ u = u) : u ∈ near n := by
  intro s
  have h1 : pt (half +ᵥ u) (s : ℝ) = pt u ((s : ℝ) + 1 / 2) := pt_vadd u (1 / 2) s
  rw [hu] at h1
  rw [← h1, sub_self, norm_zero]
  exact one_pos

/-! ### The linear homotopy -/

/-- The linear combination (1 − s/2) u + (s/2) τu in the ambient periodic H¹ space. -/
def mix (s : ℝ) (u : SphereLoop n) : periodicSubmodule n :=
  (1 - s / 2) • u.data + (s / 2) • (half +ᵥ u).data

theorem mix_continuous : Continuous fun p : ℝ × SphereLoop n => mix p.1 p.2 := by
  have hd := sphereLoop_periodicData_continuous n
  exact ((continuous_const.sub (continuous_fst.div_const 2)).smul (hd.comp continuous_snd)).add
    ((continuous_fst.div_const 2).smul (hd.comp (half_continuous.comp continuous_snd)))

theorem rep_mix (s : ℝ) (u : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative ((mix s u : periodicSubmodule n) : Space n) t =
      (1 - s / 2) • (pt u t : Ambient n) + (s / 2) • (pt u (t + 1 / 2) : Ambient n) := by
  have h1 : pt (half +ᵥ u) t = pt u (t + 1 / 2) := pt_vadd u (1 / 2) t
  change continuousRepresentative
    ((1 - s / 2) • (u.data : Space n) + (s / 2) • ((half +ᵥ u).data : Space n)) t = _
  rw [continuousRepresentative_add _ _ ht, continuousRepresentative_smul _ _ ht,
    continuousRepresentative_smul _ _ ht, ← pt_coe u ht, ← pt_coe (half +ᵥ u) ht, h1]

theorem mix_mem (s : _root_.unitInterval) {u : SphereLoop n} (hu : u ∈ near n) :
    mix (s : ℝ) u ∈ radialDomain n := by
  intro t ht
  rw [rep_mix _ _ ht]
  exact half_lt_norm_comb (norm_pt u t) (near_all hu t) (by linarith [s.2.1])
    (by linarith [s.2.2])

/-- The homotopy h_s(u) = normalize((1 − s/2) u + (s/2) τu). -/
def hmap (p : _root_.unitInterval × near n) : SphereLoop n :=
  retraction ⟨mix (p.1 : ℝ) (p.2 : SphereLoop n), mix_mem p.1 p.2.2⟩

theorem hmap_continuous : Continuous (hmap (n := n)) := by
  have hf : Continuous fun p : _root_.unitInterval × near n =>
      ((p.1 : ℝ), (p.2 : SphereLoop n)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h : Continuous ((fun q : ℝ × SphereLoop n => mix q.1 q.2) ∘
      fun p : _root_.unitInterval × near n => ((p.1 : ℝ), (p.2 : SphereLoop n))) :=
    mix_continuous.comp hf
  have h2 : Continuous fun p : _root_.unitInterval × near n =>
      (⟨mix (p.1 : ℝ) (p.2 : SphereLoop n), mix_mem p.1 p.2.2⟩ : radialDomain n) :=
    h.subtype_mk _
  have h3 : Continuous (retraction ∘ fun p : _root_.unitInterval × near n =>
      (⟨mix (p.1 : ℝ) (p.2 : SphereLoop n), mix_mem p.1 p.2.2⟩ : radialDomain n)) :=
    retraction_continuous.comp h2
  exact h3

theorem pt_hmap_of_mem (p : _root_.unitInterval × near n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (pt (hmap p) t : Ambient n) =
      mid ((p.1 : ℝ) / 2) (pt (p.2 : SphereLoop n) t) (pt (p.2 : SphereLoop n) (t + 1 / 2)) := by
  rw [pt_coe _ ht]
  change continuousRepresentative
    (radialData ((mix (p.1 : ℝ) (p.2 : SphereLoop n) : periodicSubmodule n) : Space n)) t = _
  rw [representative_radialData _ ht, rep_mix _ _ ht]
  rfl

/-- The points of h_s(u) are the radial projections of points of the chords from u(t) to
u(t + 1/2). -/
theorem pt_hmap (p : _root_.unitInterval × near n) (t : ℝ) :
    (pt (hmap p) t : Ambient n) =
      mid ((p.1 : ℝ) / 2) (pt (p.2 : SphereLoop n) t) (pt (p.2 : SphereLoop n) (t + 1 / 2)) := by
  have hfl := Int.floor_le t
  have hfl' := Int.lt_floor_add_one t
  have hI : t - ⌊t⌋ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have e1 : ∀ v : SphereLoop n, pt v t = pt v (t - ⌊t⌋) := fun v =>
    pt_eq_of_sub_int v (-⌊t⌋) (by push_cast; ring)
  have e2 : pt (p.2 : SphereLoop n) (t + 1 / 2) = pt (p.2 : SphereLoop n) (t - ⌊t⌋ + 1 / 2) :=
    pt_eq_of_sub_int _ (-⌊t⌋) (by push_cast; ring)
  rw [e1 (hmap p), e1 (p.2 : SphereLoop n), e2]
  exact pt_hmap_of_mem p hI

theorem hmap_zero (u : near n) : hmap (0, u) = (u : SphereLoop n) := by
  apply eq_of_pt
  intro t _
  apply Subtype.ext
  have hs : ((0 : _root_.unitInterval) : ℝ) / 2 = 0 := by simp
  rw [pt_hmap]
  dsimp only
  rw [hs, mid_zero (norm_pt _ t)]

/-- The homotopy fixes the loops fixed by the half rotation. -/
theorem hmap_fixed (s : _root_.unitInterval) (u : near n) (hu : half +ᵥ (u : SphereLoop n) = u) :
    hmap (s, u) = (u : SphereLoop n) := by
  apply eq_of_pt
  intro t _
  apply Subtype.ext
  have h1 : pt (half +ᵥ (u : SphereLoop n)) t = pt (u : SphereLoop n) (t + 1 / 2) :=
    pt_vadd _ (1 / 2) t
  rw [hu] at h1
  rw [pt_hmap]
  dsimp only
  rw [← h1, mid_self (norm_pt _ t)]

/-- The end of the homotopy is fixed by the half rotation. -/
theorem half_hmap_one (u : near n) : half +ᵥ hmap (1, u) = hmap (1, u) := by
  apply eq_of_pt
  intro t _
  apply Subtype.ext
  have h1 : pt (half +ᵥ hmap (1, u)) t = pt (hmap (1, u)) (t + 1 / 2) := pt_vadd _ (1 / 2) t
  have e : pt (u : SphereLoop n) (t + 1 / 2 + 1 / 2) = pt (u : SphereLoop n) t :=
    (pt_eq_of_sub_int _ 1 (by push_cast; ring)).symm
  have hs : ((1 : _root_.unitInterval) : ℝ) / 2 = 1 / 2 := by simp
  rw [h1, pt_hmap, pt_hmap]
  dsimp only
  rw [e, hs]
  exact mid_half_comm _ _

/-- The homotopy commutes with the half rotation. -/
theorem hmap_half (s : _root_.unitInterval) (u : near n) :
    hmap (s, ⟨half +ᵥ (u : SphereLoop n), half_mem_near u.2⟩) = half +ᵥ hmap (s, u) := by
  apply eq_of_pt
  intro t _
  apply Subtype.ext
  have h1 : pt (half +ᵥ hmap (s, u)) t = pt (hmap (s, u)) (t + 1 / 2) := pt_vadd _ (1 / 2) t
  have h2 : pt (half +ᵥ (u : SphereLoop n)) t = pt (u : SphereLoop n) (t + 1 / 2) :=
    pt_vadd _ (1 / 2) t
  have h3 : pt (half +ᵥ (u : SphereLoop n)) (t + 1 / 2) =
      pt (u : SphereLoop n) (t + 1 / 2 + 1 / 2) := pt_vadd _ (1 / 2) _
  rw [h1, pt_hmap, pt_hmap]
  dsimp only
  rw [h2, h3]

/-- The homotopy commutes with the reversal. -/
theorem hmap_rev (s : _root_.unitInterval) (u : near n) :
    hmap (s, ⟨reverseSphere (u : SphereLoop n), rev_mem_near u.2⟩) =
      reverseSphere (hmap (s, u)) := by
  apply eq_of_pt
  intro t _
  apply Subtype.ext
  have e : pt (u : SphereLoop n) (-(t + 1 / 2)) = pt (u : SphereLoop n) (-t + 1 / 2) :=
    pt_eq_of_sub_int _ 1 (by push_cast; ring)
  rw [pt_rev (hmap (s, u)) t, pt_hmap, pt_hmap]
  dsimp only
  rw [pt_rev, pt_rev, e]

/-- The loops h_s(u) are again uniformly closer than 1 to their half rotations. -/
theorem hmap_mem_near (s : _root_.unitInterval) (u : near n) : hmap (s, u) ∈ near n := by
  intro r
  have e : pt (u : SphereLoop n) ((r : ℝ) + 1 / 2 + 1 / 2) = pt (u : SphereLoop n) (r : ℝ) :=
    (pt_eq_of_sub_int _ 1 (by push_cast; ring)).symm
  have hxy := near_all u.2 (r : ℝ)
  rw [pt_hmap, pt_hmap]
  dsimp only
  rw [e]
  exact lt_of_le_of_lt (norm_mid_sub_le (norm_pt _ _) (norm_pt _ _) hxy (by linarith [s.2.1])
    (by linarith [s.2.2])) hxy

/-- The parameter s + s' − s s'. -/
def join (s s' : _root_.unitInterval) : _root_.unitInterval :=
  ⟨(s : ℝ) + s' - s * s', by
    have h1 := s.2.1
    have h2 := s.2.2
    have h3 := s'.2.1
    have h4 := s'.2.2
    constructor
    · nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 1 - s')]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s) (by linarith : (0 : ℝ) ≤ 1 - s')]⟩

/-- Two successive homotopies are one homotopy. -/
theorem hmap_hmap (s s' : _root_.unitInterval) (u : near n) :
    hmap (s', ⟨hmap (s, u), hmap_mem_near s u⟩) = hmap (join s s', u) := by
  apply eq_of_pt
  intro t _
  apply Subtype.ext
  have e : pt (u : SphereLoop n) (t + 1 / 2 + 1 / 2) = pt (u : SphereLoop n) t :=
    (pt_eq_of_sub_int _ 1 (by push_cast; ring)).symm
  have hxy := near_all u.2 t
  have hj : ((join s s' : _root_.unitInterval) : ℝ) / 2 =
      (s : ℝ) / 2 + (s' : ℝ) / 2 - 2 * ((s : ℝ) / 2) * ((s' : ℝ) / 2) := by
    change ((s : ℝ) + s' - s * s') / 2 = _
    ring
  rw [pt_hmap, pt_hmap, pt_hmap, pt_hmap]
  dsimp only
  rw [e, hj]
  exact mid_mid (norm_pt _ _) (norm_pt _ _) hxy (by linarith [s.2.1]) (by linarith [s.2.2])
    (by linarith [s'.2.1]) (by linarith [s'.2.2])

/-! ### The neighbourhood of the fixed loops of a set -/

/-- The loops close to their half rotation whose homotopy stays in X. -/
def tube (X : Set (Loops n)) : Set (Loops n) :=
  {u | u ∈ near n ∧ ∀ (hu : u ∈ near n) (s : _root_.unitInterval), hmap (s, ⟨u, hu⟩) ∈ X}

variable {X : Set (Loops n)}

theorem tube_subset : tube X ⊆ X := by
  intro u hu
  have h := hu.2 hu.1 0
  rw [hmap_zero] at h
  exact h

theorem tube_isOpen (hX : IsOpen X) : IsOpen (tube X) := by
  have hU : IsOpen {p : _root_.unitInterval × near n | hmap p ∈ X} := hX.preimage hmap_continuous
  have hV := isOpen_forall_unitInterval hU
  have he : tube X = Subtype.val '' {u : near n | ∀ s : _root_.unitInterval, hmap (s, u) ∈ X} := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u, hu.1⟩, fun s => hu.2 hu.1 s, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, fun _ s => hv s⟩
  rw [he]
  exact near_isOpen.isOpenMap_subtype_val _ hV

theorem rev_mem_tube (hX : ∀ u : SphereLoop n, u ∈ X → reverseSphere u ∈ X) {u : SphereLoop n}
    (hu : u ∈ tube X) : reverseSphere u ∈ tube X := by
  refine ⟨rev_mem_near hu.1, fun _ s => ?_⟩
  have h := hmap_rev s ⟨u, hu.1⟩
  have h' : hmap (s, ⟨reverseSphere u, rev_mem_near hu.1⟩) = reverseSphere (hmap (s, ⟨u, hu.1⟩)) :=
    h
  rw [h']
  exact hX _ (hu.2 hu.1 s)

theorem half_mem_tube (hX : ∀ u : SphereLoop n, u ∈ X → half +ᵥ u ∈ X) {u : SphereLoop n}
    (hu : u ∈ tube X) : half +ᵥ u ∈ tube X := by
  refine ⟨half_mem_near hu.1, fun _ s => ?_⟩
  have h' : hmap (s, ⟨half +ᵥ u, half_mem_near hu.1⟩) = half +ᵥ hmap (s, ⟨u, hu.1⟩) :=
    hmap_half s ⟨u, hu.1⟩
  rw [h']
  exact hX _ (hu.2 hu.1 s)

theorem fixed_mem_tube {u : SphereLoop n} (hu : u ∈ X) (hfix : half +ᵥ u = u) : u ∈ tube X := by
  refine ⟨fixed_mem_near hfix, fun h s => ?_⟩
  rw [hmap_fixed s ⟨u, h⟩ hfix]
  exact hu

theorem hmap_mem_tube (s : _root_.unitInterval) (x : tube X) :
    hmap (s, ⟨(x : SphereLoop n), x.2.1⟩) ∈ tube X := by
  refine ⟨hmap_mem_near s ⟨_, x.2.1⟩, fun _ s' => ?_⟩
  have h' : hmap (s', ⟨hmap (s, ⟨(x : SphereLoop n), x.2.1⟩), hmap_mem_near s ⟨_, x.2.1⟩⟩) =
      hmap (join s s', ⟨(x : SphereLoop n), x.2.1⟩) := hmap_hmap s s' ⟨_, x.2.1⟩
  rw [h']
  exact x.2.2 x.2.1 (join s s')

/-- The homotopy on the neighbourhood. -/
def tubeMap (X : Set (Loops n)) (p : _root_.unitInterval × tube X) : tube X :=
  ⟨hmap (p.1, ⟨(p.2 : SphereLoop n), p.2.2.1⟩), hmap_mem_tube p.1 p.2⟩

theorem tubeMap_continuous : Continuous (tubeMap X) := by
  have h : Continuous fun p : _root_.unitInterval × tube X =>
      ((p.1, ⟨(p.2 : SphereLoop n), p.2.2.1⟩) : _root_.unitInterval × near n) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  exact (hmap_continuous.comp h).subtype_mk _

/-- The end of the homotopy on the neighbourhood. -/
def tubeEnd (X : Set (Loops n)) : C(tube X, tube X) :=
  ⟨fun x => tubeMap X (1, x), tubeMap_continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- The homotopy on the neighbourhood, from the identity. -/
def tubeHomotopy (X : Set (Loops n)) : (ContinuousMap.id (tube X)).Homotopy (tubeEnd X) where
  toFun := tubeMap X
  continuous_toFun := tubeMap_continuous
  map_zero_left x := Subtype.ext (hmap_zero ⟨(x : SphereLoop n), x.2.1⟩)
  map_one_left _ := rfl

variable {T : Set (Loops n)} (hT : ∀ u : SphereLoop n, u ∈ T ↔ u ∈ X ∧ half +ᵥ u = u)

include hT in
theorem fixed_subset_tube : T ⊆ tube X := fun u hu =>
  fixed_mem_tube ((hT u).mp hu).1 ((hT u).mp hu).2

/-- The neighbourhood deforms onto the fixed loops of X, keeping them fixed. -/
def tubeDeformation : PairDeformation T T T (tube X) where
  r := tubeEnd X
  H := tubeHomotopy X
  r_mem x := (hT _).mpr ⟨tube_subset (tubeMap X (1, x)).2, half_hmap_one ⟨_, x.2.1⟩⟩
  r_sub x _ := (hT _).mpr ⟨tube_subset (tubeMap X (1, x)).2, half_hmap_one ⟨_, x.2.1⟩⟩
  keep_sub' τ x hx := by
    have h : (tubeHomotopy X (τ, x) : Loops n) = (x : Loops n) :=
      hmap_fixed τ ⟨_, x.2.1⟩ ((hT _).mp hx).2
    rw [h]
    exact hx
  keep τ x hx := by
    have h : (tubeHomotopy X (τ, x) : Loops n) = (x : Loops n) :=
      hmap_fixed τ ⟨_, x.2.1⟩ ((hT _).mp hx).2
    rw [h]
    exact hx
  keep_sub τ x hx := by
    have h : (tubeHomotopy X (τ, x) : Loops n) = (x : Loops n) :=
      hmap_fixed τ ⟨_, x.2.1⟩ ((hT _).mp hx).2
    rw [h]
    exact hx

/-- The inclusion of the fixed loops of X into the neighbourhood is an isomorphism on relative
cohomology of the pairs with the fixed loops. -/
theorem bijective_nativePull_tube (q : ℕ) :
    Function.Bijective (nativePull (inclPair (subset_rfl : T ⊆ T) (fixed_subset_tube hT)
      subset_rfl (fixed_subset_tube hT)) q) :=
  bijective_nativePull_inclPair (subset_rfl : T ⊆ T) (fixed_subset_tube hT) subset_rfl
    (fixed_subset_tube hT) (tubeDeformation hT) q

end

end Finsler.HalfRetract
