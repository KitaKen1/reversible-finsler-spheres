module

public import Finsler.Topology.Shortening
public import Finsler.Geometry.PolygonModel
public import Finsler.Topology.BorelK

/-! The curve shortening map of a polygon model. For a polygon model of the sublevel {E < a²}
with N vertices, straightening replaces a loop by the broken geodesic through its samples at
the grid k/N; the same operation on the grid shifted by 1/(2N) is the conjugate by the rotation
by 1/(2N). Both are joined to the identity by energy-nonincreasing homotopies and commute with
reversal (the grids shifted by ±1/(2N) coincide, and straightening commutes with the rotation by
1/N). Their composite D, first the grid and then the staggered grid, is therefore a shortening
of the sublevel t_a for every a > 0: a map commuting with reversal with an
energy-nonincreasing homotopy from the identity. This is Birkhoff's curve shortening process
for the polygon model; no flow is used. That D decreases energy strictly away from closed
geodesics, and the descent and localization properties which follow, are not proved here. -/

@[expose] public section

namespace Finsler.Birkhoff

open Set Topology
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevReverse Finsler.SobolevReflectionAction
open Finsler.SobolevShiftEnergy Finsler.PolygonModel
open Finsler.BorelK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The circle of parameters. -/
local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

variable {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
  (M : PolygonModelData F a N)

/-- Straightening on the grid shifted by 1/(2N), at time τ. -/
def stag (τ : ℝ) (u : SphereLoop n) : SphereLoop n :=
  (((-(1 / (2 * N)) : ℝ)) : Circ) +ᵥ deform M (τ, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)

theorem energy_stag_le {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {u : SphereLoop n}
    (hu : energy F u < a ^ 2) : energy F (stag M τ u) ≤ energy F u := by
  have hu' : energy F ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u) < a ^ 2 := by
    rw [energy_vadd]
    exact hu
  have h : energy F (deform M (τ, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)) ≤
      energy F ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u) :=
    energy_deform_le M (p := (τ, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)) ⟨hτ, hu'⟩
  rw [energy_vadd] at h
  unfold stag
  rw [energy_vadd]
  exact h

theorem stag_zero {u : SphereLoop n} (hu : energy F u < a ^ 2) : stag M 0 u = u := by
  have hu' : energy F ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u) < a ^ 2 := by
    rw [energy_vadd]
    exact hu
  unfold stag
  rw [deform_zero M hu', vadd_vadd, ← AddCircle.coe_add, neg_add_cancel, AddCircle.coe_zero,
    zero_vadd]

/-- Straightening on the staggered grid commutes with reversal. -/
theorem stag_reverse (τ : ℝ) (u : SphereLoop n) :
    stag M τ (reverseSphere u) = reverseSphere (stag M τ u) := by
  have hx : (1 / (2 * (N : ℝ))) = 1 / (N : ℝ) / 2 := by
    rw [div_div, mul_comm]
  have hreal : (1 / (N : ℝ) + -(1 / (2 * (N : ℝ)))) = 1 / (2 * (N : ℝ)) := by
    rw [hx]
    ring
  have hreal2 : (-(1 / (2 * (N : ℝ))) + 1 / (N : ℝ)) = -(-(1 / (2 * (N : ℝ)))) := by
    rw [hx]
    ring
  have key : ∀ w : SphereLoop n, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ w =
      (((1 / N : ℝ)) : Circ) +ᵥ ((((-(1 / (2 * N)) : ℝ)) : Circ) +ᵥ w) := by
    intro w
    rw [vadd_vadd, ← AddCircle.coe_add, hreal]
  have hsum : (((-(1 / (2 * N)) : ℝ)) : Circ) + (((1 / N : ℝ)) : Circ) =
      (((-(-(1 / (2 * N))) : ℝ)) : Circ) := by
    rw [← AddCircle.coe_add, hreal2]
  have hrev : ∀ (σ : ℝ) (v : SphereLoop n),
      deform M (σ, reverseSphere v) = reverseSphere (deform M (σ, v)) :=
    fun σ v => deform_reverse M (σ, v)
  have hrot : ∀ (σ : ℝ) (v : SphereLoop n),
      deform M (σ, (((1 / N : ℝ)) : Circ) +ᵥ v) =
        (((1 / N : ℝ)) : Circ) +ᵥ deform M (σ, v) :=
    fun σ v => deform_rotate M (σ, v)
  unfold stag
  rw [reverse_vadd, ← hrev, reverse_vadd, key (reverseSphere u), hrot, vadd_vadd, hsum]

theorem stag_continuousOn :
    ContinuousOn (fun p : ℝ × SphereLoop n => stag M p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}) := by
  have hact := Finsler.SobolevRotation.sphere_action_continuous n
  have hc1 : Continuous fun p : ℝ × SphereLoop n =>
      ((((1 / (2 * N) : ℝ)) : Circ), p.2) :=
    continuous_const.prodMk continuous_snd
  have hv1 := hact.comp hc1
  have h1 : Continuous fun p : ℝ × SphereLoop n =>
      (p.1, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ p.2) :=
    continuous_fst.prodMk hv1
  have h2 : MapsTo (fun p : ℝ × SphereLoop n =>
      (p.1, (((1 / (2 * N) : ℝ)) : Circ) +ᵥ p.2))
      (Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2})
      (Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | energy F u < a ^ 2}) := by
    rintro ⟨τ, u⟩ ⟨hτ, hu⟩
    refine ⟨hτ, ?_⟩
    change energy F ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u) < a ^ 2
    rw [energy_vadd]
    exact hu
  have hc3 : Continuous fun v : SphereLoop n =>
      ((((-(1 / (2 * N)) : ℝ)) : Circ), v) :=
    continuous_const.prodMk continuous_id
  have h3 := hact.comp hc3
  have h4 := (deform_continuousOn M).comp h1.continuousOn h2
  have h5 := h3.comp_continuousOn h4
  exact h5

/-- For a positive level, t_a is the set of loops of energy below a². -/
theorem mem_lev_iff (ha : 0 < a) (u : SphereLoop n) : u ∈ lev F a ↔ energy F u < a ^ 2 := by
  constructor
  · rintro (hu | ⟨x, rfl⟩)
    · exact (Real.sqrt_lt' ha).mp hu
    · rw [energy_constantSphereLoop]
      exact pow_pos ha 2
  · intro hu
    exact Or.inl ((Real.sqrt_lt' ha).mpr hu)

section Maps

variable (ha : 0 < a)

/-- The straightening homotopy on t_a, from the identity to the first straightening. -/
def g1Fun (p : _root_.unitInterval × lev F a) : lev F a :=
  ⟨deform M ((p.1 : ℝ), (p.2 : SphereLoop n)),
    (mem_lev_iff ha _).mpr (deform_sublevel M (p := ((p.1 : ℝ), (p.2 : SphereLoop n)))
      ⟨p.1.2, (mem_lev_iff ha _).mp p.2.2⟩ ((mem_lev_iff ha _).mp p.2.2))⟩

theorem g1Fun_continuous : Continuous (g1Fun M ha) := by
  have hf : Continuous fun p : _root_.unitInterval × lev F a =>
      ((p.1 : ℝ), (p.2 : SphereLoop n)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h := (deform_continuousOn M).comp_continuous hf
    (fun p => ⟨p.1.2, (mem_lev_iff ha _).mp p.2.2⟩)
  exact h.subtype_mk _

/-- The straightening homotopy on the staggered grid, on t_a. -/
def g2Fun (p : _root_.unitInterval × lev F a) : lev F a :=
  ⟨stag M (p.1 : ℝ) (p.2 : SphereLoop n),
    (mem_lev_iff ha _).mpr ((energy_stag_le M p.1.2 ((mem_lev_iff ha _).mp p.2.2)).trans_lt
      ((mem_lev_iff ha _).mp p.2.2))⟩

theorem g2Fun_continuous : Continuous (g2Fun M ha) := by
  have hf : Continuous fun p : _root_.unitInterval × lev F a =>
      ((p.1 : ℝ), (p.2 : SphereLoop n)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h := (stag_continuousOn M).comp_continuous hf
    (fun p => ⟨p.1.2, (mem_lev_iff ha _).mp p.2.2⟩)
  exact h.subtype_mk _

/-- Straightening on the grid, as a map of t_a. -/
def d1 : C(lev F a, lev F a) :=
  ⟨fun x => g1Fun M ha (1, x),
    (g1Fun_continuous M ha).comp (continuous_const.prodMk continuous_id)⟩

/-- Straightening on the staggered grid, as a map of t_a. -/
def d2 : C(lev F a, lev F a) :=
  ⟨fun x => g2Fun M ha (1, x),
    (g2Fun_continuous M ha).comp (continuous_const.prodMk continuous_id)⟩

/-- The homotopy from the identity to the straightening on the grid. -/
def g1 : (ContinuousMap.id (lev F a)).Homotopy (d1 M ha) where
  toFun := g1Fun M ha
  continuous_toFun := g1Fun_continuous M ha
  map_zero_left x := Subtype.ext (deform_zero M ((mem_lev_iff ha _).mp x.2))
  map_one_left _ := rfl

/-- The homotopy from the identity to the straightening on the staggered grid. -/
def g2 : (ContinuousMap.id (lev F a)).Homotopy (d2 M ha) where
  toFun := g2Fun M ha
  continuous_toFun := g2Fun_continuous M ha
  map_zero_left x := Subtype.ext (stag_zero M ((mem_lev_iff ha _).mp x.2))
  map_one_left _ := rfl

/-- The homotopy from the first straightening to the composite of the two. -/
def g21 : (d1 M ha).Homotopy ((d2 M ha).comp (d1 M ha)) where
  toFun p := g2 M ha (p.1, d1 M ha p.2)
  continuous_toFun := (g2 M ha).continuous.comp
    (continuous_fst.prodMk ((d1 M ha).continuous.comp continuous_snd))
  map_zero_left x := (g2 M ha).apply_zero (d1 M ha x)
  map_one_left x := (g2 M ha).apply_one (d1 M ha x)

theorem energy_g1_le (τ : _root_.unitInterval) (x : lev F a) :
    energy F (g1 M ha (τ, x) : SphereLoop n) ≤ energy F (x : SphereLoop n) :=
  energy_deform_le M (p := ((τ : ℝ), (x : SphereLoop n))) ⟨τ.2, (mem_lev_iff ha _).mp x.2⟩

theorem energy_g2_le (τ : _root_.unitInterval) (x : lev F a) :
    energy F (g2 M ha (τ, x) : SphereLoop n) ≤ energy F (x : SphereLoop n) :=
  energy_stag_le M τ.2 ((mem_lev_iff ha _).mp x.2)

theorem energy_d1_le (x : lev F a) :
    energy F (d1 M ha x : SphereLoop n) ≤ energy F (x : SphereLoop n) :=
  energy_g1_le M ha 1 x

/-- The curve shortening map of the polygon model as a shortening of t_a. -/
def shortening : Shortening.Data F a where
  D := (d2 M ha).comp (d1 M ha)
  G := (g1 M ha).trans (g21 M ha)
  energy_le τ x := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · exact energy_g1_le M ha _ x
    · exact (energy_g2_le M ha _ (d1 M ha x)).trans (energy_d1_le M ha x)
  rev x := by
    have h := deform_reverse M ((1 : ℝ), (x : SphereLoop n))
    change stag M 1 (deform M (1, reverseSphere (x : SphereLoop n))) =
      reverseSphere (stag M 1 (deform M (1, (x : SphereLoop n))))
    rw [show deform M (1, reverseSphere (x : SphereLoop n)) =
      reverseSphere (deform M (1, (x : SphereLoop n))) from h, stag_reverse]

end Maps

/-- Every positive sublevel carries a shortening. -/
theorem exists_shortening (F : ReversibleMetric n) {a : ℝ} (ha : 0 < a) :
    Nonempty (Shortening.Data F a) := by
  obtain ⟨N₀, hN₀⟩ := exists_polygonModelData F a
  obtain ⟨M⟩ := hN₀ (N₀ + 1) (Nat.le_succ N₀) (Nat.succ_pos N₀)
  exact ⟨shortening M ha⟩

end

end Finsler.Birkhoff
