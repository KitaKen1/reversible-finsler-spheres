module

public import Finsler.Analysis.IntervalH1Trace
public import Finsler.Geometry.FiberLegendre
public import Mathlib.Data.ZMod.Basic

/-! First pieces of the finite-cut polygon model. Continuous representatives of H¹ loops are
1/2-Hölder with constant the L² norm of the weak velocity, so consecutive samples at spacing
1/N are uniformly close. For closed polygons of geodesic segments, matching Legendre momenta
at the vertices and Legendre injectivity propagate one zero edge around the polygon, so a
nonconstant critical polygon has no zero edge. Short geodesic segments, the polygon space
and the homotopy equivalence with the energy sublevels remain separate obligations. -/

@[expose] public section

namespace Finsler.PolygonBasics

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Set
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Sampling bound: continuous representatives are 1/2-Hölder with constant the L² norm of
the weak velocity. -/
theorem representative_sub_le_sqrt (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖continuousRepresentative u t - continuousRepresentative u s‖ ≤
      Real.sqrt |t - s| * ‖velocity u‖ := by
  rw [continuousRepresentative_sub u hs ht]
  exact norm_valueLp_intervalIntegral_le_sqrt (velocity u) hs ht

/-- Consecutive samples at spacing 1/N are within √(1/N) times the velocity norm. -/
theorem sample_sub_le (u : Space n) {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i + 1 ≤ N) :
    ‖continuousRepresentative u ((i + 1 : ℕ) / N) - continuousRepresentative u (i / N)‖ ≤
      Real.sqrt (1 / N) * ‖velocity u‖ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (i / N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast (Nat.le_of_succ_le hi)
  have ht : ((i + 1 : ℕ) / N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hi
  have h := representative_sub_le_sqrt u hs ht
  have hdiff : |((i + 1 : ℕ) / N : ℝ) - i / N| = 1 / N := by
    rw [Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left, abs_of_pos (by positivity)]
  rwa [hdiff] at h

/-- Zero-edge exclusion for closed polygons of geodesic segments (abstract form): if at every
vertex the incoming and outgoing Legendre momenta agree on tangent vectors, and a segment with
zero outgoing velocity has zero incoming velocity at the next vertex, then one zero edge forces
all velocities to vanish. -/
theorem zero_edge_propagates (F : ReversibleMetric n) {N : ℕ} [NeZero N]
    (q vout vin : ZMod N → Ambient n) (hq : ∀ i, ‖q i‖ = 1)
    (hout : ∀ i, ⟪q i, vout i⟫ = 0) (hin : ∀ i, ⟪q i, vin i⟫ = 0)
    (hmatch : ∀ i k, ⟪q i, k⟫ = 0 →
      velocityDifferential F (q i, vin i) k = velocityDifferential F (q i, vout i) k)
    (hseg : ∀ i, vout i = 0 → vin (i + 1) = 0) {i₀ : ZMod N} (h0 : vout i₀ = 0) :
    ∀ i, vout i = 0 ∧ vin i = 0 := by
  have heq : ∀ i, vin i = vout i := fun i =>
    Finsler.FiberLegendre.tangent_eq_of_velocityDifferential_eq F (hq i) (hin i) (hout i)
      (hmatch i)
  have hstep : ∀ k : ℕ, vout (i₀ + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have h1 := hseg _ ih
      rw [heq] at h1
      simpa [Nat.cast_succ, add_assoc] using h1
  intro i
  have hi : i = i₀ + ((i - i₀).val : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    abel
  have hv : vout i = 0 := by
    rw [hi]
    exact hstep _
  exact ⟨hv, (heq i).trans hv⟩

end

end Finsler.PolygonBasics
