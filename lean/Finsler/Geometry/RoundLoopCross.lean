module

public import Finsler.Geometry.RoundLevel
public import Finsler.Topology.AmbientLoopPairs
public import Finsler.Topology.LoopCrossingOriented
public import Finsler.Geometry.PolygonEnergyGlobal
public import Finsler.Topology.BorelCrossing
public import Finsler.Topology.LevelBounds
public import Finsler.Geometry.RoundV2Finite

/-! The ordinary cohomology of the round crossings of the loop space.

For cuts 2π(m − 1) < a < 2πm < b < 2π(m + 1) of the length, the crossing pair (t_b, t_a) of the
loop space of the round sphere has, in every degree q, the cohomology of V₂ in degree
q − (2m − 1)(n − 1) (and none below), provided V₂ is finite dimensional in every degree. The
loop pair is the crossing pair of the penalized polygon energy for the cuts a², b² with an odd
number of vertices N = 2M + 1, m < M, large enough for a polygon model (`nonempty_loop_equiv`),
and that crossing is computed by `round_level`. -/

@[expose] public section

namespace Finsler.RoundLoopCross

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon
open Finsler.RoundChart Finsler.RoundThom Finsler.RoundLevel Finsler.AmbientPenalty
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonDescent Finsler.PolygonSampling
open Finsler.EnergyDiagonal Finsler.LoopCrossingOriented Finsler.AmbientLoopPairs
open Finsler.EnergySphereSmooth Finsler.LensFamily Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.BorelCrossing Module Set
open scoped Real

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The round crossings of the loop space.** -/
theorem round_loop_cross (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) {a b : ℝ}
    (hlo : 2 * π * ((m : ℝ) - 1) < a) (hac : a < 2 * π * m) (hcb : 2 * π * m < b)
    (hhi : b < 2 * π * ((m : ℝ) + 1))
    (hV2 : ∀ k, Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k))
    (hab : a ≤ b) (q : ℕ) :
    Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono (roundMetric n) hab))) q) ∧
      finrank (ZMod 2) (H (triv (pairOf (lev_mono (roundMetric n) hab))) q) =
        if (2 * m - 1) * (n - 1) ≤ q then
          finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)))
            (q - (2 * m - 1) * (n - 1)))
        else 0 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hπ : 0 < π := Real.pi_pos
  have hlo0 : 0 ≤ 2 * π * ((m : ℝ) - 1) := by
    have : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
    positivity
  have ha : 0 < a := lt_of_le_of_lt hlo0 hlo
  -- segment data, polygon models and short polygons
  obtain ⟨S₀⟩ := exists_segmentData (roundMetric n)
  obtain ⟨δ₁, hδ₁, hC1⟩ := exists_ambientMinEnergy_contDiffAt_one (roundMetric n)
  set S := shrink S₀ (δ' := min S₀.δ (min δ₁ 2)) (lt_min S₀.pos (lt_min hδ₁ two_pos))
    (min_le_left _ _) with hS
  have hSδ : S.δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hSδ2 : S.δ ≤ 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing (roundMetric n) (δ := S.δ) (a := b) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound (roundMetric n) hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b ^ 2 / (e * S.δ ^ 2))
  set M := N₁ + N₂ + m + 1 with hM
  set N := 2 * M + 1 with hN
  haveI : NeZero N := ⟨by omega⟩
  have hNpos : 0 < N := by omega
  let MK : PolygonModelData (roundMetric n) b N :=
    PolygonModelData.mk S fun u hu s' t hs' ht hst => hN₁ N (by omega) hNpos u hu s' t hs' ht hst
  have hKR : b ^ 2 / (e * S.δ ^ 2) < N := hN₂.trans_le (Nat.cast_le.mpr (by omega))
  have hshortK : ∀ q : ZMod N → Sphere n, PolygonDescent.energy (roundMetric n) N q ≤ b ^ 2 →
      ShortPolygon MK.δ q := fun q hq => short_of_energy_le he S.pos hedge hKR q hq
  have hCK : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < MK.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy (roundMetric n)) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q h => hC1 P Q (h.trans_le hSδ)
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  -- the crossing of the polygon level
  have hpoly := round_level (N := N) hn (M := M) hN hm (by omega) hSδ2 hCK
    (a := a ^ 2) (b := b ^ 2) (by positivity) (pow_lt_pow_left₀ hlo hlo0 two_ne_zero)
    (pow_lt_pow_left₀ hac ha.le two_ne_zero)
    (pow_lt_pow_left₀ hcb (by positivity) two_ne_zero)
    (pow_lt_pow_left₀ hhi (ha.le.trans hab) two_ne_zero) hshortK hV2 hab2 q
  -- the loop pair
  obtain ⟨e₁⟩ := nonempty_loop_equiv MK zero_le_one (fun q hq => hshortK q hq.le) ha hab le_rfl q
  haveI := hpoly.1
  exact ⟨Module.Finite.equiv e₁.symm, e₁.finrank_eq.trans hpoly.2⟩

/-- The same for the involutive cochains of the crossing. -/
theorem round_cross (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) {a b : ℝ}
    (hlo : 2 * π * ((m : ℝ) - 1) < a) (hac : a < 2 * π * m) (hcb : 2 * π * m < b)
    (hhi : b < 2 * π * ((m : ℝ) + 1))
    (hV2 : ∀ k, Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) k))
    (hab : a ≤ b) (q : ℕ) :
    Module.Finite (ZMod 2) (H (crossComplex (roundMetric n) hab) q) ∧
      finrank (ZMod 2) (H (crossComplex (roundMetric n) hab) q) =
        if (2 * m - 1) * (n - 1) ≤ q then
          finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)))
            (q - (2 * m - 1) * (n - 1)))
        else 0 := by
  have h := round_loop_cross hn hm hlo hac hcb hhi hV2 hab q
  let e := Finsler.LevelBounds.ofPairEquiv (crossPair (roundMetric n) hab)
    (revCross_sq (roundMetric n) hab) (Category.comp_id _) q
  haveI := h.1
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h.2⟩

/-- **The ordinary cohomology of the round crossings** (unconditional). -/
theorem round_cross_dims (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) {a b : ℝ}
    (hlo : 2 * π * ((m : ℝ) - 1) < a) (hac : a < 2 * π * m) (hcb : 2 * π * m < b)
    (hhi : b < 2 * π * ((m : ℝ) + 1)) (hab : a ≤ b) (q : ℕ) :
    Module.Finite (ZMod 2) (H (crossComplex (roundMetric n) hab) q) ∧
      finrank (ZMod 2) (H (crossComplex (roundMetric n) hab) q) =
        if (2 * m - 1) * (n - 1) ≤ q then
          finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)))
            (q - (2 * m - 1) * (n - 1)))
        else 0 :=
  round_cross hn hm hlo hac hcb hhi (fun k => Finsler.RoundV2Finite.V2_finite k) hab q

end

end Finsler.RoundLoopCross
