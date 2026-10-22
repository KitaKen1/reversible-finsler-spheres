module

public import Finsler.Geometry.RootField
public import Finsler.Geometry.RotationNatural
public import Finsler.Geometry.PolygonDescentK
public import Finsler.Analysis.EquivariantFieldAverage

/-! Equivariant root fields obtained by averaging the existing compactly supported descent fields. -/

@[expose] public section

namespace Finsler.RootFieldRotation

open Set Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientSymmetry Finsler.AmbientPenalty
open Finsler.AmbientDescent Finsler.LevelField Finsler.PolygonDescentK Finsler.RotationNatural
open Finsler.EquivariantApprox Finsler.EquivariantFieldAverage
open scoped ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n N : ℕ} [NeZero N]

/-- The regular set of the actual penalized energy is preserved by every vertex rotation. -/
theorem regSet_rotA (F : ReversibleMetric n) (lam : ℝ) (a : ZMod N)
    {Q : ZMod N → Ambient n} (hQ : Q ∈ regSet F N lam) :
    rotA N a Q ∈ regSet F N lam := by
  refine ⟨rotA_ne_zero N a hQ.1, ?_⟩
  have he : pen F N lam = pen F N lam ∘ rotA N (-a) :=
    funext fun P => (pen_rotA N F lam (-a) P).symm
  change ContDiffAt ℝ 1 (pen F N lam) (rotA N a Q)
  rw [he]
  refine ContDiffAt.comp (rotA N a Q) ?_ (rotA N (-a)).contDiff.contDiffAt
  rw [rotA_rotA, neg_add_cancel, rotA_zero]
  exact hQ.2

/-- The half-turn average of any existing root field keeps its smoothness, compact support,
support in the regular set, bound, nonpositive descent and every original strict descent point. -/
theorem average_root_field (F : ReversibleMetric n) (lam : ℝ) (a : ZMod N) (ha : a + a = 0)
    {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {κ : ℝ}
    (hVs : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVt : tsupport V ⊆ regSet F N lam) (hVb : ∀ x, ‖V x‖ ≤ κ)
    (hVle : ∀ x ∈ regSet F N lam, fderiv ℝ (pen F N lam) x (V x) ≤ 0) :
    let W := average (rotA N a) (rotA N a) V
    ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ regSet F N lam ∧
      (∀ x, ‖W x‖ ≤ κ) ∧
      (∀ x ∈ regSet F N lam, fderiv ℝ (pen F N lam) x (W x) ≤ 0) ∧
      (∀ x, W (rotA N a x) = rotA N a (W x)) ∧
      ∀ x, fderiv ℝ (pen F N lam) x (V x) < 0 →
        fderiv ℝ (pen F N lam) x (W x) < 0 := by
  let τ := rotA (n := n) N a
  have hτ : ∀ x, τ (τ x) = x := rotA_involutive ha
  have hinv : ∀ x, pen F N lam (τ x) = pen F N lam x := pen_rotA N F lam a
  have hreg : ∀ x ∈ regSet F N lam, τ x ∈ regSet F N lam :=
    fun _ hx => regSet_rotA F lam a hx
  refine ⟨average_contDiff τ τ hVs, average_hasCompactSupport τ hτ hVc,
    average_tsupport_subset τ hτ hVt hreg,
    average_norm_le τ (fun x => norm_rotA_le N a x) V hVb, ?_,
    average_equivariant τ τ hτ hτ V, ?_⟩
  · intro x hx
    apply average_nonpos τ hτ hinv V
      ((hreg x hx).2.differentiableAt one_ne_zero) (hVle x hx) (hVle _ (hreg x hx))
  · intro x hx
    have hVx : V x ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hx
      exact (lt_irrefl 0) hx
    have hxreg := hVt (subset_tsupport V hVx)
    exact average_strict τ hτ hinv V ((hreg x hxreg).2.differentiableAt one_ne_zero)
      hx (hVle _ (hreg x hxreg))

end

end Finsler.RootFieldRotation
