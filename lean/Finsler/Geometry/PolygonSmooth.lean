module

public import Finsler.Geometry.EnergySphereSmooth
public import Finsler.Geometry.PolygonCritical

/-! Smoothness of the polygon energy near polygons without zero edges. With normalized vertices the
polygon energy N Σ e(Q_k/‖Q_k‖, Q_{k+1}/‖Q_{k+1}‖) agrees with the polygon energy on sphere
polygons, and near a short polygon whose consecutive vertices are distinct each term is C³, since
the extended minimal energy is C³ at off-diagonal pairs; so the polygon energy is C³ there. -/

@[expose] public section

namespace Finsler.PolygonSmooth

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.SphereDistance (minEnergy)
open Set Filter
open scoped Topology ContDiff

noncomputable section

variable {n : ℕ}

/-- The polygon energy with normalized vertices. -/
def polyEnergyN (F : ReversibleMetric n) (N : ℕ) (Q : ZMod N → Ambient n) : ℝ :=
  N * ∑ k ∈ Finset.range N, ambientMinEnergy F (Q k, Q ((k : ZMod N) + 1))

theorem coe_normalize_of_norm {x : Ambient n} (hx : ‖x‖ = 1) : (normalize x : Ambient n) = x := by
  have h := normalize_inclusion (⟨x, mem_sphere_zero_iff_norm.mpr hx⟩ : Sphere n)
  exact congrArg Subtype.val h

/-- On unit vectors the normalized polygon energy is the polygon energy. -/
theorem polyEnergyN_eq (F : ReversibleMetric n) (N : ℕ) {Q : ZMod N → Ambient n}
    (hQ : ∀ i, ‖Q i‖ = 1) : polyEnergyN F N Q = polyEnergy F N Q := by
  unfold polyEnergyN polyEnergy ambientMinEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [coe_normalize_of_norm (hQ _), coe_normalize_of_norm (hQ _)]

/-- Near a short polygon without zero edges the polygon energy is C³. -/
theorem polyEnergyN_contDiffAt (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {N : ℕ} [NeZero N] {q : ZMod N → Sphere n} (hq : ShortPolygon δ q)
    (hne : ∀ i, q (i + 1) ≠ q i) :
    ContDiffAt ℝ 3 (polyEnergyN F N) (fun i => (q i : Ambient n)) := by
  unfold polyEnergyN
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro k _
  have hproj : ContDiffAt ℝ 3 (fun Q : ZMod N → Ambient n => (Q k, Q ((k : ZMod N) + 1)))
      (fun i => (q i : Ambient n)) :=
    ((contDiff_apply ℝ (Ambient n) (k : ZMod N)).prodMk
      (contDiff_apply ℝ (Ambient n) ((k : ZMod N) + 1))).contDiffAt
  exact ContDiffAt.comp (g := ambientMinEnergy F)
    (f := fun Q : ZMod N → Ambient n => (Q k, Q ((k : ZMod N) + 1)))
    (x := fun i => (q i : Ambient n)) (hδ _ _ (hne k) (hq k)) hproj

/-- Along a differentiable curve of sphere polygons through a short polygon without zero edges the
polygon energy is differentiable. -/
theorem polyEnergy_hasDerivAt_curve (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {N : ℕ} [NeZero N] {q : ZMod N → Sphere n} (hq : ShortPolygon δ q)
    (hne : ∀ i, q (i + 1) ≠ q i) {c : ℝ → ZMod N → Ambient n} {c' : ZMod N → Ambient n}
    (hc0 : c 0 = fun i => (q i : Ambient n)) (hcn : ∀ r i, ‖c r i‖ = 1) (hcd : HasDerivAt c c' 0) :
    HasDerivAt (fun r => polyEnergy F N (c r))
      (fderiv ℝ (polyEnergyN F N) (fun i => (q i : Ambient n)) c') 0 := by
  have hs := polyEnergyN_contDiffAt F hδ hq hne
  have hd : HasFDerivAt (polyEnergyN F N) (fderiv ℝ (polyEnergyN F N) (fun i => (q i : Ambient n)))
      (c 0) := by
    rw [hc0]
    exact (hs.differentiableAt (by simp)).hasFDerivAt
  have h := hd.comp_hasDerivAt 0 hcd
  have he : (fun r => polyEnergy F N (c r)) = polyEnergyN F N ∘ c := by
    funext r
    exact (polyEnergyN_eq F N (hcn r)).symm
  rw [he]
  exact h

end

end Finsler.PolygonSmooth
