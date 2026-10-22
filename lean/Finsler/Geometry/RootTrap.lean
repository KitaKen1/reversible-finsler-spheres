module

public import Finsler.Geometry.LabelTransport
public import Finsler.Topology.OrbitTrap

/-! Trapping of whole orbits for a bounded field on the polygons with nonzero vertices. Let a
Lipschitz field V on polygons with N vertices be bounded by κ, supported away from polygons with
a zero vertex, and let D be its descent for a function g. If Z ⊆ Z₀ are sets of polygons such
that every polygon at distance at most κ from Z lies in Z₀, the orbits of the points of Z stay in
Z₀ up to the time one (a margin). Hence, on a compact band of g on which the time-one map
decreases g strictly outside Z ∪ R, with R open and disjoint from Z₀ and Z open, whole orbits
of points of Z₀ below b which are not taken below a in time T ≥ 1 stay in Z₀ up to the time T,
for all sufficiently tight cuts. This is the trapping on the root side, and with the margin of
v0.120 also on the ambient side. -/

@[expose] public section

namespace Finsler.RootTrap

open Set Filter Metric
open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.FlowLens Finsler.OrbitTrap Finsler.LabelTransport
open scoped Topology NNReal

noncomputable section

variable {n N : ℕ} [NeZero N] {V : (ZMod N → Ambient n) → ZMod N → Ambient n} {K : ℝ≥0}
  (hL : LipschitzWith K V) (hV0 : ∀ P : ZMod N → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod N → Ambient n) → ℝ} {O : Set (ZMod N → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)

/-- **The margin of a bounded flow.** -/
theorem flow_margin {κ : ℝ} (hκ : ∀ x, ‖V x‖ ≤ κ) {Z Z₀ : Set (ZMod N → Ambient n)}
    (hZ : ∀ z ∈ Z, ∀ z', ‖z' - z‖ ≤ κ → z' ∈ Z₀) (v : Om n N) (hv : v.1 ∈ Z) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : ((descentOf hL hV0 hg hsupp hle).flow s v).1 ∈ Z₀ := by
  change ODE.globalSolution V hL v.1 (max s 0) ∈ Z₀
  rw [max_eq_left hs]
  apply hZ v.1 hv
  have h1 := norm_globalSolution_sub_le hL hκ v.1 hs
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ v.1)
  calc ‖ODE.globalSolution V hL v.1 s - v.1‖ ≤ κ * s := h1
    _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hs1 hκ0
    _ = κ := mul_one κ

/-- **Trapping of whole orbits for a bounded flow.** -/
theorem exists_trap_bounded {κ : ℝ} (hκ : ∀ x, ‖V x‖ ≤ κ) {Z Z₀ : Set (ZMod N → Ambient n)}
    (hZopen : IsOpen {v : Om n N | v.1 ∈ Z}) (hZZ : Z ⊆ Z₀)
    (hZ : ∀ z ∈ Z, ∀ z', ‖z' - z‖ ≤ κ → z' ∈ Z₀) {R : Set (Om n N)} (hR : IsOpen R)
    (hdis : Disjoint {v : Om n N | v.1 ∈ Z₀} R) (hgc : Continuous fun v : Om n N => g v.1)
    {a₀ b₀ : ℝ} (hK : IsCompact {v : Om n N | a₀ ≤ g v.1 ∧ g v.1 ≤ b₀})
    (hstrict : ∀ v : Om n N, a₀ ≤ g v.1 → g v.1 ≤ b₀ → v ∉ {v : Om n N | v.1 ∈ Z} ∪ R →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 v).1 < g v.1) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b T : ℝ, a₀ ≤ a → b ≤ b₀ → b - a < d → 1 ≤ T →
      ∀ v ∈ {v : Om n N | v.1 ∈ Z₀}, g v.1 < b → a ≤ g ((descentOf hL hV0 hg hsupp hle).flow T v).1 →
        ∀ s, 0 ≤ s → s ≤ T → (descentOf hL hV0 hg hsupp hle).flow s v ∈ {v : Om n N | v.1 ∈ Z₀} :=
  exists_orbit_trap (descentOf hL hV0 hg hsupp hle) hgc hZopen hR (fun _ hv => hZZ hv) hdis hK
    hstrict (fun v hv s hs hs1 => flow_margin hL hV0 hg hsupp hle hκ hZ v hv s hs hs1)

end

end Finsler.RootTrap
