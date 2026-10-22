import ReversibleFinslerSpheres
import FCTargetDefinitions
import Finsler.Geometry.RoundMetric
import Lean.Util.CollectAxioms

/-!
# The independent FC definitions agree with the proof targets

The self-contained FC file is imported for its definitions. None of its four
placeholder theorems is used in the proofs below; the final transitive axiom audit
checks this explicitly. The metric conversion is an equivalence, and unbundled curves and variations have exactly the same underlying functions. The image-set equality below
uses the proved equivalence of stationarity and the coordinate Euler–Lagrange
equation. In particular it preserves the precise meaning of geometric distinctness
and primeness. The final audit rejects `sorryAx` and any additional axiom.
-/

namespace ReversibleFinslerSphereCorrespondence

open ReversibleFinslerSpheres
open scoped Manifold ContDiff

noncomputable section

/-- The independent metric record contains exactly the proof-side data. -/
def metricEquiv (n : ℕ) : ReversibleMetric n ≃ Finsler.Geometry.ReversibleMetric n where
  toFun F := ⟨F.value, F.continuous, F.smooth, F.zero, F.positive,
    F.homogeneous, F.reversible, F.strongConvex⟩
  invFun F := ⟨F.value, F.continuous, F.smooth, F.zero, F.positive,
    F.homogeneous, F.reversible, F.strongConvex⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unbundled energy is the proof project's actual integral energy. -/
theorem energy_eq {n : ℕ} (F : ReversibleMetric n) (γ : Finsler.Loops.SmoothLoop n) :
    energy F γ.curve = Finsler.LoopEnergy.energy (metricEquiv n F) γ := rfl

/-- Unbundled smooth periodic variations are precisely the proof-side variations.
No FC placeholder proof is used. -/
theorem stationary_iff {n : ℕ} (F : ReversibleMetric n) (γ : Finsler.Loops.SmoothLoop n) :
    (∀ V : ℝ × ℝ → Sphere n, ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ V →
      (∀ u, Function.Periodic (fun t => V (u, t)) 1) →
      (∀ t, V (0, t) = γ t) → HasDerivAt (fun u => energy F (fun t => V (u, t))) 0 0) ↔
      Finsler.Geodesics.Stationary (metricEquiv n F) γ := by
  constructor
  · intro h V hV
    apply h V.family V.smooth V.periodic
    intro t
    exact congrArg (fun δ : Finsler.Loops.SmoothLoop n => δ t) hV
  · intro h V hs hp hbase
    let W : Finsler.Geodesics.SmoothVariation n := ⟨V, hs, hp⟩
    apply h W
    exact Finsler.Loops.loop_ext hbase

theorem isRiemannian_iff {n : ℕ} (F : ReversibleMetric n) :
    IsRiemannian F ↔ ReversibleFinslerSphereFC.IsRiemannian (metricEquiv n F) := Iff.rfl

/-- The two specifications count exactly the same subsets of the same sphere. -/
theorem primeImages_eq {n : ℕ} (F : ReversibleMetric n) :
    PrimeClosedGeodesicImages F =
      ReversibleFinslerSphereFC.PrimeClosedGeodesicImages (metricEquiv n F) := by
  ext s
  constructor
  · rintro ⟨γ, hs, hperiod, hr, hp, he, hi⟩
    let δ : Finsler.Loops.SmoothLoop n := ⟨γ, hs, hperiod⟩
    have hregular : Finsler.Geodesics.Regular δ := hr
    exact ⟨δ, hregular,
      (Finsler.SphereCoordinateEuler.stationary_iff_coordinateEuler _ hregular).mp
        ((stationary_iff F δ).mp he), hp, hi⟩
  · rintro ⟨γ, hr, he, hp, hi⟩
    exact ⟨γ.curve, γ.smooth, γ.periodic, hr, hp,
      (stationary_iff F γ).mpr
        ((Finsler.SphereCoordinateEuler.stationary_iff_coordinateEuler _ hr).mpr he), hi⟩

/-- This holds in every dimension, so it covers all four FC dimension ranges. -/
theorem infinite_primeImages_iff {n : ℕ} (F : ReversibleMetric n) :
    (PrimeClosedGeodesicImages F).Infinite ↔
      (ReversibleFinslerSphereFC.PrimeClosedGeodesicImages (metricEquiv n F)).Infinite := by
  rw [primeImages_eq]

/-- Neither direction loses metrics when universally quantifying over them. -/
theorem finsler_assertion_iff (n : ℕ) :
    (∀ F : ReversibleMetric n, (PrimeClosedGeodesicImages F).Infinite) ↔
      (∀ F : Finsler.Geometry.ReversibleMetric n,
        (ReversibleFinslerSphereFC.PrimeClosedGeodesicImages F).Infinite) := by
  constructor
  · intro h F
    exact (infinite_primeImages_iff ((metricEquiv n).symm F)).mp (h _)
  · intro h F
    exact (infinite_primeImages_iff F).mpr (h _)

theorem riemannian_assertion_iff (n : ℕ) :
    (∀ F : ReversibleMetric n, IsRiemannian F → (PrimeClosedGeodesicImages F).Infinite) ↔
      (∀ F : Finsler.Geometry.ReversibleMetric n, ReversibleFinslerSphereFC.IsRiemannian F →
        (ReversibleFinslerSphereFC.PrimeClosedGeodesicImages F).Infinite) := by
  constructor
  · intro h F hF
    exact (infinite_primeImages_iff ((metricEquiv n).symm F)).mp
      (h _ ((isRiemannian_iff _).mpr hF))
  · intro h F hF
    exact (infinite_primeImages_iff F).mpr (h _ ((isRiemannian_iff F).mp hF))

open Finsler.SphereGeometry Finsler.Geometry
open scoped RealInnerProductSpace

/-- Nonvacuity: the independent Riemannian predicate admits the round metric. -/
theorem round_isRiemannian (n : ℕ) : IsRiemannian ((metricEquiv n).symm (roundMetric n)) := by
  intro x
  refine ⟨(innerₗ (Finsler.SphereGeometry.Ambient n)).compl₁₂ (ambientMap x).toLinearMap
    (ambientMap x).toLinearMap, ?_, ?_, ?_⟩
  · intro v w
    exact (real_inner_comm (ambientMap x v) (ambientMap x w)).symm
  · intro v hv
    change 0 < ⟪ambientMap x v, ambientMap x v⟫
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ambientMap_ne_zero x hv))
  · intro v
    change ‖ambientMap x v‖ ^ 2 = ⟪ambientMap x v, ambientMap x v⟫
    exact (real_inner_self_eq_norm_sq _).symm

end

run_cmd do
  let targets : List Lean.Name := [``energy_eq, ``stationary_iff,
    ``isRiemannian_iff, ``primeImages_eq,
    ``infinite_primeImages_iff, ``finsler_assertion_iff, ``riemannian_assertion_iff,
    ``round_isRiemannian]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {target}: {axiomName}"
    Lean.logInfo m!"PASS: {target}; axioms = {axioms}"

end ReversibleFinslerSphereCorrespondence
