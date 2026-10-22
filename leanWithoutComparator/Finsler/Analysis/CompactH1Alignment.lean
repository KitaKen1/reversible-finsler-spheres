module

public import Finsler.Analysis.H1BasepointAlignment
public import Finsler.Analysis.IntervalH1EnergyContinuity

/-! Choose the compact-family length bound before the basepoint correction radius.
In particular, an already chosen finite singular chain and filling can be
bounded through its compact parameter spaces, without using the rotation radius. -/

@[expose] public section

namespace Finsler.CompactH1Alignment

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevLength Finsler.H1OrthogonalLength Finsler.H1BasepointAlignment
open Finsler.NearbyRotor Set

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def basepoint (u : SphereLoop n) : Ambient n :=
  continuousRepresentative (u.data : Space n) 0

def align (u : SphereLoop n) (y : Sphere n) : SphereLoop n :=
  rotateLoop (rotor (basepoint u) (y : Ambient n)) u

theorem exists_length_bound (F : ReversibleMetric n) {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (u : X → SphereLoop n) (hu : ContinuousOn u K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, length F (u x) ≤ M := by
  have hE := (Finsler.SobolevEnergy.energy_continuous F).comp_continuousOn hu
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hE
  refine ⟨1 + |C|, by positivity, fun x hx => ?_⟩
  have he : Finsler.SobolevEnergy.energy F (u x) ≤ C :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hC x hx)
  have hl := length_sq_le_energy F (u x)
  have hnonneg := length_nonneg F (u x)
  have hc := le_abs_self C
  have ha := abs_nonneg C
  nlinarith [sq_nonneg |C|]

/-- The bound M is obtained independently, before the common alignment radius ρ. -/
theorem exists_family_alignment (F : ReversibleMetric n) {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (u : X → SphereLoop n) (hu : ContinuousOn u K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x ∈ K, length F (u x) ≤ M) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y : Sphere n,
        dist (y : Ambient n) (basepoint (u x)) < ρ →
        basepoint (align (u x) y) = (y : Ambient n) ∧
          |length F (align (u x) y) - length F (u x)| < ε := by
  obtain ⟨M, hM, hb⟩ := exists_length_bound F hK u hu
  obtain ⟨ρ, hρ, hd⟩ := exists_alignment F M hM hε
  refine ⟨M, hM, hb, ρ, hρ, fun x hx y hy => ?_⟩
  simpa only [basepoint, align] using
    hd _ _ ((u x).sphere_constraint ⟨0, by norm_num⟩)
      (by simpa using y.property) hy (u x) rfl (hb x hx)


end
end Finsler.CompactH1Alignment
