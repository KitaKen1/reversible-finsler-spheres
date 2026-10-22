module

public import Finsler.Analysis.H1AlignmentHomotopy

/-! A common alignment radius for finitely many compact parameter spaces.
In particular, the parameters of a finite collection of singular simplices
may have different dimensions. The length bound is obtained before the radius. -/

@[expose] public section

namespace Finsler.FiniteFamilyAlignment

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy Finsler.SobolevLength
open Set

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_common_control (F : ReversibleMetric n) {ι : Type*} [Finite ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (u : ∀ i, X i → SphereLoop n) (hu : ∀ i, Continuous (u i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ i z, length F (u i z) ≤ M) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ i z, ∀ y : Sphere n,
        dist (y : Ambient n) (basepoint (u i z)) < ρ →
        ∀ s : _root_.unitInterval,
          |length F (hom s (u i z) y) - length F (u i z)| < ε := by
  let U : (Σ i, X i) → SphereLoop n := fun p => u p.1 p.2
  have hU : Continuous U := continuous_sigma_iff.mpr hu
  obtain ⟨M, hM, hb, ρ, hρ, hρ1, hd⟩ := exists_compact_control F
    (K := (univ : Set (Σ i, X i))) isCompact_univ U hU.continuousOn hε
  exact ⟨M, hM, (fun i z => hb ⟨i, z⟩ (mem_univ _)), ρ, hρ, hρ1,
    fun i z y hy => hd ⟨i, z⟩ (mem_univ _) y hy⟩


end
end Finsler.FiniteFamilyAlignment
