module

public import Finsler.Loop.OriginalFirstHalfJoinTimeCover

/-! The actual first spatial join cap lifted directly into the real
zero-cylinder small-chain complex on every nonzero whole parent. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfLocalizedJoinCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJoinTimeCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η ρ : ℝ)
  {κ : ℝ} (hκ : 0 < κ)

theorem parent_image (q : ℕ)
    (τ : ((ambient α β).smallSingularSubcomplex (cover α β R r η ρ κ) : SSet) _⦋(m + 1) + q⦌)
    (hτ : (TopCat.toSSet.obj (ambient α β)).ιChainComplex τ.val ≫
      absoluteChain (ambient α β) (m + 1) q ((m + 1) + q) rfl (join α β hκ) ≠ 0) :
    ∃ i, Set.range ((ambient α β).toSSetObjEquiv _ τ.val) ⊆
      nearSource α β R '' OriginalFirstHalfZeroCover.cover α β R r η ρ i := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β)
    (cover α β R r η ρ κ) τ.val).mp τ.property
  cases i with
  | none =>
      have hf : Set.range ((ambient α β).toSSetObjEquiv _ τ.val) ⊆ joinFar α β κ := by
        intro z hz
        exact (show κ < OriginalFirstHalfJointCover.pairGap α β z from hi hz).le
      exact (hτ (SupportedCap.cap_zero_on_simplex _ _ (m + 1) q ((m + 1) + q) rfl
        (join α β hκ) (join_far_zero α β hκ) τ.val hf)).elim
  | some i => exact ⟨i, fun z hz => near_image α β R r η ρ κ i (hi hz)⟩

def operation : DegreeLoweringHomology.Map
    (small (ambient α β) (cover α β R r η ρ κ))
    (small (OriginalFirstHalfZeroCover.space α β R) (OriginalFirstHalfZeroCover.cover α β R r η ρ)) (m + 1) :=
  SmallCapSubspaceLift.operation (ambient α β) (OriginalFirstHalfZeroCover.space α β R)
    (pairDomain α β R) (pairIso α β R) (cover α β R r η ρ κ)
    (OriginalFirstHalfZeroCover.cover α β R r η ρ) (m + 1) (join α β hκ)
    (fun q τ hτ => by
      rw [source_eq]
      exact parent_image α β R r η ρ hκ q τ hτ)
    (join_closed α β hκ)

theorem component_source (q : ℕ) :
    (operation α β R r η ρ hκ).component q ≫
      (inclusion (OriginalFirstHalfZeroCover.space α β R) (OriginalFirstHalfZeroCover.cover α β R r η ρ)).f q ≫
        (push (nearSource α β R)).f q =
    (inclusion (ambient α β) (cover α β R r η ρ κ)).f ((m + 1) + q) ≫
      absoluteChain (ambient α β) (m + 1) q ((m + 1) + q) rfl (join α β hκ) := by
  have hc := SmallCapSubspaceLift.component_inclusion (ambient α β) (OriginalFirstHalfZeroCover.space α β R)
    (pairDomain α β R) (pairIso α β R) (cover α β R r η ρ κ)
    (OriginalFirstHalfZeroCover.cover α β R r η ρ) (m + 1) (join α β hκ)
    (fun q τ hτ => by rw [source_eq]; exact parent_image α β R r η ρ hκ q τ hτ) q
  simpa only [operation, SmallCapSubspaceLift.operation, SmallCapSubspaceLift.target,
    HomologicalComplex.comp_f, source_eq, Category.assoc] using hc

end
end Finsler.OriginalFirstHalfLocalizedJoinCap
