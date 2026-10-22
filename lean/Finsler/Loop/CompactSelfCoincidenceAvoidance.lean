module

public import Finsler.Topology.NormalizedSelfCut
public import Mathlib.Topology.Order.Compact

/-! A compact family of genuinely unequal sphere pairs has ONE
positive far radius. Consequently the ORIGINAL normalized self-cut
Thom cochain pulls back to literal zero on that entire compact patch,
for every smaller positive support radius. -/
@[expose] public section
namespace Finsler.CompactSelfCoincidenceAvoidance
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem exists_radius {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f g : C(X, Sphere n)) (K : Set X) (hK : IsCompact K)
    (hne : ∀ x ∈ K, f x ≠ g x) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, R ≤ ‖(g x : Ambient n) - (f x : Ambient n)‖ := by
  let d : X → ℝ := fun x => ‖(g x : Ambient n) - (f x : Ambient n)‖
  have hd : Continuous d :=
    ((continuous_subtype_val.comp g.continuous).sub (continuous_subtype_val.comp f.continuous)).norm
  by_cases h : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMinOn h hd.continuousOn
    refine ⟨d x, ?_, fun y hy => hm hy⟩
    apply norm_pos_iff.mpr
    intro hz
    exact hne x hx (Subtype.ext (sub_eq_zero.mp hz).symm)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (h ⟨x, hx⟩).elim

theorem normalized_far_zero {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}}
    (f : X ⟶ DiagonalCohomology.product n) (K : Set X) (hK : IsCompact K)
    (hne : ∀ x ∈ K, (f x).1 ≠ (f x).2) :
    ∃ R : ℝ, 0 < R ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ R →
      cochainPullback (SupportedCap.subspaceMap X K ≫ f) n (NormalizedDiagonalCocycle.ambient n hn hρ) = 0 := by
  let a : C(X, Sphere n) := ⟨fun x => (f x).1, continuous_fst.comp f.hom.continuous⟩
  let b : C(X, Sphere n) := ⟨fun x => (f x).2, continuous_snd.comp f.hom.continuous⟩
  obtain ⟨R, hR, hfar⟩ := exists_radius a b K hK hne
  refine ⟨R, hR, fun ρ hρ hρR => ?_⟩
  apply NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ
  intro x
  exact hρR.trans (hfar x.val x.property)

theorem original_thom_zero {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}}
    (α : X ⟶ SelfCutThomCocycle.parameters n) (K : Set X) (hK : IsCompact K)
    (hne : ∀ x ∈ K, (SelfCutThomCocycle.selfEvaluation n (α x)).1 ≠
      (SelfCutThomCocycle.selfEvaluation n (α x)).2) :
    ∃ R : ℝ, 0 < R ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ R →
      cochainPullback (SupportedCap.subspaceMap X K ≫ α) n (NormalizedSelfCut.cocycle n hn hρ) = 0 := by
  obtain ⟨R, hR, hzero⟩ := normalized_far_zero hn (α ≫ SelfCutThomCocycle.selfEvaluation n) K hK hne
  refine ⟨R, hR, fun ρ hρ hρR => ?_⟩
  rw [NormalizedSelfCut.cocycle, ← pullback_comp, Category.assoc]
  exact hzero ρ hρ hρR

end
end Finsler.CompactSelfCoincidenceAvoidance
