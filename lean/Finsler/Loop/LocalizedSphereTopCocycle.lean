module

public import Finsler.Loop.CompactSelfCoincidenceAvoidance

/-! A representative of the EXISTING normalized sphere top class,
supported in any positive-radius neighborhood of a chosen point.
It is obtained from the ORIGINAL normalized diagonal cocycle by
the actual fixed-point fiber. Compact families avoiding that point
pull it back literally to zero at one common small radius. -/
@[expose] public section
namespace Finsler.LocalizedSphereTopCocycle
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.DiagonalCohomology Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

def cocycle (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (BorelEvaluation.sphere n) n :=
  cochainPullback (fiber n Q) n (NormalizedDiagonalCocycle.ambient n hn hρ)

theorem closed (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (BorelEvaluation.sphere n) n (cocycle n hn Q hρ) = 0 :=
  cochainPullback_cocycle (fiber n Q) n _ (NormalizedDiagonalCocycle.ambient_closed n hn hρ)

theorem top_class (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (cochainCxZMod2 (BorelEvaluation.sphere n)) n (cocycle n hn Q hρ)
      (closed n hn Q hρ) = SphereTopClass.topClass n hn := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (product n))
    (singularCochainComplexZMod2.map (fiber n Q).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)
    (closed n hn Q hρ)
  change (cohPullback (fiber n Q) n).hom
    (CochainClass.classOf (cochainCxZMod2 (product n)) n (NormalizedDiagonalCocycle.ambient n hn hρ)
      (NormalizedDiagonalCocycle.ambient_closed n hn hρ)) =
    CochainClass.classOf (cochainCxZMod2 (BorelEvaluation.sphere n)) n (cocycle n hn Q hρ) (closed n hn Q hρ) at he
  rw [NormalizedDiagonalCocycle.ambient_class, fiber_pullback] at he
  exact he.symm

theorem pullback_far_zero {n : ℕ} (hn : 1 ≤ n) (Q : Sphere n) {ρ : ℝ} (hρ : 0 < ρ)
    {X : TopCat.{0}} (f : X ⟶ BorelEvaluation.sphere n)
    (hf : ∀ x, ρ ≤ ‖(f x : Ambient n) - (Q : Ambient n)‖) :
    cochainPullback f n (cocycle n hn Q hρ) = 0 := by
  rw [cocycle, ← pullback_comp]
  exact NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ (f ≫ fiber n Q) hf

theorem compact_avoid_zero {n : ℕ} (hn : 1 ≤ n) (Q : Sphere n)
    {X : TopCat.{0}} (f : X ⟶ BorelEvaluation.sphere n) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x ∈ K, f x ≠ Q) :
    ∃ R : ℝ, 0 < R ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ R →
      cochainPullback (SupportedCap.subspaceMap X K ≫ f) n (cocycle n hn Q hρ) = 0 := by
  obtain ⟨R, hR, hzero⟩ := CompactSelfCoincidenceAvoidance.normalized_far_zero hn (f ≫ fiber n Q) K hK
    (fun x hx => (hf x hx).symm)
  refine ⟨R, hR, fun ρ hρ hρR => ?_⟩
  rw [cocycle, ← pullback_comp, Category.assoc]
  exact hzero ρ hρ hρR

theorem point_pullback_zero (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {ρ : ℝ} (hρ : 0 < ρ)
    (X : TopCat.{0}) :
    cochainPullback (TopCat.ofHom (ContinuousMap.const X Q)) n (cocycle n hn Q hρ) = 0 := by
  rw [cocycle, ← pullback_comp]
  exact NormalizedDiagonalCocycle.pullback_zero_of_diagonal hn hρ _ (fun _ => rfl)

end
end Finsler.LocalizedSphereTopCocycle
