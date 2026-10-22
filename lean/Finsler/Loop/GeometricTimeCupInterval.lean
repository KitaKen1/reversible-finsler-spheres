module

public import Finsler.Loop.NormalizedCutScalarPullback
public import Finsler.Loop.RightIntervalCochain

/-! Exact interval expression for the EXISTING geometric time cup after
an arbitrary actual loop-valued map. All original cut and degree casts
remain, including the time-first parameter coordinate. -/
@[expose] public section
namespace Finsler.GeometricTimeCupInterval
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem integrate_pullback {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⊗ TopCat.I ⟶ Z) (N : ℕ)
    (T : singularCochainGroup (ZMod 2) Z (N + 1)) :
    cochainPullback f N (TimeTriangleSplit.interval Y N ≫ cochainPullback g (N + 1) T) =
      TimeTriangleSplit.interval X N ≫ cochainPullback ((f ▷ TopCat.I) ≫ g) (N + 1) T := by
  rw [pullback_comp]
  change (push f).f N ≫ (TimeTriangleSplit.interval Y N ≫ cochainPullback g (N + 1) T) = _
  rw [← Category.assoc, RightIntervalCochain.naturality, Category.assoc]
  rfl

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (p q : ℕ)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
  (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)

theorem pullback_interval {X : TopCat.{0}} (f : X ⟶ Loops (m + 1)) :
    cochainPullback f ((m + p) + q) (GeometricTimeCupCochain.cochain m p hρ hρr hr T q B) =
      TimeTriangleSplit.interval X ((m + p) + q) ≫
        CochainDegreeTransport.pre (X ⊗ TopCat.I) (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)
          (NormalizedCutScalarPullback.originalValue m ((f ▷ TopCat.I) ≫ (SelfCutTimePrism.cylinder (m + 1)).h)
            hρ hρr hr p q T B) := by
  unfold NormalizedCutScalarPullback.originalValue
  rw [NormalizedCutScalarPullback.pre_pullback]
  have h := integrate_pullback f (SelfCutTimePrism.cylinder (m + 1)).h ((m + p) + q)
    (CochainDegreeTransport.pre (SelfCutThomCocycle.parameters (m + 1))
      (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)
      ((NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + q) ≫
        GeometricTimeCupCochain.splitCup m p hr T q B))
  simp only [GeometricTimeCupCochain.cochain, TimeShuffleComparison.rectangle,
    TimeTriangleSplit.interval, CochainDegreeTransport.pre, Category.assoc] at h ⊢
  exact h

end
end Finsler.GeometricTimeCupInterval
