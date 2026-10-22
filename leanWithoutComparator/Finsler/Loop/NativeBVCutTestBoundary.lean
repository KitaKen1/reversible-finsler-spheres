module

public import Finsler.Loop.NativeBVThomBoundary

/-! An arbitrary primitive in the TESTED slot passes through the actual
split cup, supported Thom cap and original time prism. The resulting
source primitive vanishes on constants independently of its own support. -/
@[expose] public section
namespace Finsler.NativeBVCutTestBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedSelfCut Finsler.NativeBVThomBoundary
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem cast_boundary (X : TopCat.{0}) (i j : ℕ) (h : i + 1 = j)
    (K : singularCochainGroup (ZMod 2) X i) :
    cochainCast h (cochainCoboundary (ZMod 2) X i K) = (chains X).d j i ≫ K := by
  subst j
  rfl

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)

theorem split_test_boundary (p q : ℕ)
    (K : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0) :
    (chains (TopCat.of (neighborhood (m + 1) r))).d ((p + 1) + q) (p + q) ≫
      GeometricTimeCupCochain.splitCup m p hr K q B =
    GeometricTimeCupCochain.splitCup m (p + 1) hr (cochainCoboundary (ZMod 2) _ p K) q B := by
  have h := cochainCupZMod2_coboundary_left' p q
    (cochainPullback (TopCat.ofHom (tested (m + 1) hr)) p K)
    (cochainPullback (TopCat.ofHom (retained (m + 1) hr)) q B)
    (cochainPullback_cocycle _ q B hB)
  rw [cast_boundary _ (p + q) ((p + 1) + q) (by omega)] at h
  unfold GeometricTimeCupCochain.splitCup NormalizedSelfCut.testedCocycle
  rw [← cochainPullback_cochainCoboundary]
  exact h.symm

theorem source_test_boundary (p q : ℕ)
    (K : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0) :
    (chains (Loops (m + 1))).d (m + ((p + 1) + q)) (m + (p + q)) ≫
      source m hρ hρr (p + q) (GeometricTimeCupCochain.splitCup m p hr K q B) =
    source m hρ hρr ((p + 1) + q)
      (GeometricTimeCupCochain.splitCup m (p + 1) hr (cochainCoboundary (ZMod 2) _ p K) q B) := by
  unfold source
  rw [lowering_boundary_at (GlobalThomTime.operation m hρ hρr) _ _ (by omega), split_test_boundary m hr p q K B hB]

theorem source_geometric (p q : ℕ)
    (K : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q) :
    CochainDegreeTransport.pre (Loops (m + 1)) (Nat.add_assoc m p q)
      (source m hρ hρr (p + q) (GeometricTimeCupCochain.splitCup m p hr K q B)) =
    GeometricTimeCupCochain.cochain m p hρ hρr hr K q B :=
  GlobalTimeCupCohomology.cochain_compare m hρ hρr hr p q K B

theorem relative_test_boundary_zero (p q : ℕ)
    (K : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X (m + ((p + 1) + q)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (m + ((p + 1) + q))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d (m + ((p + 1) + q)) (m + (p + q)) = 0) :
    u ≫ source m hρ hρr ((p + 1) + q)
      (GeometricTimeCupCochain.splitCup m (p + 1) hr (cochainCoboundary (ZMod 2) _ p K) q B) = 0 := by
  rw [← source_test_boundary m hρ hρr hr p q K B hB]
  exact relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1))) _ _ u hu _
    (source_constants_zero m hρ hρr _ _)

end
end Finsler.NativeBVCutTestBoundary
