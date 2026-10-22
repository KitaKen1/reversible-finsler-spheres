module

public import Finsler.Loop.ComplementThomTimeComparison
public import Finsler.Loop.NativeBVRelativeCochain
public import Finsler.Loop.SelfCutPrismCoboundary

/-! The supported complement-Thom representative error, after ANY
closed near test, is an explicit constant-relative source boundary.
It remains invisible after the original full-period H1 rotation on
actual constant-relative cycles. No absolute-cycle assumption is
made about the original cut-time prism. -/
@[expose] public section
namespace Finsler.ComplementThomTimeCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.ComplementThomTimeComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 1 ≤ m) {ρ r : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) (hρr : ρ < r)
  (q : ℕ) (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)

def parameter : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q) :=
  primitiveCap m hm hρ hρ2 hρr q ≫ K

theorem parameter_boundary (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    cochainCoboundary (ZMod 2) (parameters (m + 1)) (m + q) (parameter m hm hρ hρ2 hρr q K) =
      SupportedThomTime.aligned (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m
        (ComplementThomEndpointPrimitive.swapped m hρ) (ComplementThomEndpointPrimitive.swapped_supported m hρ)
        (ComplementThomEndpointPrimitive.swapped_closed m hρ) q ≫ K - GlobalThomTime.aligned m hρ hρr q ≫ K := by
  have he := congrArg (fun f => f ≫ K) (cap_boundary m hm hρ hρ2 hρr q)
  change (chains (TopCat.of (neighborhood (m + 1) r))).d (q + 1) q ≫ K = 0 at hK
  simp only [Category.assoc, hK, comp_zero, Preadditive.sub_comp] at he
  exact sub_eq_zero.mp he.symm

theorem parameter_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (atTime (m + 1) t) (m + q) (parameter m hm hρ hρ2 hρr q K) = 0 := by
  change (push (atTime (m + 1) t)).f _ ≫ (_ ≫ K) = 0
  rw [← Category.assoc, cap_endpoint_zero m hm hρ hρ2 hρr q t ht, zero_comp]

private theorem time_boundary_at (n i j : ℕ) (h : i + 1 = j)
    (T : singularCochainGroup (ZMod 2) (parameters n) j)
    (h₀ : cochainPullback (atTime n 0) j T = 0) (h₁ : cochainPullback (atTime n 1) j T = 0) :
    (chains (Loops n)).d j i ≫ (-((SelfCutTimePrism.chainHomotopy n).hom i j ≫ T)) =
      SelfCutTimePrism.prism n j ≫ cochainCoboundary (ZMod 2) (parameters n) j T := by
  subst j
  exact SelfCutPrismCoboundary.boundary n i T h₀ h₁

def sourcePrimitive (k : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) k :=
  -((SelfCutTimePrism.chainHomotopy (m + 1)).hom k (m + q) ≫ parameter m hm hρ hρ2 hρr q K)

theorem source_boundary (k : ℕ) (h : k + 1 = m + q) (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    (chains (Loops (m + 1))).d (m + q) k ≫ sourcePrimitive m hm hρ hρ2 hρr q K k =
      (operation m hm hρ hρ2 hρr).component q ≫ K - (GlobalThomTime.operation m hρ hρr).component q ≫ K := by
  unfold sourcePrimitive
  rw [time_boundary_at (m + 1) k (m + q) h _
    (parameter_endpoint m hm hρ hρ2 hρr q K 0 (Or.inl rfl))
    (parameter_endpoint m hm hρ hρ2 hρr q K 1 (Or.inr rfl)),
    parameter_boundary m hm hρ hρ2 hρr q K hK, Preadditive.comp_sub]
  rfl

private theorem prism_constants_zero (n i j : ℕ) (h : i + 1 = j)
    (T : singularCochainGroup (ZMod 2) (parameters n) j)
    (hT : cochainPullback (CylinderPrismNaturality.map (GlobalTimeCupConstantsVanish.inclusion n)) j T = 0) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion n) i
      (-((SelfCutTimePrism.chainHomotopy n).hom i j ≫ T)) = 0 := by
  subst j
  change (push (GlobalTimeCupConstantsVanish.inclusion n)).f i ≫
    (-(AnnularTimeTrim.prism (Loops n) i ≫ T)) = 0
  rw [Preadditive.comp_neg, ← Category.assoc, CylinderPrismNaturality.prism, Category.assoc]
  change -(_ ≫ cochainPullback (CylinderPrismNaturality.map (GlobalTimeCupConstantsVanish.inclusion n)) (i + 1) T) = 0
  rw [hT, comp_zero, neg_zero]

theorem source_constants_zero (k : ℕ) (h : k + 1 = m + q) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) k
      (sourcePrimitive m hm hρ hρ2 hρr q K k) = 0 := by
  apply prism_constants_zero (m + 1) k (m + q) h
  change (push (CylinderPrismNaturality.map (GlobalTimeCupConstantsVanish.inclusion (m + 1)))).f _ ≫
    (primitiveCap m hm hρ hρ2 hρr q ≫ K) = 0
  rw [← Category.assoc, cap_diagonal_zero m hm hρ hρ2 hρr q _
    (GlobalTimeCupConstantsVanish.cylinder_diagonal (m + 1)), zero_comp]

theorem relative_values (k : ℕ) (h : k + 1 = m + q) (hK : cochainCoboundary (ZMod 2) _ q K = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X (m + q))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (m + q)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d (m + q) k = 0) :
    u ≫ (operation m hm hρ hρ2 hρr).component q ≫ K =
      u ≫ (GlobalThomTime.operation m hρ hρr).component q ≫ K := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← source_boundary m hm hρ hρ2 hρr q K k h hK]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1))) k (m + q)
    u hu _ (source_constants_zero m hm hρ hρ2 hρr q K k h)

theorem rotated_relative_values (k : ℕ) (hk : 1 ≤ k) (h : k + 1 = m + q)
    (hK : cochainCoboundary (ZMod 2) _ q K = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X k)
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f k) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d k (k - 1) = 0) :
    u ≫ (H1LoopRotation.chainHomotopy (m + 1)).hom k (m + q) ≫ (operation m hm hρ hρ2 hρr).component q ≫ K =
      u ≫ (H1LoopRotation.chainHomotopy (m + 1)).hom k (m + q) ≫ (GlobalThomTime.operation m hρ hρr).component q ≫ K :=
  NativeBVRelativeCochain.comparison_relative_values (m + 1) (k - 1) k (m + q) (by omega) h
    (sourcePrimitive m hm hρ hρ2 hρr q K k) (source_constants_zero m hm hρ hρ2 hρr q K k h) _ _
    (source_boundary m hm hρ hρ2 hρr q K k h hK) u hu

end
end Finsler.ComplementThomTimeCochain
