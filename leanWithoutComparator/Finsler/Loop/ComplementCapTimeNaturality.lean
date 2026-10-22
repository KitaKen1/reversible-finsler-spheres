module

public import Finsler.Loop.ComplementCapNaturalityCochain

/-! Combine the actual subdivision correction with the endpoint-zero
Thom representative correction. Complement moves from the near test
across the ORIGINAL supported Thom cap through the actual cut-time
prism and H1 rotation, with ONE constant-relative source primitive.
The remaining complementary time-square geometry is not asserted. -/
@[expose] public section
namespace Finsler.ComplementCapTimeNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.ComplementCapNaturalityCochain (nearTest)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

variable (m : ℕ) (hm : 1 ≤ m) {ρ r : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) (hρr : ρ < r)
  (q : ℕ) (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)

def parameter : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q) :=
  ComplementCapNaturalityCochain.primitive m hρ hρr q K +
    ComplementThomTimeCochain.parameter m hm hρ hρ2 hρr q (nearTest m q K)

theorem parameter_boundary (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    cochainCoboundary (ZMod 2) _ (m + q) (parameter m hm hρ hρ2 hρr q K) =
      ComplementCapNaturalityCochain.before m hρ hρr q K -
        (GlobalThomTime.aligned m hρ hρr q ≫ nearTest m q K : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q + 1)) := by
  change ((cochainCxZMod2 (parameters (m + 1))).d _ _).hom (_ + _) = _
  rw [map_add]
  change cochainCoboundary (ZMod 2) _ (m + q) (ComplementCapNaturalityCochain.primitive m hρ hρr q K) +
    cochainCoboundary (ZMod 2) _ (m + q) (ComplementThomTimeCochain.parameter m hm hρ hρ2 hρr q (nearTest m q K)) = _
  rw [ComplementCapNaturalityCochain.primitive_boundary m hρ hρr q K hK,
    ComplementThomTimeCochain.parameter_boundary m hm hρ hρ2 hρr q _ (ComplementCapNaturalityCochain.nearTest_closed m q K hK)]
  change (_ - ComplementCapNaturalityCochain.after m hρ hρr q K) +
    (ComplementCapNaturalityCochain.after m hρ hρr q K - _) = _
  exact sub_add_sub_cancel (ComplementCapNaturalityCochain.before m hρ hρr q K)
    (ComplementCapNaturalityCochain.after m hρ hρr q K)
    (GlobalThomTime.aligned m hρ hρr q ≫ nearTest m q K : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q + 1))

theorem parameter_carrier_zero :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))
      (m + q) (parameter m hm hρ hρ2 hρr q K) = 0 := by
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))).op).f (m + q)).hom (_ + _) = 0
  rw [map_add]
  have ha := ComplementCapNaturalityCochain.primitive_diagonal_zero m hm hρ hρ2 hρr q K
  have hb : cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))) (m + q)
      (ComplementThomTimeCochain.parameter m hm hρ hρ2 hρr q (nearTest m q K)) = 0 := by
    change (push (SupportedCap.subspaceMap _ _)).f _ ≫ (_ ≫ nearTest m q K) = 0
    rw [← Category.assoc, ComplementThomTimeComparison.cap_diagonal_zero m hm hρ hρ2 hρr q
      (SupportedCap.subspaceMap _ _) (fun z => z.property), zero_comp]
  exact (congrArg₂ (fun a b => a + b) ha hb).trans (zero_add 0)

theorem parameter_diagonal_zero {X : TopCat.{0}} (f : X ⟶ parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    cochainPullback f (m + q) (parameter m hm hρ hρ2 hρr q K) = 0 := by
  let g : X ⟶ TopCat.of (FilteredGlobalThomTime.endpointCarrier (m + 1)) :=
    TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap _ (FilteredGlobalThomTime.endpointCarrier (m + 1)) := by ext x : 1; rfl
  rw [he, pullback_comp, parameter_carrier_zero]
  change (push g).f (m + q) ≫ 0 = 0
  exact comp_zero

theorem parameter_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (atTime (m + 1) t) (m + q) (parameter m hm hρ hρ2 hρr q K) = 0 := by
  apply parameter_diagonal_zero m hm hρ hρ2 hρr q K
  rcases ht with rfl | rfl
  · exact fun _ => rfl
  · exact fun u => (sphereRepresentative_endpoints u).symm

def before : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + q) :=
  SelfCutTimePrism.prism (m + 1) (m + q) ≫ ComplementCapNaturalityCochain.before m hρ hρr q K

def after : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + q) :=
  (GlobalThomTime.operation m hρ hρr).component q ≫ nearTest m q K

def primitive (k : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) k :=
  -((SelfCutTimePrism.chainHomotopy (m + 1)).hom k (m + q) ≫ parameter m hm hρ hρ2 hρr q K)

private theorem time_boundary_at (n i j : ℕ) (h : i + 1 = j)
    (T : singularCochainGroup (ZMod 2) (parameters n) j)
    (h₀ : cochainPullback (atTime n 0) j T = 0) (h₁ : cochainPullback (atTime n 1) j T = 0) :
    (chains (Loops n)).d j i ≫ (-((SelfCutTimePrism.chainHomotopy n).hom i j ≫ T)) =
      SelfCutTimePrism.prism n j ≫ cochainCoboundary (ZMod 2) (parameters n) j T := by
  subst j
  exact SelfCutPrismCoboundary.boundary n i T h₀ h₁

theorem boundary (k : ℕ) (h : k + 1 = m + q) (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    (chains (Loops (m + 1))).d (m + q) k ≫ primitive m hm hρ hρ2 hρr q K k =
      before m hρ hρr q K - after m hρ hρr q K := by
  unfold primitive
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
  change (push (GlobalTimeCupConstantsVanish.inclusion n)).f i ≫ (-(AnnularTimeTrim.prism (Loops n) i ≫ T)) = 0
  rw [Preadditive.comp_neg, ← Category.assoc, CylinderPrismNaturality.prism, Category.assoc]
  change -(_ ≫ cochainPullback (CylinderPrismNaturality.map (GlobalTimeCupConstantsVanish.inclusion n)) (i + 1) T) = 0
  rw [hT, comp_zero, neg_zero]

theorem primitive_constants_zero (k : ℕ) (h : k + 1 = m + q) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) k
      (primitive m hm hρ hρ2 hρr q K k) = 0 :=
  prism_constants_zero (m + 1) k (m + q) h _ (parameter_diagonal_zero m hm hρ hρ2 hρr q K _
    (GlobalTimeCupConstantsVanish.cylinder_diagonal (m + 1)))

include hm hρ2 in
theorem relative_values (k : ℕ) (h : k + 1 = m + q) (hK : cochainCoboundary (ZMod 2) _ q K = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X (m + q))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (m + q)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d (m + q) k = 0) :
    u ≫ before m hρ hρr q K = u ≫ after m hρ hρr q K := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary m hm hρ hρ2 hρr q K k h hK]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1))) k (m + q)
    u hu _ (primitive_constants_zero m hm hρ hρ2 hρr q K k h)

include hm hρ2 in
theorem rotated_relative_values (k : ℕ) (hk : 1 ≤ k) (h : k + 1 = m + q)
    (hK : cochainCoboundary (ZMod 2) _ q K = 0)
    {M : ModuleCat.{0} (ZMod 2)} (u : M ⟶ (chains (Loops (m + 1))).X k)
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f k) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d k (k - 1) = 0) :
    u ≫ (H1LoopRotation.chainHomotopy (m + 1)).hom k (m + q) ≫ before m hρ hρr q K =
      u ≫ (H1LoopRotation.chainHomotopy (m + 1)).hom k (m + q) ≫ after m hρ hρr q K :=
  NativeBVRelativeCochain.comparison_relative_values (m + 1) (k - 1) k (m + q) (by omega) h
    (primitive m hm hρ hρ2 hρr q K k) (primitive_constants_zero m hm hρ hρ2 hρr q K k h) _ _
    (boundary m hm hρ hρ2 hρr q K k h hK) u hu

end
end Finsler.ComplementCapTimeNaturality
