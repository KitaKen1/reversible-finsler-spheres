module

public import Finsler.Loop.SupportedCapSmallNaturality
public import Finsler.Loop.SupportedSmallCochainComparison
public import Finsler.Loop.ComplementThomTimeCochain

/-! Exact naturality on the ORIGINAL small-chain cover supplies a
concrete subdivision-prism correction for complementing the actual
supported Thom cap. Its primitive vanishes on the whole diagonal,
so it can be integrated through the actual cut-time prism. -/
@[expose] public section
namespace Finsler.ComplementCapNaturalityCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.WholeSelfCutComplement
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 1 ≤ m) {ρ r : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) (hρr : ρ < r)
  (q : ℕ) (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q)

def nearTest : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q :=
  cochainPullback (neighborhoodMap (m + 1) r) q K

def before : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q + 1) :=
  cochainPullback (complement (m + 1)) (m + q + 1) (GlobalThomTime.aligned m hρ hρr q ≫ K)

def after : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q + 1) :=
  SupportedThomTime.aligned (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m
    (ComplementThomEndpointPrimitive.swapped m hρ) (ComplementThomEndpointPrimitive.swapped_supported m hρ)
    (ComplementThomEndpointPrimitive.swapped_closed m hρ) q ≫ nearTest m q K

theorem nearTest_closed (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    cochainCoboundary (ZMod 2) _ q (nearTest m q K) = 0 :=
  pullback_closed (neighborhoodMap (m + 1) r) q K hK

private theorem aligned_closed {X : TopCat.{0}} (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (d : ℕ) (φ : singularCochainGroup (ZMod 2) X (d + 1))
    (hs : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0) (q : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hT : cochainCoboundary (ZMod 2) _ q T = 0) :
    cochainCoboundary (ZMod 2) X (d + q + 1)
      (SupportedThomTime.aligned X A B hA hB hc d φ hs hφ q ≫ T) = 0 := by
  have he := congrArg (fun f => f ≫ T) (SupportedThomTime.comm X A B hA hB hc d φ hs hφ q)
  change (chains (TopCat.of B)).d (q + 1) q ≫ T = 0 at hT
  change (chains X).d (d + q + 1 + 1) (d + q + 1) ≫ (_ ≫ T) = 0
  simpa only [Nat.add_assoc, Category.assoc, hT, comp_zero] using he.symm

theorem before_closed (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    cochainCoboundary (ZMod 2) _ (m + q + 1) (before m hρ hρr q K) = 0 := by
  apply pullback_closed (complement (m + 1))
  exact aligned_closed _ _ (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) (NormalizedSelfCut.cocycle_supported _ _ hρ)
    (NormalizedSelfCut.cocycle_closed _ _ hρ) q K hK

theorem after_closed (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    cochainCoboundary (ZMod 2) _ (m + q + 1) (after m hρ hρr q K) = 0 :=
  aligned_closed _ _ (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m _
    (ComplementThomEndpointPrimitive.swapped_supported m hρ) (ComplementThomEndpointPrimitive.swapped_closed m hρ)
    q _ (nearTest_closed m q K hK)

private theorem naturality_at {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hcX : A ∪ B = Set.univ)
    (hC : IsOpen C) (hD : IsOpen D) (hcY : C ∪ D = Set.univ)
    (hfA : Set.MapsTo f A C) (hfB : Set.MapsTo f B D)
    (p q N : ℕ) (h : p + q = N) (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (SupportedCap.subspaceMap Y C) p φ = 0) :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f N ≫ (push f).f N ≫
      SupportedCap.cut Y C D hC hD hcY p q N h φ hs =
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f N ≫
      SupportedCap.cut X A B hA hB hcX p q N h (cochainPullback f p φ)
        (pullback_support f A C hfA p φ hs) ≫ (push (restriction f B D hfB)).f q := by
  subst N
  exact SupportedCapSmallNaturality.naturality f A B C D hA hB hcX hC hD hcY hfA hfB p q φ hs

private theorem pullback_push {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (T : singularCochainGroup (ZMod 2) Y n) : cochainPullback f n T = (push f).f n ≫ T := rfl

theorem small_equal :
    (SmallChainCarrier.inclusion (parameters (m + 1))
      (SupportedCap.cover _ (exterior (m + 1) ρ) (neighborhood (m + 1) r))).f (m + q + 1) ≫ before m hρ hρr q K =
    (SmallChainCarrier.inclusion (parameters (m + 1))
      (SupportedCap.cover _ (exterior (m + 1) ρ) (neighborhood (m + 1) r))).f (m + q + 1) ≫ after m hρ hρr q K := by
  have he := naturality_at (complement (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
    (exterior_mapsTo (m + 1) ρ) (neighborhood_mapsTo (m + 1) r)
    (m + 1) q (m + q + 1) (by omega)
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) (NormalizedSelfCut.cocycle_supported _ _ hρ)
  have ha := SupportedThomTimeRepresentative.aligned_cut (parameters (m + 1))
    (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m q
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) (NormalizedSelfCut.cocycle_supported _ _ hρ)
    (NormalizedSelfCut.cocycle_closed _ _ hρ)
  change GlobalThomTime.aligned m hρ hρr q = _ at ha
  unfold before after
  rw [ha, SupportedThomTimeRepresentative.aligned_cut, pullback_push, nearTest, pullback_push]
  simpa only [ComplementThomEndpointPrimitive.swapped, neighborhoodMap, Category.assoc] using congrArg (fun f => f ≫ K) he

theorem diagonal_mapsTo (n : ℕ) : Set.MapsTo (complement n)
    (FilteredGlobalThomTime.endpointCarrier n) (FilteredGlobalThomTime.endpointCarrier n) := by
  intro z hz
  change H1FiberBase.point (complement n z).2 = H1SelfCutNeighborhood.endpoint (complement n z)
  rw [point_complement, endpoint_complement]
  exact hz.symm

private theorem aligned_diagonal_zero {X : TopCat.{0}} (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (d : ℕ)
    (φ : singularCochainGroup (ZMod 2) X (d + 1))
    (hs : cochainPullback (SupportedCap.subspaceMap X A) (d + 1) φ = 0)
    (hφ : cochainCoboundary (ZMod 2) X (d + 1) φ = 0)
    (hC : cochainPullback (SupportedCap.subspaceMap X C) (d + 1) φ = 0)
    (q : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    cochainPullback (SupportedCap.subspaceMap X C) (d + q + 1)
      (SupportedThomTime.aligned X A B hA hB hc d φ hs hφ q ≫ T) = 0 := by
  change (push (SupportedCap.subspaceMap X C)).f _ ≫ (_ ≫ T) = 0
  rw [← Category.assoc, SupportedThomTime.endpoint X A B hA hB hc d φ hs hφ (SupportedCap.subspaceMap X C) C hC (fun z => z.property) q, zero_comp]

theorem before_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))
      (m + q + 1) (before m hρ hρr q K) = 0 := by
  apply pullback_support (complement (m + 1)) _ _ (diagonal_mapsTo (m + 1))
  exact aligned_diagonal_zero _ _ _ (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m
    (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) (NormalizedSelfCut.cocycle_supported _ _ hρ)
    (NormalizedSelfCut.cocycle_closed _ _ hρ) (FilteredGlobalThomTime.cocycle_endpoint m hρ) q K

include hm hρ2 in
theorem after_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))
      (m + q + 1) (after m hρ hρr q K) = 0 :=
  aligned_diagonal_zero _ _ _ (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) m _
    (ComplementThomEndpointPrimitive.swapped_supported m hρ) (ComplementThomEndpointPrimitive.swapped_closed m hρ)
    (ComplementThomEndpointPrimitive.swapped_carrier_zero m hm hρ hρ2) q _

def difference : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q + 1) :=
  before m hρ hρr q K - after m hρ hρr q K

def primitive : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + q) :=
  SupportedSmallCochainComparison.primitive
    (SupportedCap.cover _ (exterior (m + 1) ρ) (neighborhood (m + 1) r)) (m + q) (difference m hρ hρr q K)

theorem primitive_boundary (hK : cochainCoboundary (ZMod 2) _ q K = 0) :
    cochainCoboundary (ZMod 2) _ (m + q) (primitive m hρ hρr q K) = difference m hρ hρr q K := by
  apply SupportedSmallCochainComparison.primitive_boundary _
    (SupportedCap.cover_open _ _ _ (exterior_open _ _) (neighborhood_open _ _))
    (SupportedCap.cover_univ _ _ _ (cover _ hρr))
  · change ((cochainCxZMod2 (parameters (m + 1))).d _ _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((before_closed m hρ hρr q K hK).trans (after_closed m hρ hρr q K hK).symm)
  · change _ ≫ (_ - _) = 0
    rw [Preadditive.comp_sub, small_equal, sub_self]

include hm hρ2 in
theorem primitive_diagonal_zero :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1)))
      (m + q) (primitive m hρ hρr q K) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))).op).f (m + q + 1)).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_diagonal_zero m hρ hρr q K).trans (after_diagonal_zero m hm hρ hρ2 hρr q K).symm)

end
end Finsler.ComplementCapNaturalityCochain
