module

public import Finsler.Loop.NormalizedCutScalarPullback
public import Finsler.Loop.NativeSupportedStageCarrier

/-! Carrier control for the SAME pullback-comparison primitive. Output
support is imposed on the original ambient parameter space, so the proof
does not assume naturality of its chosen small-chain retraction. -/
@[expose] public section
namespace Finsler.NormalizedCutScalarCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeOrderedDoubleCutSupported Finsler.SupportedSelfCut
open Finsler.NormalizedCutScalarPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def outputCarrier {Y Z : TopCat.{0}} (B : Set Y) (g : TopCat.of B ⟶ Z) (C : Set Z) : Set Y :=
  {y | ∀ hy : y ∈ B, g ⟨y, hy⟩ ∈ C}

theorem output_restriction_zero {Y Z : TopCat.{0}} (B : Set Y) (g : TopCat.of B ⟶ Z)
    (C : Set Z) (p : ℕ) (T : singularCochainGroup (ZMod 2) Z p)
    (hT : cochainPullback (SupportedCap.subspaceMap Z C) p T = 0) :
    cochainPullback (restriction (SupportedCap.subspaceMap Y (outputCarrier B g C))
      ((SupportedCap.subspaceMap Y (outputCarrier B g C)) ⁻¹' B) B (fun _ h => h)) p
      (cochainPullback g p T) = 0 := by
  rw [← pullback_comp]
  exact NativeSupportedStageCarrier.map_zero
    (restriction (SupportedCap.subspaceMap Y (outputCarrier B g C))
      ((SupportedCap.subspaceMap Y (outputCarrier B g C)) ⁻¹' B) B (fun _ h => h) ≫ g)
    C (fun z => z.val.property z.property) p T hT

variable (m : ℕ) {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
  {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (p q : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (IntervalSobolev.SphereLoop (m + 1))) p)
  (B : singularCochainGroup (ZMod 2) (TopCat.of (IntervalSobolev.SphereLoop (m + 1))) q)
  (S : Set X)

theorem primitive_zero
    (hl : cochainPullback (SupportedCap.subspaceMap X S) ((m + 1) + (p + q))
      (localValue m f hρ hρr hr p q T B) = 0)
    (ho : cochainPullback (SupportedCap.subspaceMap X S) ((m + 1) + (p + q))
      (originalValue m f hρ hρr hr p q T B) = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (m + (p + q))
      (primitive m f hρ hρr hr p q T B) = 0 := by
  apply SupportedCapPullbackPrimitive.primitive_carrier_zero
  · have h := congrArg (CochainDegreeTransport.pre (TopCat.of S)
      (show m + (p + q) + 1 = (m + 1) + (p + q) by omega)) hl
    rw [pre_pullback] at h
    dsimp only [localValue, NativeOrderedDoubleCutSupported.operation, SupportedCapHomology.operation] at h
    rw [pre_cut X (far f ρ) (near f r) (far_open f ρ) (near_open f r)
      (NativeOrderedDoubleCutSupported.cover f hρr) (m + 1) (p + q)
      (m + (p + q) + 1) ((m + 1) + (p + q)) (by omega) rfl (by omega)] at h
    simpa only [CochainDegreeTransport.pre, comp_zero, SupportedCapPullbackPrimitive.localValue,
      SupportedCapPullbackPrimitive.original, nearMap, thom] using h
  · have h := congrArg (CochainDegreeTransport.pre (TopCat.of S)
      (show m + (p + q) + 1 = (m + 1) + (p + q) by omega)) ho
    rw [pre_pullback] at h
    dsimp only [originalValue] at h
    rw [pre_pullback] at h
    dsimp only [NormalizedSelfCut.operation, SupportedCapHomology.operation] at h
    rw [pre_cut (SelfCutThomCocycle.parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
      (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r)
      (SupportedSelfCut.cover (m + 1) hρr) (m + 1) (p + q) (m + (p + q) + 1) ((m + 1) + (p + q)) (by omega) rfl (by omega)] at h
    simpa only [CochainDegreeTransport.pre, comp_zero, SupportedCapPullbackPrimitive.localValue,
      SupportedCapPullbackPrimitive.original, nearMap, thom] using h

theorem original_time_zero (t : IntervalSobolev.ClosedInterval)
    (hf : ∀ x ∈ S, (f x).1 = t)
    (ht : cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) ((m + 1) + (p + q))
      (originalValue m f hρ hρr hr p q T B) = 0 := by
  unfold originalValue
  rw [← pullback_comp]
  change (push (_ ≫ f)).f _ ≫ (_ ≫ _) = 0
  rw [← Category.assoc]
  have h := SelfCutEndpoints.cut_map_zero
    (exterior (m + 1) ρ) (neighborhood (m + 1) r) (SelfCutEndpoints.timeSlice (m + 1) t)
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (SupportedSelfCut.cover (m + 1) hρr)
    (m + 1) (p + q) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (SelfCutEndpoints.slice_cocycle_zero (m + 1) (by omega) hρ t ht)
    (SupportedCap.subspaceMap X S ≫ f) (fun z => hf z.val z.property)
  change (push (_ ≫ f)).f _ ≫ (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + q) = 0 at h
  rw [h, zero_comp]

theorem original_tested_zero (C : Set (IntervalSobolev.SphereLoop (m + 1)))
    (hT : cochainPullback (SupportedCap.subspaceMap _ C) p T = 0)
    (hf : ∀ x ∈ S, ∀ hx : f x ∈ neighborhood (m + 1) r,
      SupportedSelfCut.tested (m + 1) hr ⟨f x, hx⟩ ∈ C) :
    cochainPullback (SupportedCap.subspaceMap X S) ((m + 1) + (p + q))
      (originalValue m f hρ hρr hr p q T B) = 0 := by
  let D := outputCarrier (neighborhood (m + 1) r) (TopCat.ofHom (SupportedSelfCut.tested (m + 1) hr)) C
  unfold originalValue
  rw [← pullback_comp]
  apply NativeSupportedStageCarrier.map_zero (SupportedCap.subspaceMap X S ≫ f) D
    (fun x => hf x.val x.property)
  apply SupportedCutCochainCarrierZero.subspace_cochain_zero (SelfCutThomCocycle.parameters (m + 1))
    (exterior (m + 1) ρ) (neighborhood (m + 1) r) D
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (SupportedSelfCut.cover (m + 1) hρr)
    (m + 1) (p + q) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) (GeometricTimeCupCochain.splitCup m p hr T q B)
  unfold GeometricTimeCupCochain.splitCup NormalizedSelfCut.testedCocycle
  rw [cochainCup_naturality, output_restriction_zero _ _ _ p T hT, cochainCup_zero_left]

theorem original_retained_zero (C : Set (IntervalSobolev.SphereLoop (m + 1)))
    (hB : cochainPullback (SupportedCap.subspaceMap _ C) q B = 0)
    (hf : ∀ x ∈ S, ∀ hx : f x ∈ neighborhood (m + 1) r,
      SupportedSelfCut.retained (m + 1) hr ⟨f x, hx⟩ ∈ C) :
    cochainPullback (SupportedCap.subspaceMap X S) ((m + 1) + (p + q))
      (originalValue m f hρ hρr hr p q T B) = 0 := by
  let D := outputCarrier (neighborhood (m + 1) r) (TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr)) C
  unfold originalValue
  rw [← pullback_comp]
  apply NativeSupportedStageCarrier.map_zero (SupportedCap.subspaceMap X S ≫ f) D
    (fun x => hf x.val x.property)
  apply SupportedCutCochainCarrierZero.subspace_cochain_zero (SelfCutThomCocycle.parameters (m + 1))
    (exterior (m + 1) ρ) (neighborhood (m + 1) r) D
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (SupportedSelfCut.cover (m + 1) hρr)
    (m + 1) (p + q) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) (GeometricTimeCupCochain.splitCup m p hr T q B)
  unfold GeometricTimeCupCochain.splitCup
  rw [cochainCup_naturality, output_restriction_zero _ _ _ q B hB, cochainCup_zero_right]

end
end Finsler.NormalizedCutScalarCarrier
