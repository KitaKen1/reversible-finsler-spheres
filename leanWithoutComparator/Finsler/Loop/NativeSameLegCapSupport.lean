module

public import Finsler.Loop.NativeSameLegLocalizedClass
public import Finsler.Loop.SupportedCutCochainCarrierZero

/-! Actual support of the SAME source-local primitive-cap correction.
The original retained evaluation is the cut start point on the whole
near tube. Both first-far and endpoint-far carriers therefore kill the
complete correction, with the original radii. Rotation boundary zero
and diagonal seam zero are kept as concrete separate statements. -/
@[expose] public section
namespace Finsler.NativeSameLegCapSupport
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.SupportedCapNaturality
open Finsler.NativeSameLegThomPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem splitCup_far_family_zero (m p : ℕ) (Q : Sphere (m + 1)) {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) {Y : TopCat.{0}}
    (f : Y ⟶ TopCat.of (SupportedSelfCut.neighborhood (m + 1) r))
    (hf : ∀ y, η ≤ ‖(LocalizedCutEvaluationCochain.nearStart (m + 1) r (f y) : Ambient (m + 1)) - Q‖) :
    cochainPullback f (p + (m + 1)) (NativeSameLegLocalizedClass.output m p Q hr hη T) = 0 := by
  have hz := LocalizedSphereTopCocycle.pullback_far_zero (by omega) Q hη
    (f ≫ LocalizedCutEvaluationCochain.nearStart (m + 1) r) hf
  unfold NativeSameLegLocalizedClass.output GeometricTimeCupCochain.splitCup
  rw [cochainCup_naturality, LocalizedCutEvaluationCochain.retained_pullback, ← pullback_comp, hz, cochainCup_zero_right]

theorem first_far_of_either_far {n : ℕ} (Q : Sphere n) (z : SelfCutThomCocycle.parameters n) {r η D : ℝ}
    (hz : SupportedSelfCut.distance n z < r) (hηr : η + r ≤ D)
    (hfar : D ≤ ‖(H1FiberBase.point z.2 : Ambient n) - Q‖ ∨ D ≤ ‖(H1SelfCutNeighborhood.endpoint z : Ambient n) - Q‖) :
    η ≤ ‖(H1FiberBase.point z.2 : Ambient n) - Q‖ := by
  have hd : 0 ≤ SupportedSelfCut.distance n z := norm_nonneg _
  rcases hfar with h | h
  · linarith
  · have he := norm_sub_le_norm_sub_add_norm_sub (H1SelfCutNeighborhood.endpoint z : Ambient n) (H1FiberBase.point z.2 : Ambient n) (Q : Ambient n)
    change ‖(H1SelfCutNeighborhood.endpoint z : Ambient n) - Q‖ ≤
      SupportedSelfCut.distance n z + ‖(H1FiberBase.point z.2 : Ambient n) - Q‖ at he
    linarith

def outside {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (Q : Sphere n) (D : ℝ) :
    Set (localSpace P v₀ k) :=
  {z | D ≤ ‖(H1FiberBase.point (family P v₀ k isLong z).2 : Ambient n) - Q‖ ∨
    D ≤ ‖(H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z) : Ambient n) - Q‖}

def nearOutput (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool) (Q : Sphere (m + 1))
    {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η) (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :=
  cochainPullback (NativeSameLegOriginalCapClass.nearMap P v₀ k isLong r) (p + (m + 1))
    (NativeSameLegLocalizedClass.output m p Q hr hη T)

theorem near_output_carrier_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (isLong : Bool)
    (Q : Sphere (m + 1)) {r η : ℝ} (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) (C : Set (localSpace P v₀ k))
    (hC : ∀ z, z ∈ C → z ∈ NativeSameLegLocalCap.near P v₀ k isLong r →
      η ≤ ‖(H1FiberBase.point (family P v₀ k isLong z).2 : Ambient (m + 1)) - Q‖) :
    cochainPullback (restriction (SupportedCap.subspaceMap (localSpace P v₀ k) C)
      ((SupportedCap.subspaceMap (localSpace P v₀ k) C) ⁻¹' NativeSameLegLocalCap.near P v₀ k isLong r)
      (NativeSameLegLocalCap.near P v₀ k isLong r) (fun _ h => h)) (p + (m + 1))
      (nearOutput m p P v₀ k isLong Q hr hη T) = 0 := by
  unfold nearOutput
  rw [← pullback_comp]
  apply splitCup_far_family_zero m p Q hr hη T
  intro z
  exact hC z.val.val z.val.property z.property

theorem correction_carrier_zero (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    (k : Fin 3) (isLong : Bool) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) (C : Set (localSpace P v₀ k))
    (hC : ∀ z, z ∈ C → z ∈ NativeSameLegLocalCap.near P v₀ k isLong r →
      η ≤ ‖(H1FiberBase.point (family P v₀ k isLong z).2 : Ambient (m + 1)) - Q‖) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) C) (m + (p + (m + 1)))
      (NativeSameLegLocalCap.correction m hm P v₀ k isLong hρ hρr hρ1 (p + (m + 1))
        (nearOutput m p P v₀ k isLong Q hr hη T)) = 0 :=
  SupportedCutCochainCarrierZero.subspace_cochain_zero (localSpace P v₀ k)
    (NativeSameLegLocalCap.exterior P v₀ k isLong ρ) (NativeSameLegLocalCap.near P v₀ k isLong r) C
    (NativeSameLegLocalCap.exterior_open P v₀ k isLong ρ) (NativeSameLegLocalCap.near_open P v₀ k isLong r)
    (NativeSameLegLocalCap.cover P v₀ k isLong hρr) m (p + (m + 1))
    (primitive (by omega) P v₀ k isLong hρ hρ1) (NativeSameLegLocalCap.primitive_supported m hm P v₀ k isLong hρ hρ1)
    (nearOutput m p P v₀ k isLong Q hr hη T) (near_output_carrier_zero m p P v₀ k isLong Q hr hη T C hC)

theorem correction_outside_zero (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    (k : Fin 3) (isLong : Bool) (Q : Sphere (m + 1)) {ρ r η D : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (hr : r ≤ 1) (hη : 0 < η) (hηr : η + r ≤ D)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (outside P v₀ k isLong Q D)) (m + (p + (m + 1)))
      (NativeSameLegLocalCap.correction m hm P v₀ k isLong hρ hρr hρ1 (p + (m + 1))
        (nearOutput m p P v₀ k isLong Q hr hη T)) = 0 :=
  correction_carrier_zero m hm p P v₀ k isLong Q hρ hρr hρ1 hr hη T _
    (fun z hz hn => first_far_of_either_far Q (family P v₀ k isLong z) hn hηr hz)

end
end Finsler.NativeSameLegCapSupport
