module

public import Finsler.Loop.NativeSequentialSupportedStages
public import Finsler.Topology.SelfCutEndpoints

/-! Carrier annihilation for the actual normalized supported operation.
Both lemmas retain its original image-preserving small approximation.
The output lemma uses the near-side inverse image of the SAME carrier. -/
@[expose] public section
namespace Finsler.NativeSupportedStageCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeOrderedDoubleCutSupported
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem map_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y)
    (hf : ∀ x, f x ∈ S) (q : ℕ) (T : singularCochainGroup (ZMod 2) Y q)
    (hT : cochainPullback (SupportedCap.subspaceMap Y S) q T = 0) :
    cochainPullback f q T = 0 := by
  let g : X ⟶ TopCat.of S := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap Y S := rfl
  rw [he, pullback_comp, hT]
  change (push g).f q ≫ 0 = 0
  exact comp_zero

variable {n : ℕ} {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters n)
  (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)

theorem thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) n (thom f hn hρ) = 0)
    (q : ℕ) : (push (SupportedCap.subspaceMap X S)).f (n + q) ≫
      (operation f hn hρ hρr).component q = 0 :=
  SelfCutEndpoints.cut_map_zero (far f ρ) (near f r) S (far_open f ρ) (near_open f r)
    (cover f hρr) n q (thom f hn hρ) (thom_supported f hn hρ) hS
      (SupportedCap.subspaceMap X S) (fun x => x.property)

theorem output_zero (S : Set X) (q : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (near f r)) q)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (near f r))
      ((SupportedCap.subspaceMap X (near f r)) ⁻¹' S)) q T = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) (n + q)
      ((operation f hn hρ hρr).component q ≫ T) = 0 := by
  apply SupportedCutCochainCarrierZero.subspace_cochain_zero X (far f ρ) (near f r) S
    (far_open f ρ) (near_open f r) (cover f hρr) n q (thom f hn hρ) (thom_supported f hn hρ) T
  exact map_zero (restriction (SupportedCap.subspaceMap X S)
    ((SupportedCap.subspaceMap X S) ⁻¹' near f r) (near f r) (fun _ h => h))
    ((SupportedCap.subspaceMap X (near f r)) ⁻¹' S) (fun z => z.val.property) q T hT

theorem parameter_time_zero (S : Set X) (t : IntervalSobolev.ClosedInterval)
    (hS : ∀ z ∈ S, (f z).1 = t)
    (ht : cochainPullback (SelfCutThomCocycle.atTime n t) n
      (NormalizedSelfCut.cocycle n hn hρ) = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) n (thom f hn hρ) = 0 :=
  pullback_support f S (SelfCutEndpoints.timeSlice n t) hS n _
    (SelfCutEndpoints.slice_cocycle_zero n hn hρ t ht)

end
end Finsler.NativeSupportedStageCarrier
