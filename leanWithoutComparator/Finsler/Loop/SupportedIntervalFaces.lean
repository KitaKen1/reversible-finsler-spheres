module

public import Finsler.Loop.SupportedIntervalProduct
public import Finsler.Loop.SupportedCapTestOrder

/-! Literal endpoint and spatial-carrier annihilation for the genuine
product supported cut, before taking any cohomology class. -/
@[expose] public section
namespace Finsler.SupportedIntervalFaces
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain Finsler.SupportedIntervalProduct
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def slice (X : TopCat.{0}) (t : _root_.unitInterval) : Set (space X) :=
  {z | CartesianMonoidalCategory.snd X TopCat.I z = ULift.up t}

def sliceNearProject (X : TopCat.{0}) (B : Set X) (t : _root_.unitInterval) :
    TopCat.of ((SupportedCap.subspaceMap (space X) (slice X t)) ⁻¹' liftSet X B) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun z => ⟨project X z.val.val, z.property⟩,
    (((project X).hom.continuous.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _⟩

theorem slice_near_square (X : TopCat.{0}) (B : Set X) (t : _root_.unitInterval) :
    restriction (SupportedCap.subspaceMap (space X) (slice X t))
      ((SupportedCap.subspaceMap (space X) (slice X t)) ⁻¹' liftSet X B) (liftSet X B) (fun _ h => h) ≫
      nearOut X B = sliceNearProject X B t ≫ endpoint (TopCat.of B) t := by
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · exact z.val.property

theorem map_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) (hf : ∀ x, f x ∈ S)
    (N : ℕ) (φ : singularCochainGroup (ZMod 2) Y N)
    (hφ : cochainPullback (SupportedCap.subspaceMap Y S) N φ = 0) : cochainPullback f N φ = 0 := by
  let g : X ⟶ TopCat.of S := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap Y S := rfl
  rw [he, pullback_comp, hφ]
  change (push g).f N ≫ 0 = 0
  exact comp_zero

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
  (θ : singularCochainGroup (ZMod 2) X p)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
  (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) q)

theorem tested_slice_zero (t : _root_.unitInterval)
    (hT : cochainPullback (endpoint (TopCat.of B) t) q T = 0) :
    cochainPullback (SupportedCap.subspaceMap (space X) (slice X t)) N
      (tested X A B hA hB hc p q N hN θ hs T) = 0 := by
  apply SupportedCapTestOrder.cut_carrier_zero_at_degree
  rw [← pullback_comp, slice_near_square, pullback_comp, hT]
  change (push (sliceNearProject X B t)).f q ≫ 0 = 0
  exact comp_zero

theorem tested_endpoint_zero (t : _root_.unitInterval)
    (hT : cochainPullback (endpoint (TopCat.of B) t) q T = 0) :
    cochainPullback (endpoint X t) N (tested X A B hA hB hc p q N hN θ hs T) = 0 :=
  map_zero (endpoint X t) (slice X t) (fun _ => rfl) N _
    (tested_slice_zero X A B hA hB hc p q N hN θ hs T t hT)

theorem tested_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) p θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S ▷ TopCat.I) N
      (tested X A B hA hB hc p q N hN θ hs T) = 0 := by
  have h := congrArg (fun f => f ≫ cochainPullback (nearOut X B) q T)
    (SupportedThomCarrierZero.cut_map_zero (liftSet X A) (liftSet X B) (liftSet X S)
      (lift_open X A hA) (lift_open X B hB) (lift_cover X A B hc) p q N hN
      (cochainPullback (project X) p θ) (theta_supported X A p θ hs)
      (theta_supported X S p θ hS) (SupportedCap.subspaceMap X S ▷ TopCat.I) (fun z => z.1.property))
  simp only [Category.assoc, zero_comp] at h
  exact h

end
end Finsler.SupportedIntervalFaces
