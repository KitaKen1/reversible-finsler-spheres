module

public import Finsler.Loop.RightIntervalCochain
public import Finsler.Loop.SupportedRightTestLocal

/-! The actual inverse-image near/far cover on X times the canonical
interval, with its genuine supported cut and explicit near-output map.
No alternative subdivision or unsupported zero extension is substituted. -/
@[expose] public section
namespace Finsler.SupportedIntervalProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.RightIntervalCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

abbrev project (X : TopCat.{0}) : space X ⟶ X := CartesianMonoidalCategory.fst X TopCat.I
abbrev liftSet (X : TopCat.{0}) (A : Set X) : Set (space X) := project X ⁻¹' A

theorem lift_open (X : TopCat.{0}) (A : Set X) (hA : IsOpen A) : IsOpen (liftSet X A) :=
  hA.preimage (project X).hom.continuous

theorem lift_cover (X : TopCat.{0}) (A B : Set X) (hc : A ∪ B = Set.univ) :
    liftSet X A ∪ liftSet X B = Set.univ := by
  rw [← Set.preimage_union, hc, Set.preimage_univ]

def nearIn (X : TopCat.{0}) (B : Set X) : space (TopCat.of B) ⟶ TopCat.of (liftSet X B) :=
  TopCat.ofHom ⟨fun z => ⟨(z.1.val, z.2), z.1.property⟩, by fun_prop⟩

def nearOut (X : TopCat.{0}) (B : Set X) : TopCat.of (liftSet X B) ⟶ space (TopCat.of B) :=
  TopCat.ofHom ⟨fun (z : liftSet X B) => (⟨(z.val : X × TopCat.I).1, z.property⟩,
    (z.val : X × TopCat.I).2),
    (((project X).hom.continuous.comp continuous_subtype_val).subtype_mk _).prodMk
      ((CartesianMonoidalCategory.snd X TopCat.I).hom.continuous.comp continuous_subtype_val)⟩

theorem near_square (X : TopCat.{0}) (B : Set X) :
    nearIn X B ≫ SupportedCap.subspaceMap (space X) (liftSet X B) =
      SupportedCap.subspaceMap X B ▷ TopCat.I := rfl

theorem near_in_out (X : TopCat.{0}) (B : Set X) : nearIn X B ≫ nearOut X B = 𝟙 _ := rfl

theorem project_square (X : TopCat.{0}) (B : Set X) :
    (SupportedCap.subspaceMap X B ▷ TopCat.I) ≫ project X =
      project (TopCat.of B) ≫ SupportedCap.subspaceMap X B := rfl

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
  (θ : singularCochainGroup (ZMod 2) X p)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)

include hs in
theorem theta_supported : cochainPullback (SupportedCap.subspaceMap (space X) (liftSet X A)) p
    (cochainPullback (project X) p θ) = 0 :=
  pullback_support (project X) (liftSet X A) A (fun _ h => h) p θ hs

def tested (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) q) :
    singularCochainGroup (ZMod 2) (space X) N :=
  SupportedCap.cut (space X) (liftSet X A) (liftSet X B) (lift_open X A hA) (lift_open X B hB)
    (lift_cover X A B hc) p q N hN (cochainPullback (project X) p θ) (theta_supported X A p θ hs) ≫
      cochainPullback (nearOut X B) q T

theorem near_tested (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) q) :
    cochainPullback (SupportedCap.subspaceMap X B ▷ TopCat.I) N (tested X A B hA hB hc p q N hN θ hs T) =
      absoluteChain (space (TopCat.of B)) p q N hN
        (cochainPullback (project (TopCat.of B)) p (cochainPullback (SupportedCap.subspaceMap X B) p θ)) ≫ T := by
  have h := congrArg (fun f => f ≫ cochainPullback (nearOut X B) q T)
    (SupportedCapNearRestriction.cut_near_map (space X) (liftSet X A) (liftSet X B)
      (lift_open X A hA) (lift_open X B hB) (lift_cover X A B hc) p q N hN
      (cochainPullback (project X) p θ) (theta_supported X A p θ hs) (nearIn X B))
  rw [near_square] at h
  simp only [Category.assoc] at h
  have hout : (push (nearIn X B)).f q ≫ cochainPullback (nearOut X B) q T = T := by
    change cochainPullback (nearIn X B) q (cochainPullback (nearOut X B) q T) = T
    rw [← pullback_comp, near_in_out]
    exact congrArg (fun f => (f.f q).hom T)
      (singularCochainComplexZMod2.map_id (Opposite.op (space (TopCat.of B))))
  have hθ : cochainPullback (SupportedCap.subspaceMap X B ▷ TopCat.I) p (cochainPullback (project X) p θ) =
      cochainPullback (project (TopCat.of B)) p (cochainPullback (SupportedCap.subspaceMap X B) p θ) := by
    rw [← pullback_comp, project_square, pullback_comp]
  rw [hout, hθ] at h
  exact h

theorem far_tested (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) q) :
    cochainPullback (SupportedCap.subspaceMap X A ▷ TopCat.I) N (tested X A B hA hB hc p q N hN θ hs T) = 0 := by
  have h := congrArg (fun f => f ≫ cochainPullback (nearOut X B) q T)
    (SupportedCapNearRestriction.cut_far_map (space X) (liftSet X A) (liftSet X B)
      (lift_open X A hA) (lift_open X B hB) (lift_cover X A B hc) p q N hN
      (cochainPullback (project X) p θ) (theta_supported X A p θ hs) (nearIn X A))
  rw [near_square] at h
  simp only [Category.assoc, zero_comp] at h
  exact h

theorem tested_closed (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) q)
    (hθ : cochainCoboundary (ZMod 2) X p θ = 0)
    (hT : cochainCoboundary (ZMod 2) (space (TopCat.of B)) q T = 0) :
    cochainCoboundary (ZMod 2) (space X) N (tested X A B hA hB hc p q N hN θ hs T) = 0 :=
  SupportedCapTestOrderCoupling.supported_closed (space X) (liftSet X A) (liftSet X B)
    (lift_open X A hA) (lift_open X B hB) (lift_cover X A B hc) p q N hN _
    (theta_supported X A p θ hs) (pullback_closed (project X) p θ hθ) _
    (pullback_closed (nearOut X B) q T hT)

end
end Finsler.SupportedIntervalProduct
