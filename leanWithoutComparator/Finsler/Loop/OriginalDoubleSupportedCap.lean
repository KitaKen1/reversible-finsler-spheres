module

public import Finsler.Loop.SupportedCapNearRestriction
public import Finsler.Loop.SupportedCapTestOrder
public import Finsler.Loop.DoubleFarCupOneCap

/-! The ORIGINAL sequential supported cuts with a test defined only
on the genuine common near set. Exact common-near cap/cup formula,
literal vanishing on EACH original far set, and genuine closure.
No commutation of small retractions or global closed extension is used. -/
@[expose] public section
namespace Finsler.OriginalDoubleSupportedCap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (B C D : Set X)

def secondFar : Set (TopCat.of B) := (SupportedCap.subspaceMap X B) ⁻¹' C
def secondNear : Set (TopCat.of B) := (SupportedCap.subspaceMap X B) ⁻¹' D

def jointMap : TopCat.of (secondNear X B D) ⟶ TopCat.of (B ∩ D : Set X) := TopCat.ofHom
  ⟨fun z => ⟨z.val.val, z.val.property, z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def jointFirst : TopCat.of (B ∩ D : Set X) ⟶ TopCat.of B := TopCat.ofHom
  ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def jointSecond : TopCat.of (B ∩ D : Set X) ⟶ TopCat.of (secondNear X B D) := TopCat.ofHom
  ⟨fun z => ⟨jointFirst X B D z, z.property.2⟩,
    (jointFirst X B D).hom.continuous.subtype_mk _⟩

theorem joint_square : jointSecond X B D ≫ jointMap X B D = 𝟙 (TopCat.of (B ∩ D : Set X)) := by
  ext z
  rfl

theorem second_cover (hCD : C ∪ D = Set.univ) :
    secondFar X B C ∪ secondNear X B D = Set.univ := by
  rw [secondFar, secondNear, ← Set.preimage_union, hCD, Set.preimage_univ]

variable (A : Set X) (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hD : IsOpen D)
  (hAB : A ∪ B = Set.univ) (hCD : C ∪ D = Set.univ)
  (p r q N : ℕ) (hN : (p + r) + q = N)
  (θ : singularCochainGroup (ZMod 2) X p) (η : singularCochainGroup (ZMod 2) X r)
  (hθ : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
  (hη : cochainPullback (SupportedCap.subspaceMap X C) r η = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (B ∩ D : Set X)) q)

def inner : singularCochainGroup (ZMod 2) (TopCat.of B) (r + q) :=
  SupportedCap.cut (TopCat.of B) (secondFar X B C) (secondNear X B D)
    (hC.preimage (SupportedCap.subspaceMap X B).hom.continuous)
    (hD.preimage (SupportedCap.subspaceMap X B).hom.continuous) (second_cover X B C D hCD)
    r q (r + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) r η)
    (pullback_support _ (secondFar X B C) C (fun _ h => h) r η hη) ≫
      cochainPullback (jointMap X B D) q ψ

def sequential : singularCochainGroup (ZMod 2) X N :=
  SupportedCap.cut X A B hA hB hAB p (r + q) N (by omega) θ hθ ≫
    inner X B C D hC hD hCD r q η hη ψ

theorem inner_closed (hηc : cochainCoboundary (ZMod 2) X r η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (B ∩ D : Set X)) q ψ = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of B) (r + q) (inner X B C D hC hD hCD r q η hη ψ) = 0 :=
  SupportedCapTestOrderCoupling.supported_closed _ _ _ _ _ _ r q _ rfl _ _
    (pullback_closed _ r η hηc) _ (pullback_closed _ q ψ hψ)

theorem sequential_closed (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X r η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (B ∩ D : Set X)) q ψ = 0) :
    cochainCoboundary (ZMod 2) X N (sequential X B C D A hA hB hC hD hAB hCD p r q N hN θ η hθ hη ψ) = 0 :=
  SupportedCapTestOrderCoupling.supported_closed X A B hA hB hAB p (r + q) N (by omega) θ hθ hθc _
    (inner_closed X B C D hC hD hCD r q η hη ψ hηc hψ)

theorem first_far_zero : cochainPullback (SupportedCap.subspaceMap X A) N
    (sequential X B C D A hA hB hC hD hAB hCD p r q N hN θ η hθ hη ψ) = 0 := by
  change (push (SupportedCap.subspaceMap X A)).f N ≫
    (SupportedCap.cut X A B hA hB hAB p (r + q) N (by omega) θ hθ ≫ _) = 0
  rw [← Category.assoc, SupportedCapNearRestriction.cut_far, zero_comp]

def farOverlap : TopCat.of ((SupportedCap.subspaceMap X C) ⁻¹' B) ⟶
    TopCat.of (secondFar X B C) := TopCat.ofHom
  ⟨fun z => ⟨⟨z.val.val, z.property⟩, z.val.property⟩,
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem second_far_zero : cochainPullback (SupportedCap.subspaceMap X C) N
    (sequential X B C D A hA hB hC hD hAB hCD p r q N hN θ η hθ hη ψ) = 0 := by
  apply SupportedCapTestOrder.cut_carrier_zero_at_degree X A B C hA hB hAB p (r + q) N (by omega) θ hθ
    (inner X B C D hC hD hCD r q η hη ψ)
  have hz := SupportedCapNearRestriction.cut_far_map (TopCat.of B) (secondFar X B C) (secondNear X B D)
    (hC.preimage (SupportedCap.subspaceMap X B).hom.continuous)
    (hD.preimage (SupportedCap.subspaceMap X B).hom.continuous) (second_cover X B C D hCD)
    r q (r + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) r η)
    (pullback_support _ (secondFar X B C) C (fun _ h => h) r η hη) (farOverlap X B C)
  have he : farOverlap X B C ≫ SupportedCap.subspaceMap (TopCat.of B) (secondFar X B C) =
      restriction (SupportedCap.subspaceMap X C) ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h) := rfl
  rw [he] at hz
  change (push (restriction (SupportedCap.subspaceMap X C)
    ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h))).f (r + q) ≫
      inner X B C D hC hD hCD r q η hη ψ = 0
  simpa only [inner, Category.assoc, zero_comp] using congrArg
    (fun f => f ≫ cochainPullback (jointMap X B D) q ψ) hz

theorem cap_cup_at_degree (Y : TopCat.{0}) (a b d t M : ℕ) (hd : a + b = d) (hM : d + t = M)
    (α : singularCochainGroup (ZMod 2) Y a) (β : singularCochainGroup (ZMod 2) Y b) :
    absoluteChain Y a (b + t) M (by
      calc
        a + (b + t) = (a + b) + t := (Nat.add_assoc a b t).symm
        _ = d + t := congrArg (fun n => n + t) hd
        _ = M := hM) α ≫ absoluteChain Y b t (b + t) rfl β =
      absoluteChain Y d t M hM (CupOne.cup Y a b d hd α β) := by
  subst M
  exact CupCapOrder.cap_cup Y a b d t hd α β

theorem common_near (d : ℕ) (hd : p + r = d) : cochainPullback (SupportedCap.subspaceMap X (B ∩ D)) N
    (sequential X B C D A hA hB hC hD hAB hCD p r q N hN θ η hθ hη ψ) =
    absoluteChain (TopCat.of (B ∩ D : Set X)) d q N (by omega)
      (cochainPullback (SupportedCap.subspaceMap X (B ∩ D)) d (CupOne.cup X p r d hd θ η)) ≫ ψ := by
  let J := TopCat.of (B ∩ D : Set X)
  let j := SupportedCap.subspaceMap X (B ∩ D)
  have ho := SupportedCapNearRestriction.cut_near_map X A B hA hB hAB p (r + q) N (by omega) θ hθ
    (jointFirst X B D)
  change (push j).f N ≫ SupportedCap.cut X A B hA hB hAB p (r + q) N (by omega) θ hθ =
    absoluteChain J p (r + q) N (by omega) (cochainPullback j p θ) ≫ (push (jointFirst X B D)).f (r + q) at ho
  have hi := SupportedCapNearRestriction.cut_near_map (TopCat.of B) (secondFar X B C) (secondNear X B D)
    (hC.preimage (SupportedCap.subspaceMap X B).hom.continuous)
    (hD.preimage (SupportedCap.subspaceMap X B).hom.continuous) (second_cover X B C D hCD)
    r q (r + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) r η)
    (pullback_support _ (secondFar X B C) C (fun _ h => h) r η hη) (jointSecond X B D)
  have hp : (jointSecond X B D ≫ SupportedCap.subspaceMap (TopCat.of B) (secondNear X B D)) ≫
      SupportedCap.subspaceMap X B = j := rfl
  rw [← pullback_comp, hp] at hi
  change (push (jointFirst X B D)).f (r + q) ≫ _ =
    absoluteChain J r q (r + q) rfl (cochainPullback j r η) ≫ (push (jointSecond X B D)).f q at hi
  have htest : (push (jointSecond X B D)).f q ≫ cochainPullback (jointMap X B D) q ψ = ψ := by
    change cochainPullback (jointSecond X B D) q (cochainPullback (jointMap X B D) q ψ) = ψ
    rw [← pullback_comp, joint_square]
    exact congrArg (fun f => (f.f q).hom ψ) (singularCochainComplexZMod2.map_id (Opposite.op J))
  have hin : (push (jointFirst X B D)).f (r + q) ≫ inner X B C D hC hD hCD r q η hη ψ =
      absoluteChain J r q (r + q) rfl (cochainPullback j r η) ≫ ψ := by
    change (push (jointFirst X B D)).f (r + q) ≫
      (SupportedCap.cut (TopCat.of B) (secondFar X B C) (secondNear X B D)
        (hC.preimage (SupportedCap.subspaceMap X B).hom.continuous)
        (hD.preimage (SupportedCap.subspaceMap X B).hom.continuous) (second_cover X B C D hCD)
        r q (r + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) r η)
        (pullback_support _ (secondFar X B C) C (fun _ h => h) r η hη) ≫
          cochainPullback (jointMap X B D) q ψ) = _
    rw [← Category.assoc, hi, Category.assoc, htest]
  change (push j).f N ≫ (SupportedCap.cut X A B hA hB hAB p (r + q) N (by omega) θ hθ ≫
    inner X B C D hC hD hCD r q η hη ψ) = _
  rw [← Category.assoc, ho, Category.assoc, hin, ← Category.assoc,
    cap_cup_at_degree J p r d q N hd (by omega)]
  rw [CupCapOrder.naturality]

end
end Finsler.OriginalDoubleSupportedCap
