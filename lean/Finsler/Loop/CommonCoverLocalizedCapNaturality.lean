module

public import Finsler.Loop.CylinderCommonCover

/-! Real localized caps commute on an actual common source cover.
Only the genuine near-subspace inclusion on CHAIN GROUPS is cancelled. -/

@[expose] public section
namespace Finsler.CommonCoverLocalizedCapNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem component {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y p)
    (hs : cochainPullback (SupportedCap.subspaceMap Y C) p φ = 0) :
    (CylinderCommonCover.toSource (SupportedCap.cover X A B) (SupportedCap.cover Y C D) f).f (p + q) ≫
      SupportedCap.localizedCap X A B p q (p + q) rfl (cochainPullback f p φ)
        (pullback_support f A C hA p φ hs) ≫ (push (restriction f B D hB)).f q =
    (CylinderCommonCover.toTarget (SupportedCap.cover X A B) (SupportedCap.cover Y C D) f).f (p + q) ≫
      SupportedCap.localizedCap Y C D p q (p + q) rfl φ hs := by
  have : Mono ((push (SupportedCap.subspaceMap Y D)).f q) := SupportedCap.subspacePush_mono Y D q
  apply (cancel_mono ((push (SupportedCap.subspaceMap Y D)).f q)).mp
  have hi := congrArg (fun g => g.f q) (restriction_push f B D hB)
  have hMs := congrArg (fun g => g.f (p + q))
    (CylinderCommonCover.toSource_inclusion (SupportedCap.cover X A B) (SupportedCap.cover Y C D) f)
  have hMt := congrArg (fun g => g.f (p + q))
    (CylinderCommonCover.toTarget_inclusion (SupportedCap.cover X A B) (SupportedCap.cover Y C D) f)
  have hxc : SupportedCap.localizedCap X A B p q (p + q) rfl (cochainPullback f p φ)
      (pullback_support f A C hA p φ hs) ≫ (push (SupportedCap.subspaceMap X B)).f q =
    (inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
      RelativeCapAssociativity.absoluteChain X p q (p + q) rfl (cochainPullback f p φ) :=
    SupportedCap.localizedCap_inclusion X A B p q (p + q) rfl
      (cochainPullback f p φ) (pullback_support f A C hA p φ hs)
  have hyc : SupportedCap.localizedCap Y C D p q (p + q) rfl φ hs ≫
      (push (SupportedCap.subspaceMap Y D)).f q =
    (inclusion Y (SupportedCap.cover Y C D)).f (p + q) ≫
      RelativeCapAssociativity.absoluteChain Y p q (p + q) rfl φ :=
    SupportedCap.localizedCap_inclusion Y C D p q (p + q) rfl φ hs
  simp only [HomologicalComplex.comp_f] at hi hMs hMt
  have hn : RelativeCapAssociativity.absoluteChain X p q (p + q) rfl
      (cochainPullback f p φ) ≫ (push f).f q =
    (push f).f (p + q) ≫ RelativeCapAssociativity.absoluteChain Y p q (p + q) rfl φ :=
    RelativeCapBoundary.absolute_chain_natural f p q (p + q) rfl φ
  simp only [Category.assoc]
  rw [hi, reassoc_of% hxc, hyc,
    reassoc_of% hMs, reassoc_of% hMt,
    hn]

end
end Finsler.CommonCoverLocalizedCapNaturality
