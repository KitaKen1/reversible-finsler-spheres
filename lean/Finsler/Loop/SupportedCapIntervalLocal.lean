module

public import Finsler.Loop.SupportedIntervalProduct

/-! The original supported cut and the canonical right interval agree
on the SAME original near/far small-chain complex. The normalized
Thom factor is restricted naturally, and all degree casts are retained. -/
@[expose] public section
namespace Finsler.SupportedCapIntervalLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.RightIntervalCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem normalized_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization Y) φ) :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X)
      (cochainPullback f n φ) := by
  cases n with
  | zero => exact (DoldKan.degeneraciesVanish_zero_iff_true _).mpr True.intro
  | succ n =>
    rw [DoldKan.degeneraciesVanish_succ_iff]
    intro i
    change (SingularNormalization.linearization X).σ i ≫
      (SingularNormalization.linearMap f).app _ ≫ φ = 0
    rw [← Category.assoc, SimplicialObject.σ_naturality, Category.assoc, hφ.σ_comp, comp_zero]

theorem interval_cap_at_degree (X : TopCat.{0}) (a q N : ℕ) (hN : a + q = N)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    TimeTriangleSplit.interval X N ≫
      absoluteChain (space X) a (q + 1) (N + 1) (by omega)
        (cochainPullback (SupportedIntervalProduct.project X) a φ) =
      absoluteChain X a q N hN φ ≫ TimeTriangleSplit.interval X q := by
  subst N
  exact NormalizedCapRightInterval.interval_cap X a q φ hφ

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (p q : ℕ)
  (θ : singularCochainGroup (ZMod 2) X (p + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (p + 1) θ = 0)
  (T : singularCochainGroup (ZMod 2) (space (TopCat.of B)) (q + 1))

def before : singularCochainGroup (ZMod 2) X (p + q + 1) :=
  SupportedCap.cut X A B hA hB hc (p + 1) q (p + q + 1) (by omega) θ hs ≫
    TimeTriangleSplit.interval (TopCat.of B) q ≫ T

def after : singularCochainGroup (ZMod 2) X (p + q + 1) :=
  TimeTriangleSplit.interval X (p + q + 1) ≫
    SupportedIntervalProduct.tested X A B hA hB hc (p + 1) (q + 1) (p + q + 1 + 1)
      (by omega) θ hs T

def difference : singularCochainGroup (ZMod 2) X (p + q + 1) :=
  before X A B hA hB hc p q θ hs T - after X A B hA hB hc p q θ hs T

theorem near_before : cochainPullback (SupportedCap.subspaceMap X B) (p + q + 1)
    (before X A B hA hB hc p q θ hs T) =
    absoluteChain (TopCat.of B) (p + 1) q (p + q + 1) (by omega)
      (cochainPullback (SupportedCap.subspaceMap X B) (p + 1) θ) ≫
        TimeTriangleSplit.interval (TopCat.of B) q ≫ T := by
  exact SupportedRightTestLocal.cut_near_scalar X A B hA hB hc (p + 1) q (p + q + 1)
    (by omega) θ hs (TimeTriangleSplit.interval (TopCat.of B) q ≫ T) |>.trans
      (SupportedRightTestLocal.dual_at_degree _ _ _ _ _ _ _).symm

theorem near_after : cochainPullback (SupportedCap.subspaceMap X B) (p + q + 1)
    (after X A B hA hB hc p q θ hs T) =
    TimeTriangleSplit.interval (TopCat.of B) (p + q + 1) ≫
      absoluteChain (space (TopCat.of B)) (p + 1) (q + 1) (p + q + 1 + 1) (by omega)
        (cochainPullback (SupportedIntervalProduct.project (TopCat.of B)) (p + 1)
          (cochainPullback (SupportedCap.subspaceMap X B) (p + 1) θ)) ≫ T := by
  change (push (SupportedCap.subspaceMap X B)).f _ ≫ (TimeTriangleSplit.interval X _ ≫ _) = _
  rw [← Category.assoc, RightIntervalCochain.naturality, Category.assoc]
  exact congrArg (fun z => TimeTriangleSplit.interval (TopCat.of B) (p + q + 1) ≫ z)
    (SupportedIntervalProduct.near_tested X A B hA hB hc (p + 1) (q + 1) _ (by omega) θ hs T)

theorem near_equal (hθ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) θ) :
    cochainPullback (SupportedCap.subspaceMap X B) (p + q + 1) (before X A B hA hB hc p q θ hs T) =
    cochainPullback (SupportedCap.subspaceMap X B) (p + q + 1) (after X A B hA hB hc p q θ hs T) := by
  rw [near_before, near_after]
  exact (congrArg (fun f => f ≫ T) (interval_cap_at_degree (TopCat.of B) (p + 1) q (p + q + 1)
    (by omega) _ (normalized_pullback (SupportedCap.subspaceMap X B) (p + 1) θ hθ))).symm

theorem far_before : cochainPullback (SupportedCap.subspaceMap X A) (p + q + 1)
    (before X A B hA hB hc p q θ hs T) = 0 :=
  SupportedRightTestLocal.cut_thom_zero X A B A hA hB hc (p + 1) q (p + q + 1) (by omega)
    θ hs hs (TimeTriangleSplit.interval (TopCat.of B) q ≫ T)

theorem far_after : cochainPullback (SupportedCap.subspaceMap X A) (p + q + 1)
    (after X A B hA hB hc p q θ hs T) = 0 := by
  change (push (SupportedCap.subspaceMap X A)).f _ ≫ (TimeTriangleSplit.interval X _ ≫ _) = 0
  rw [← Category.assoc, RightIntervalCochain.naturality, Category.assoc]
  have h := SupportedIntervalProduct.far_tested X A B hA hB hc (p + 1) (q + 1) (p + q + 1 + 1) (by omega) θ hs T
  change (push (SupportedCap.subspaceMap X A ▷ TopCat.I)).f (p + q + 1 + 1) ≫
    SupportedIntervalProduct.tested X A B hA hB hc (p + 1) (q + 1) (p + q + 1 + 1)
      (by omega) θ hs T = 0 at h
  rw [h, comp_zero]

theorem small_equal (hθ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) θ) :
    (inclusion X (SupportedCap.cover X A B)).f (p + q + 1) ≫ difference X A B hA hB hc p q θ hs T = 0 := by
  apply CarrierCochainZero.small_zero
  intro i
  cases i with
  | false =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X A).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((far_before X A B hA hB hc p q θ hs T).trans
      (far_after X A B hA hB hc p q θ hs T).symm)
  | true =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X B).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (near_equal X A B hA hB hc p q θ hs T hθ)

end
end Finsler.SupportedCapIntervalLocal
