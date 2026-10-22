module

public import Finsler.Loop.OriginalDoubleSupportedCap
public import Finsler.Loop.MultiFarCapRestriction
public import Finsler.Loop.SupportedSmallCochainComparison

/-! An explicit boundary from the TWO ORIGINAL sequential supported
cuts to the genuine common-cover cup cap. A near-output cochain is
defined only on B intersect D. Near equality and each separate far
zero prove exact small-chain equality on the actual three-open cover.
The original subdivision prism supplies the global source primitive. -/
@[expose] public section
namespace Finsler.OriginalDoubleCapCommonComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MultiFarSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (A B C D : Set X)
  (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hD : IsOpen D)
  (hAB : A ∪ B = Set.univ) (hCD : C ∪ D = Set.univ)
  (p r q : ℕ) (θ : singularCochainGroup (ZMod 2) X p)
  (η : singularCochainGroup (ZMod 2) X (r + 1))
  (hθ : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
  (hη : cochainPullback (SupportedCap.subspaceMap X C) (r + 1) η = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (B ∩ D : Set X)) q)

def sourceCover := cover X (DoubleFarCupOneCap.far X A C) (B ∩ D)

def sequential : singularCochainGroup (ZMod 2) X ((p + r) + q + 1) :=
  OriginalDoubleSupportedCap.sequential X B C D A hA hB hC hD hAB hCD
    p (r + 1) q ((p + r) + q + 1) (by omega) θ η hθ hη ψ

def coupled := DoubleFarCupOneCap.left X A C p r θ η hθ hη (B ∩ D)
  hA hC (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD) q ψ

def difference : singularCochainGroup (ZMod 2) X ((p + r) + q + 1) :=
  sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ -
    coupled X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ

theorem near_equal : cochainPullback (SupportedCap.subspaceMap X (B ∩ D)) _
    (sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) =
    cochainPullback (SupportedCap.subspaceMap X (B ∩ D)) _
      (coupled X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) := by
  have hs := OriginalDoubleSupportedCap.common_near X B C D A hA hB hC hD hAB hCD
    p (r + 1) q ((p + r) + q + 1) (by omega) θ η hθ hη ψ (p + r + 1) (by omega)
  change cochainPullback (SupportedCap.subspaceMap X (B ∩ D)) _
    (sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = _ at hs
  rw [hs]
  change _ = (push (SupportedCap.subspaceMap X (B ∩ D))).f _ ≫
    (cut X (DoubleFarCupOneCap.far X A C) (B ∩ D) (DoubleFarCupOneCap.far_open X A C hA hC)
      (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD)
      (p + r + 1) q ((p + r) + q + 1) (by omega) _ _ ≫ ψ)
  rw [← Category.assoc, MultiFarCapRestriction.cut_near]
  rfl

theorem coupled_far_zero (i : Bool) :
    cochainPullback (SupportedCap.subspaceMap X (DoubleFarCupOneCap.far X A C i)) _
      (coupled X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  change (push (SupportedCap.subspaceMap X (DoubleFarCupOneCap.far X A C i))).f _ ≫
    (cut X (DoubleFarCupOneCap.far X A C) (B ∩ D) (DoubleFarCupOneCap.far_open X A C hA hC)
      (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD)
      (p + r + 1) q ((p + r) + q + 1) (by omega) _ _ ≫ ψ) = 0
  rw [← Category.assoc, MultiFarCapRestriction.cut_far, zero_comp]

theorem sequential_far_zero (i : Bool) :
    cochainPullback (SupportedCap.subspaceMap X (DoubleFarCupOneCap.far X A C i)) _
      (sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  cases i with
  | false =>
    exact OriginalDoubleSupportedCap.first_far_zero X B C D A hA hB hC hD hAB hCD
      p (r + 1) q ((p + r) + q + 1) (by omega) θ η hθ hη ψ
  | true =>
    exact OriginalDoubleSupportedCap.second_far_zero X B C D A hA hB hC hD hAB hCD
      p (r + 1) q ((p + r) + q + 1) (by omega) θ η hθ hη ψ

theorem small_equal : (inclusion X (sourceCover X A B C D)).f ((p + r) + q + 1) ≫
    difference X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ = 0 := by
  apply CarrierCochainZero.small_zero
  intro i
  cases i with
  | none =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X (B ∩ D)).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (near_equal X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ)
  | some i =>
    change ((singularCochainComplexZMod2.map
      (SupportedCap.subspaceMap X (DoubleFarCupOneCap.far X A C i)).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((sequential_far_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ i).trans
      (coupled_far_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ i).symm)

def primitive : singularCochainGroup (ZMod 2) X ((p + r) + q) :=
  SupportedSmallCochainComparison.primitive (sourceCover X A B C D) ((p + r) + q)
    (difference X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ)

theorem difference_closed (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X (r + 1) η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (B ∩ D : Set X)) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (difference X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  change ((cochainCxZMod2 X).d _ _).hom (_ - _) = 0
  rw [map_sub]
  have hs := OriginalDoubleSupportedCap.sequential_closed X B C D A hA hB hC hD hAB hCD
    p (r + 1) q ((p + r) + q + 1) (by omega) θ η hθ hη ψ hθc hηc hψ
  have ht := DoubleFarCupOneCap.left_closed X A C p r θ η hθ hη (B ∩ D)
    hA hC (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD) q ψ hθc hηc hψ
  change cochainCoboundary (ZMod 2) X _ (sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) -
    cochainCoboundary (ZMod 2) X _ (coupled X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0
  exact sub_eq_zero.mpr (hs.trans ht.symm)

theorem boundary (hθc : cochainCoboundary (ZMod 2) X p θ = 0)
    (hηc : cochainCoboundary (ZMod 2) X (r + 1) η = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (B ∩ D : Set X)) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (primitive X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) =
      difference X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ :=
  SupportedSmallCochainComparison.primitive_boundary (sourceCover X A B C D)
    (cover_open X (DoubleFarCupOneCap.far X A C) (B ∩ D) (DoubleFarCupOneCap.far_open X A C hA hC) (hB.inter hD))
    (cover_univ X (DoubleFarCupOneCap.far X A C) (B ∩ D) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD))
    ((p + r) + q) _ (difference_closed X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ hθc hηc hψ)
    (small_equal X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ)

end
end Finsler.OriginalDoubleCapCommonComparison
