module

public import Finsler.Loop.OriginalFirstHalfJointCover

/-! Actual cochain vanishing on the joint cover from its two far
restrictions and its genuine proper source restriction. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfJointCochainZero

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem restriction_zero_subset (X : TopCat.{0}) (U V : Set X) (hUV : U ⊆ V)
    (d : ℕ) (ξ : singularCochainGroup (ZMod 2) X d)
    (hV : cochainPullback (SupportedCap.subspaceMap X V) d ξ = 0) :
    cochainPullback (SupportedCap.subspaceMap X U) d ξ = 0 := by
  let f := restriction (𝟙 X) U V hUV
  have he : f ≫ SupportedCap.subspaceMap X V = SupportedCap.subspaceMap X U := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hz := congrArg (cochainPullback f d) hV
  rw [← pullback_comp, he] at hz
  simpa only [cochainPullback, map_zero] using hz

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ)
  (d : ℕ) (ξ : singularCochainGroup (ZMod 2) (ambient α β) d)
  (hjoin : cochainPullback (SupportedCap.subspaceMap (ambient α β) (joinFar α β κ)) d ξ = 0)
  (hcut : cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) d ξ = 0)
  (hsource : cochainPullback (source α β R r) d ξ = 0)

include hsource in
theorem proper_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (proper α β R r)) d ξ = 0 := by
  have hj : (properIso α β R r).inv ≫ source α β R r = SupportedCap.subspaceMap (ambient α β) (proper α β R r) := by
    rw [source, SmallCapSubspaceLift.source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he := congrArg (cochainPullback (properIso α β R r).inv d) hsource
  rw [← pullback_comp, hj] at he
  simpa only [cochainPullback, map_zero] using he

include hjoin hcut hsource in
theorem cover_zero (i : Option (Option (FirstInputRotationCochains.space α β R r))) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cover α β R r η κ ρ i)) d ξ = 0 := by
  cases i with
  | none =>
    exact restriction_zero_subset (ambient α β) _ (joinFar α β κ)
      (fun z hz => show κ ≤ pairGap α β z from hz.le) d ξ hjoin
  | some i =>
    cases i with
    | none => exact hcut
    | some i =>
      exact restriction_zero_subset (ambient α β) _ (proper α β R r)
        (fun z hz => ⟨hz.1.2.le, hz.2.le⟩) d ξ (proper_zero α β R r d ξ hsource)

include hjoin hcut hsource in
theorem small_cap_zero (q : ℕ) :
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f (d + q) ≫
      absoluteChain (ambient α β) d q (d + q) rfl ξ = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((ambient α β).smallSingularSubcomplex (cover α β R r η κ ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β) (cover α β R r η κ ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact SupportedCap.cap_zero_on_simplex _ _ d q _ rfl _
    (cover_zero α β R r η κ ρ d ξ hjoin hcut hsource i) σ.val hi

end
end Finsler.OriginalFirstHalfJointCochainZero
