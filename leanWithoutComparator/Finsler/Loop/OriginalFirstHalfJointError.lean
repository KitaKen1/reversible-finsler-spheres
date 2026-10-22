module

public import Finsler.Loop.OriginalFirstHalfJointCochains
public import Finsler.Topology.SupportedCapCochain

/-! Remove the literal tested-extension coboundary error on the
actual original-input joint cover, using both far supports and real
proper restriction closure, never ambient closure. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfJointError

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains Finsler.OriginalFirstHalfJointCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

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

private theorem absolute_add (X : TopCat.{0}) (d q : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X d) :
    absoluteChain X d q (d + q) rfl (φ + ψ) =
      absoluteChain X d q (d + q) rfl φ + absoluteChain X d q (d + q) rfl ψ := map_add _ φ ψ

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  {κ : ℝ} (hκ : 0 < κ) (η : ℝ)

include hR hT in
theorem error_proper_subspace_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (proper α β R r)) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  have hj : (properIso α β R r).inv ≫ source α β R r = SupportedCap.subspaceMap (ambient α β) (proper α β R r) := by
    rw [source, SmallCapSubspaceLift.source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he := congrArg (cochainPullback (properIso α β R r).inv (((m + 1) + (m + p)) + 1))
    (OriginalFirstHalfJointCochains.error_proper_zero α β R r hR hr h p T hκ hT)
  rw [← pullback_comp, hj] at he
  simpa only [cochainPullback, map_zero] using he

include hR hT in
theorem error_cover_zero (i : Option (Option (FirstInputRotationCochains.space α β R r))) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cover α β R r η κ ρ i)) (((m + 1) + (m + p)) + 1)
      (error α β r hr h p T hκ) = 0 := by
  cases i with
  | none =>
    apply restriction_zero_subset (ambient α β) (cover α β R r η κ ρ none) (joinFar α β κ)
      (fun z hz => show κ ≤ pairGap α β z from hz.le) _ _
    exact OriginalFirstHalfJointCochains.error_join_far_zero α β r hr h p T hκ
  | some i =>
    cases i with
    | none => exact OriginalFirstHalfJointCochains.error_cut_far_zero α β r hr h p T hκ
    | some i =>
      apply restriction_zero_subset (ambient α β) (cover α β R r η κ ρ (some (some i))) (proper α β R r)
        (fun z hz => ⟨hz.1.2.le, hz.2.le⟩) _ _
      exact error_proper_subspace_zero α β R r hR hr h p T hT hκ

include hR hT in
theorem error_small_cap_zero (q : ℕ) :
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (error α β r hr h p T hκ) = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((ambient α β).smallSingularSubcomplex (cover α β R r η κ ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β) (cover α β R r η κ ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact SupportedCap.cap_zero_on_simplex _ _ (((m + 1) + (m + p)) + 1) q _ rfl _
    (error_cover_zero α β R r hR hr h p T hT hκ η i) σ.val hi

include hR hT in
theorem commutator_cap (q : ℕ) :
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α β) ((m + 1) + (m + p)) (primitive α β r hr h p T hκ)) =
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (CupOne.cup (ambient α β) (m + 1) ((m + 1) + p) (((m + 1) + (m + p)) + 1) (by omega)
          (join α β hκ) (gamma α β r hr h p T)) -
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl
        (CupOne.cup (ambient α β) ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) (by omega)
          (gamma α β r hr h p T) (join α β hκ)) := by
  have he := congrArg (fun ξ =>
    (inclusion (ambient α β) (cover α β R r η κ ρ)).f ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q ((((m + 1) + (m + p)) + 1) + q) rfl ξ)
    (boundary_with_error α β r hr h p T hκ)
  rw [absolute_add, SupportedCapCochain.absolute_sub, Preadditive.comp_add, Preadditive.comp_sub,
    error_small_cap_zero α β R r hR hr h p T hT hκ η q, add_zero] at he
  exact he

end
end Finsler.OriginalFirstHalfJointError
