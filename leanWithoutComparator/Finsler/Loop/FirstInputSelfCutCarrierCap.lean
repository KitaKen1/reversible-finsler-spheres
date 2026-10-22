module

public import Finsler.Loop.FirstInputSelfCutCover
public import Finsler.Loop.LiftedCapCochainBoundary
import all Finsler.Loop.OriginalFirstHalfCutGammaJoinCap

/-! A single-input cap lifted into actual proper-cut small chains.
Only local closure on the proper domain and far zero are needed.
The ambient tested extension is allowed to have a coboundary. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutCarrierCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ ρ : ℝ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (ambient α) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) d φ = 0)

theorem lift_source : SmallCapSubspaceLift.source (ambient α)
    (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (CompactRotatedCutData.source α r)
    (Iso.refl _) = source α r := by
  simp only [SmallCapSubspaceLift.source, Iso.refl_hom, Category.id_comp, source]

include hfar in
theorem parent_image (q : ℕ)
    (σ : ((ambient α).smallSingularSubcomplex (cover α r hr κ ρ) : SSet) _⦋d + q⦌)
    (hnz : (TopCat.toSSet.obj (ambient α)).ιChainComplex σ.val ≫
      absoluteChain (ambient α) d q (d + q) rfl φ ≠ 0) :
    ∃ i, Set.range ((ambient α).toSSetObjEquiv _ σ.val) ⊆ source α r '' carrier α r hr κ i := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α) (cover α r hr κ ρ) σ.val).mp σ.property
  cases i with
  | none => exact (hnz (SupportedCap.cap_zero_on_simplex _ _ d q (d + q) rfl φ hfar σ.val hi)).elim
  | some i => exact ⟨i, hi.trans (near_image α r hr κ ρ i)⟩

def component (q : ℕ) := SmallCapSubspaceLift.component (ambient α)
  (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (CompactRotatedCutData.source α r) (Iso.refl _)
  (cover α r hr κ ρ) (carrier α r hr κ) d φ
  (fun q σ hnz => by rw [lift_source]; exact parent_image α r hr κ ρ d φ hfar q σ hnz) q

theorem component_source (q : ℕ) :
    component α r hr κ ρ d φ hfar q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).f q ≫
        (push (source α r)).f q =
    (inclusion (ambient α) (cover α r hr κ ρ)).f (d + q) ≫ absoluteChain (ambient α) d q (d + q) rfl φ := by
  have hc := SmallCapSubspaceLift.component_inclusion (ambient α)
    (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (CompactRotatedCutData.source α r) (Iso.refl _)
    (cover α r hr κ ρ) (carrier α r hr κ) d φ
    (fun q σ hnz => by rw [lift_source]; exact parent_image α r hr κ ρ d φ hfar q σ hnz) q
  simpa only [component, SmallCapSubspaceLift.target, HomologicalComplex.comp_f, lift_source, Category.assoc] using hc

theorem target_mono (q : ℕ) : Mono (((inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
    (carrier α r hr κ)) ≫ push (source α r)).f q) := by
  have hc := SmallCapSubspaceLift.target_mono (ambient α)
    (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (CompactRotatedCutData.source α r) (Iso.refl _)
    (carrier α r hr κ) q
  simpa only [SmallCapSubspaceLift.target, lift_source] using hc

variable (hproper : cochainPullback (source α r) (d + 1) (cochainCoboundary (ZMod 2) (ambient α) d φ) = 0)

include hproper hfar in
theorem cover_boundary_zero (i : Option (CompactRotatedCutData.source α r)) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (cover α r hr κ ρ i)) (d + 1)
      (cochainCoboundary (ZMod 2) (ambient α) d φ) = 0 := by
  cases i with
  | none =>
      change cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) (d + 1)
        (cochainCoboundary (ZMod 2) (ambient α) d φ) = 0
      rw [OriginalFirstHalfCutGammaJoinCap.coboundary_pullback, hfar]
      exact map_zero _
  | some i =>
      exact OriginalFirstHalfCutGammaJoinCap.restriction_zero_subset (ambient α) _
        (CompactRotatedCutData.source α r) (fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from
          (show SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r from hz.2).le) (d + 1) _ hproper

include hproper hfar in
theorem small_boundary_zero (q : ℕ) :
    (inclusion (ambient α) (cover α r hr κ ρ)).f ((d + 1) + q) ≫
      absoluteChain (ambient α) (d + 1) q ((d + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α) d φ) = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((ambient α).smallSingularSubcomplex (cover α r hr κ ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α) (cover α r hr κ ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact SupportedCap.cap_zero_on_simplex _ _ _ q _ rfl _
    (cover_boundary_zero α r hr κ ρ d φ hfar hproper i) σ.val hi

include hproper in
theorem component_comm (q : ℕ) :
    component α r hr κ ρ d φ hfar (q + 1) ≫
      (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).d (q + 1) q =
    (small (ambient α) (cover α r hr κ ρ)).d (d + (q + 1)) (d + q) ≫
      component α r hr κ ρ d φ hfar q := by
  have hb := LiftedCapCochainBoundary.boundary (cover α r hr κ ρ)
    (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ))
    (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ) ≫ push (source α r))
    (target_mono α r hr κ) d φ (component α r hr κ ρ d φ hfar) (fun _ => 0)
    (fun q => by simpa only [HomologicalComplex.comp_f, Category.assoc] using component_source α r hr κ ρ d φ hfar q)
    (fun q => by rw [zero_comp, small_boundary_zero α r hr κ ρ d φ hfar hproper q]) q
  simpa only [comp_zero, sub_zero] using hb

def operation : DegreeLoweringHomology.Map (small (ambient α) (cover α r hr κ ρ))
    (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)) d where
  component := component α r hr κ ρ d φ hfar
  comm := component_comm α r hr κ ρ d φ hfar hproper

end
end Finsler.FirstInputSelfCutCarrierCap
