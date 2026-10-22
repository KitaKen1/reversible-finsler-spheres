module

public import Finsler.Loop.FirstInputSelfCutCarrierCap
import all Finsler.Loop.OriginalFirstHalfCutGammaJoinCap

/-! A literal cochain zero on the actual proper cut and far regions
has zero cap on the genuine first-input cover. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutLocalCochainZero

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ ρ : ℝ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (ambient α) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) d φ = 0)
  (hproper : cochainPullback (source α r) d φ = 0)

include hfar hproper in
theorem cover_zero (i : Option (CompactRotatedCutData.source α r)) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (cover α r hr κ ρ i)) d φ = 0 := by
  cases i with
  | none => exact hfar
  | some i =>
      exact OriginalFirstHalfCutGammaJoinCap.restriction_zero_subset (ambient α) _
        (CompactRotatedCutData.source α r) (fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from
          (show SupportedSelfCut.distance (m + 1) (z.1, α z.2) < r from hz.2).le) d φ hproper

include hfar hproper in
theorem small_cap_zero (q : ℕ) :
    (inclusion (ambient α) (cover α r hr κ ρ)).f (d + q) ≫
      absoluteChain (ambient α) d q (d + q) rfl φ = 0 := by
  apply SSet.chainComplex_hom_ext (X := ((ambient α).smallSingularSubcomplex (cover α r hr κ ρ) : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α) (cover α r hr κ ρ) σ.val).mp σ.property
  simp only [SmallChainCarrier.inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact SupportedCap.cap_zero_on_simplex _ _ d q _ rfl φ
    (cover_zero α r hr κ ρ d φ hfar hproper i) σ.val hi

end
end Finsler.FirstInputSelfCutLocalCochainZero
