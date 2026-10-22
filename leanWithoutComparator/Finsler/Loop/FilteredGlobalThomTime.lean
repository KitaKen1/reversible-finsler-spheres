module

public import Finsler.Loop.CylinderSupportedThomNaturality
public import Finsler.Loop.FilteredThomSupportRadius
public import Finsler.Loop.GlobalThomTime

/-! The genuine first Thom TIME commutes with forgetting a strict
length bound. Both chosen small-chain models are compared over an
actual common cylinder cover; their endpoints vanish on the diagonal. -/

@[expose] public section
namespace Finsler.FilteredGlobalThomTime
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

def endpointCarrier (n : ℕ) : Set (parameters n) :=
  selfEvaluation n ⁻¹' DiagonalAvoidanceCocycle.diagonal n

theorem cocycle_endpoint (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (endpointCarrier (m + 1)))
      (m + 1) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0 := by
  rw [NormalizedSelfCut.cocycle, ← pullback_comp]
  exact NormalizedDiagonalCocycle.pullback_zero_of_diagonal (by omega) hρ _ (fun z => z.property)

def nearMap (m : ℕ) (F : ReversibleMetric (m + 1)) (a r : ℝ) :
    TopCat.of (FilteredPrismSelfCut.near F a r) ⟶
      TopCat.of (SupportedSelfCut.neighborhood (m + 1) r) :=
  FilteredPrismSelfCut.toIncoming F r a ≫ FilteredTestedCap.inclusion F r a

theorem homology (m : ℕ) (F : ReversibleMetric (m + 1)) (a : ℝ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ) :
    (FilteredThomSupportRadius.operation m F a hρ hρr).homology q ≫
      HomologicalComplex.homologyMap (push (nearMap m F a r)) q =
    HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F a))) (m + q) ≫
      (GlobalThomTime.operation m hρ hρr).homology q := by
  exact CylinderSupportedThomNaturality.homology_naturality
    (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F a))
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) m (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ)
    (endpointCarrier (m + 1)) (cocycle_endpoint m hρ)
    (fun _ => rfl) (fun u => (sphereRepresentative_endpoints u).symm) q

end
end Finsler.FilteredGlobalThomTime
