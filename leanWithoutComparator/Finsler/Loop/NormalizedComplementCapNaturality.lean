module

public import Finsler.Loop.WholeSelfCutComplement
public import Finsler.Loop.FarNormalizedDiagonalSymmetry
public import Finsler.Topology.DiagonalCutSwap

/-! Complementarity is natural for the ORIGINAL normalized first Thom
cap in actual neighborhood homology. The correction is an actual
primitive supported on the SAME exterior, pulled from the ORIGINAL
far-relative normalized class. Subdivision/cap are not replaced.
This does not yet compare the tested/output cap or compute local counts. -/
@[expose] public section
namespace Finsler.NormalizedComplementCapNaturality
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCap
open Finsler.WholeSelfCutComplement
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def primitive (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (parameters (m + 1)) m :=
  cochainPullback (selfEvaluation (m + 1)) m
    (FarNormalizedDiagonalSymmetry.ambientPrimitive (m + 1) (by omega) hρ hρ2)

theorem primitive_supported (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (subspaceMap (parameters (m + 1)) (exterior (m + 1) ρ)) m
      (primitive m hm hρ hρ2) = 0 := by
  exact SupportedCapNaturality.pullback_support (selfEvaluation (m + 1))
    (exterior (m + 1) ρ) (DiagonalAvoidanceCocycle.far (m + 1) ρ)
    (by intro z hz
        change ρ ≤ distance (m + 1) z
        exact hz.le) m
    (FarNormalizedDiagonalSymmetry.ambientPrimitive (m + 1) (by omega) hρ hρ2)
    (FarNormalizedDiagonalSymmetry.ambientPrimitive_supported (m + 1) (by omega) hρ hρ2)

theorem primitive_boundary (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainCoboundary (ZMod 2) (parameters (m + 1)) m (primitive m hm hρ hρ2) =
      cochainPullback (complement (m + 1)) (m + 1)
        (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) -
      NormalizedSelfCut.cocycle (m + 1) (by omega) hρ := by
  rw [primitive, DiagonalCutSwap.pullback_coboundary]
  have hb := FarNormalizedDiagonalSymmetry.ambientPrimitive_boundary (m + 1) (by omega) hρ hρ2
  change cochainCoboundary (ZMod 2) (DiagonalCohomology.product (m + 1)) m
    (FarNormalizedDiagonalSymmetry.ambientPrimitive (m + 1) (by omega) hρ hρ2) = _ at hb
  rw [hb, DiagonalCutSwap.pullback_sub, ← SupportedCapNaturality.pullback_comp,
    ← selfEvaluation_exchange, SupportedCapNaturality.pullback_comp]
  rfl

theorem first_thom_homology_naturality (m : ℕ) (hm : 1 ≤ m) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) (hρr : ρ < r) (q : ℕ) :
    HomologicalComplex.homologyMap (SupportedCapNaturality.push (complement (m + 1))) ((m + 1) + q) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).homology q =
        (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).homology q ≫
          HomologicalComplex.homologyMap (SupportedCapNaturality.push (neighborhoodMap (m + 1) r)) q := by
  let n := m + 1
  have hn : 1 ≤ n := by omega
  have he := SupportedCapNaturality.homology_naturality (complement n)
    (exterior n ρ) (neighborhood n r) (exterior n ρ) (neighborhood n r)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hρr)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hρr)
    (exterior_mapsTo n ρ) (neighborhood_mapsTo n r) n q
    (NormalizedSelfCut.cocycle n hn hρ) (NormalizedSelfCut.cocycle_supported n hn hρ)
    (NormalizedSelfCut.cocycle_closed n hn hρ)
  have hr := SupportedCapRepresentative.homology_eq (parameters n) (exterior n ρ) (neighborhood n r)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hρr) m q
    (cochainPullback (complement n) n (NormalizedSelfCut.cocycle n hn hρ))
    (NormalizedSelfCut.cocycle n hn hρ)
    (SupportedCapNaturality.pullback_support (complement n) (exterior n ρ) (exterior n ρ)
      (exterior_mapsTo n ρ) n _ (NormalizedSelfCut.cocycle_supported n hn hρ))
    (NormalizedSelfCut.cocycle_supported n hn hρ)
    (SupportedCapNaturality.pullback_closed (complement n) n _ (NormalizedSelfCut.cocycle_closed n hn hρ))
    (NormalizedSelfCut.cocycle_closed n hn hρ)
    (primitive m hm hρ hρ2) (primitive_supported m hm hρ hρ2) (primitive_boundary m hm hρ hρ2)
  rw [hr] at he
  exact he

end
end Finsler.NormalizedComplementCapNaturality
