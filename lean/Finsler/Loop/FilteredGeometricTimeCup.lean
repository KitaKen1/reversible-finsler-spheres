module

public import Finsler.Topology.SelfCutShuffle
public import Finsler.Topology.RelativeCapDual
public import Finsler.Loop.DegreeLoweringCochainPullback

/-! Independently defined filtered time-cut cup cochains: actual split
pullbacks, ordinary cup, tested small approximation, supported Thom cut
and genuine time rectangle. Their canonical D_T pairing is proved. -/

@[expose] public section
namespace Finsler.FilteredGeometricTimeCup
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def splitCup {n : ℕ} (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (a : ℝ) (p q : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) q) :
    singularCochainGroup (ZMod 2) (FilteredTestedCap.space F r a) (p + q) :=
  cochainCup p q (FilteredTestedCap.cochain F hr a p T)
    (cochainPullback (FilteredTestedCap.retainedMap F hr a) q B)

theorem tested_cap_dual {n : ℕ} (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε) (p q : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
      (SelfCutOscillation.short F L)) p T = 0)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) q) :
    (FilteredTestedCap.operation F hr hε hrr p T hT hshort (a := a)).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F (a - L + 3 * ε)))).f q ≫ B =
    (TauCeti.singularSmallApprox coeff (FilteredTestedCap.cover F hr a ε)).f (p + q) ≫
      splitCup F hr a p q T B := by
  rw [← Category.assoc, FilteredTestedCap.operation_inclusion]
  simp only [Category.assoc]
  change (TauCeti.singularSmallApprox coeff (FilteredTestedCap.cover F hr a ε)).f (p + q) ≫
      (absoluteChain (FilteredTestedCap.space F r a) p q (p + q) rfl
        (FilteredTestedCap.cochain F hr a p T) ≫
        cochainPullback (FilteredTestedCap.retainedMap F hr a) q B) = _
  rw [RelativeCapDual.absolute_chain_dual]
  rfl

def cochain (m p : ℕ) (F : ReversibleMetric (m + 1)) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (a ε : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (q : ℕ) (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q) :
    singularCochainGroup (ZMod 2) (TopCat.of (SelfCutOscillation.short F a)) ((m + p) + q) :=
  TimeShuffleComparison.rectangle (FilteredPrismSelfCut.cylinder F a) ((m + p) + q) ≫
    eqToHom (congrArg (chains (FilteredPrismSelfCut.domain F a)).X
      (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)) ≫
    (FilteredPrismSelfCut.firstThom (by omega) F a hρ hρr).component (p + q) ≫
    (push (FilteredPrismSelfCut.toIncoming F r a)).f (p + q) ≫
    (TauCeti.singularSmallApprox coeff (FilteredTestedCap.cover F hr a ε)).f (p + q) ≫
    splitCup F hr a p q T B

theorem operation_dual (m p : ℕ) (F : ReversibleMetric (m + 1)) {ρ r ε a L : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hε : 0 < ε)
    (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0)
    (q : ℕ) (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q) :
    (FilteredPrismSelfCut.operation m p F hρ hρr hr hε hrr T hT hshort (a := a)).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))).f q ≫ B =
    cochain m p F hρ hρr hr a ε T q B := by
  rw [SelfCutShuffle.filtered_operation_eq_shuffle, FilteredPrismSelfCut.indexedCut,
    FilteredPrismSelfCut.chainCut, cochain]
  change (TimeShuffleComparison.rectangle (FilteredPrismSelfCut.cylinder F a) ((m + p) + q) ≫
    eqToHom (congrArg (chains (FilteredPrismSelfCut.domain F a)).X
      (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)) ≫
    ((FilteredPrismSelfCut.firstThom (by omega) F a hρ hρr).component (p + q) ≫
      (push (FilteredPrismSelfCut.toIncoming F r a)).f (p + q)) ≫
    (FilteredTestedCap.operation F hr hε hrr p T hT hshort).component q) ≫ _ = _
  simp only [Category.assoc]
  rw [tested_cap_dual F hr hε hrr p q T hT hshort B]

def canonicalCochain (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε : ℝ}
    (hε : 0 < ε) (a : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (q : ℕ) (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q) :=
  cochain m p F (half_pos (SelfCutLengthControl.radius_spec F hε).1)
    (half_lt_self (SelfCutLengthControl.radius_spec F hε).1) (SelfCutLengthControl.radius_spec F hε).2.1 a ε T q B

theorem canonical_dual (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ}
    (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0)
    (q : ℕ) (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q) :
    (FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))).f q ≫ B =
    canonicalCochain m p F hε a T q B :=
  operation_dual m p F (half_pos (SelfCutLengthControl.radius_spec F hε).1)
    (half_lt_self (SelfCutLengthControl.radius_spec F hε).1) (SelfCutLengthControl.radius_spec F hε).2.1
    hε le_rfl T hT hshort q B

end
end Finsler.FilteredGeometricTimeCup
