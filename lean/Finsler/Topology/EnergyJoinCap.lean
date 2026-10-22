module

public import Finsler.Topology.EnergyFilteredJoin
public import Finsler.Topology.JoinThomPrimitive
public import Finsler.Topology.NearFarCapSelf

/-! Single supported Thom and correction caps on the original energy-cut
inputs themselves. Their comparison chains lie in the actual energy-input
near domain, so the verified energy-output homotopy applies directly. -/

@[expose] public section
namespace Finsler.EnergyJoinCap

open CategoryTheory AlgebraicTopology HomologicalComplex SphereOddDegree MonoidalCategory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SobolevReflectionAction Finsler.CompactH1Alignment
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity Finsler.PairDistanceCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {n : ℕ} (F : ReversibleMetric n)

def basePoint (p : ℝ) (u : energyCut F p) : Ambient n := basepoint u.val

theorem basePoint_continuous (p : ℝ) : Continuous (basePoint F p) :=
  H1AlignmentHomotopy.basepoint_continuous.comp continuous_subtype_val

variable (p q : ℝ)

theorem pullback_far_zero (k : ℕ) (ρ : ℝ)
    (φ : singularCochainGroup (ZMod 2)
      (SupportedFilteredJoinComparison.lengthSpace F p ⊗ SupportedFilteredJoinComparison.lengthSpace F q) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap
      (SupportedFilteredJoinComparison.lengthSpace F p ⊗ SupportedFilteredJoinComparison.lengthSpace F q)
      (NearFarCapComparison.far (SupportedFilteredJoinComparison.basePoint F p)
        (SupportedFilteredJoinComparison.basePoint F q) ρ)) k φ = 0) :
    cochainPullback (SupportedCap.subspaceMap (EnergyFilteredJoin.inputSpace F p q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)) k
      (cochainPullback (EnergyFilteredJoin.inputMap F p q) k φ) = 0 :=
  pullback_support (EnergyFilteredJoin.inputMap F p q)
    (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)
    (NearFarCapComparison.far (SupportedFilteredJoinComparison.basePoint F p)
      (SupportedFilteredJoinComparison.basePoint F q) ρ)
    (fun _ hz => hz) k φ hφ

def cocycle (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (EnergyFilteredJoin.inputSpace F p q) n :=
  cochainPullback (EnergyFilteredJoin.inputMap F p q) n (JoinThomCocycle.cocycle F p q hn hρ)

theorem cocycle_far_zero (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (EnergyFilteredJoin.inputSpace F p q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)) n
      (cocycle F p q hn hρ) = 0 :=
  pullback_far_zero F p q n ρ _ (JoinThomCocycle.cocycle_far_zero F p q hn hρ)

def primitive (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (EnergyFilteredJoin.inputSpace F p q) (n - 1) :=
  cochainPullback (EnergyFilteredJoin.inputMap F p q) (n - 1)
    (JoinThomPrimitive.primitive F p q hn hρ hρ2)

theorem primitive_far_zero (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (SupportedCap.subspaceMap (EnergyFilteredJoin.inputSpace F p q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q) ρ)) (n - 1)
      (primitive F p q hn hρ hρ2) = 0 :=
  pullback_far_zero F p q (n - 1) ρ _ (JoinThomPrimitive.primitive_far_zero F p q hn hρ hρ2)

variable (hp : 0 ≤ p) (hq : 0 ≤ q) {ε : ℝ} (hε : 0 < ε)

theorem cap_factor (i j k t : ℕ) (h : k + t = i + j + 1)
    (σ : ((TopCat.of (energyCut F p)).smallSingularSubcomplex
      (cover (basePoint F p) (SupportedFilteredJoinComparison.witnessRadius F p q hp hq hε / 4)) : SSet) _⦋i⦌)
    (τ : ((TopCat.of (energyCut F q)).smallSingularSubcomplex
      (cover (basePoint F q) (SupportedFilteredJoinComparison.witnessRadius F p q hp hq hε / 4)) : SSet) _⦋j⦌)
    (φ : singularCochainGroup (ZMod 2) (EnergyFilteredJoin.inputSpace F p q) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (EnergyFilteredJoin.inputSpace F p q)
      (NearFarCapComparison.far (basePoint F p) (basePoint F q)
        (SupportedFilteredJoinComparison.witnessRadius F p q hp hq hε))) k φ = 0) :
    ∃ d : coeff ⟶ (chains (TopCat.of (EnergyFilteredJoin.domain F p q hp hq hε))).X t,
      d ≫ (push (SupportedCap.subspaceMap (EnergyFilteredJoin.inputSpace F p q)
        (EnergyFilteredJoin.domain F p q hp hq hε))).f t =
      NearFarCapComparison.prism (basePoint F p) (basePoint_continuous F p)
        (basePoint F q) (basePoint_continuous F q)
        (SupportedFilteredJoinComparison.witnessRadius F p q hp hq hε)
        (SupportedFilteredJoinComparison.witnessRadius_pos F p q hp hq hε) i j σ.val τ.val ≫
          absoluteChain (EnergyFilteredJoin.inputSpace F p q) k t (i + j + 1) h φ := by
  apply NearFarCapSelf.cap_factor
    (X := TopCat.of (energyCut F p)) (Y := TopCat.of (energyCut F q))
    (basePoint F p) (basePoint_continuous F p) (basePoint F q) (basePoint_continuous F q)
    (SupportedFilteredJoinComparison.witnessRadius F p q hp hq hε)
    (SupportedFilteredJoinComparison.witnessRadius_pos F p q hp hq hε)
    (EnergyFilteredJoin.domain F p q hp hq hε) ?_ i j k t h σ τ φ hφ
  intro u v hnear
  change dist (basepoint u.val) (basepoint v.val) < FilteredOriginalJoin.radius F p q hp hq hε
  change dist (basepoint u.val) (basepoint v.val) <
    2 * (FilteredOriginalJoin.radius F p q hp hq hε / 2) at hnear
  linarith

end
end Finsler.EnergyJoinCap
