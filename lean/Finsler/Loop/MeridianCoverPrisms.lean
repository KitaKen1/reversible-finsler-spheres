module

public import Finsler.Loop.MeridianSweepQuarterMaps
public import Finsler.Loop.HomotopyRangeRestriction
public import Finsler.Topology.TimePrismComparison

/-! The four actual meridian prisms restricted to the ACTUAL
antipodal open sets. Their upper/lower sums have only the varying
and fixed equator endpoints, and recover the ORIGINAL sweep modulo
the explicit three-triangle boundary. -/

@[expose] public section
namespace Finsler.MeridianCoverPrisms
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.MeridianQuarterHomotopies
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1400000

def upperFirst {n : ℕ} (P : Sphere n) :=
  HomotopyRangeRestriction.restriction (outgoingH P) (upper P) (outgoing_upper P)

def lowerSecond {n : ℕ} (P : Sphere n) :=
  HomotopyRangeRestriction.restriction (incomingH P) (lower P) (incoming_lower P)

def lowerThird {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  HomotopyRangeRestriction.restriction (returnIncomingH P v₀) (lower P) (returnIncoming_lower P v₀)

def upperFourth {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  HomotopyRangeRestriction.restriction (returnOutgoingH P v₀) (upper P) (returnOutgoing_upper P v₀)

def upperHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  ((upperFourth P v₀).toSSet.chainComplexMap coeff).trans ((upperFirst P).toSSet.chainComplexMap coeff)

def lowerHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  ((lowerSecond P).toSSet.chainComplexMap coeff).trans ((lowerThird P v₀).toSSet.chainComplexMap coeff)

def upperChain {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  (upperHomotopy P v₀).hom q (q + 1)

def lowerChain {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  (lowerHomotopy P v₀).hom q (q + 1)

theorem upper_include {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    upperChain P v₀ q ≫ (push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (upper P))).f (q + 1) =
      ((returnOutgoingH P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) +
        ((outgoingH P).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  change ((((upperFourth P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) +
    ((upperFirst P).toSSet.chainComplexMap coeff).hom q (q + 1)) ≫ _) = _
  rw [Preadditive.add_comp]
  rw [upperFourth, upperFirst, HomotopyRangeRestriction.include_prism, HomotopyRangeRestriction.include_prism]

theorem lower_include {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    lowerChain P v₀ q ≫ (push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (lower P))).f (q + 1) =
      ((incomingH P).toSSet.chainComplexMap coeff).hom q (q + 1) +
        ((returnIncomingH P v₀).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  change ((((lowerSecond P).toSSet.chainComplexMap coeff).hom q (q + 1) +
    ((lowerThird P v₀).toSSet.chainComplexMap coeff).hom q (q + 1)) ≫ _) = _
  rw [Preadditive.add_comp]
  rw [lowerSecond, lowerThird, HomotopyRangeRestriction.include_prism, HomotopyRangeRestriction.include_prism]

theorem upper_boundary {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    ((chains (parameters P)).iCycles q ≫ upperChain P v₀ q) ≫ (chains (TopCat.of (upper P))).d (q + 1) q =
      (chains (parameters P)).iCycles q ≫
        ((push (HomotopyRangeRestriction.start (returnOutgoingH P v₀) (upper P) (returnOutgoing_upper P v₀))).f q -
          (push (HomotopyRangeRestriction.finish (outgoingH P) (upper P) (outgoing_upper P))).f q) :=
  TimePrismComparison.cycles_prism_boundary (upperHomotopy P v₀) q

theorem lower_boundary {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    ((chains (parameters P)).iCycles q ≫ lowerChain P v₀ q) ≫ (chains (TopCat.of (lower P))).d (q + 1) q =
      (chains (parameters P)).iCycles q ≫
        ((push (HomotopyRangeRestriction.start (incomingH P) (lower P) (incoming_lower P))).f q -
          (push (HomotopyRangeRestriction.finish (returnIncomingH P v₀) (lower P) (returnIncoming_lower P v₀))).f q) :=
  TimePrismComparison.cycles_prism_boundary (lowerHomotopy P v₀) q

theorem original_cover_split {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    (chains (parameters P)).iCycles q ≫
      ((push (ordinary P v₀)).f q ≫ (ContinuousLoopSweep.chainHomotopy n).hom q (q + 1)) =
    (chains (parameters P)).iCycles q ≫
      (upperChain P v₀ q ≫ (push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (upper P))).f (q + 1)) +
    (chains (parameters P)).iCycles q ≫
      (lowerChain P v₀ q ≫ (push (SupportedCap.subspaceMap (BorelEvaluation.sphere n) (lower P))).f (q + 1)) +
    ((chains (parameters P)).iCycles q ≫ UncappedTimeSplit.fourComparison
      (MeridianSweepQuarterMaps.fullMap P v₀) q) ≫ (chains (BorelEvaluation.sphere n)).d (q + 2) (q + 1) := by
  rw [MeridianSweepQuarterMaps.original_four_split, upper_include, lower_include]
  simp only [Preadditive.comp_add]
  abel

end
end Finsler.MeridianCoverPrisms
