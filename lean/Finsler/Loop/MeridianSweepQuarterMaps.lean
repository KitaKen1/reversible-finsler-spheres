module

public import Finsler.Loop.MeridianQuarterHomotopies
public import Finsler.Loop.MeridianLoopQuarterPaths
public import Finsler.Loop.ContinuousLoopSweep

/-! Tie the ORIGINAL loop-evaluation sweep to the four genuine
meridian homotopies. The four-quarter identity includes the actual
triangle comparison boundary; the original sweep is not redefined. -/

@[expose] public section
namespace Finsler.MeridianSweepQuarterMaps
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.MeridianQuarterHomotopies
open Finsler.RationalSphereArc
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1200000

def fullH {n : ℕ} (P : Sphere n) (v₀ : equator P) :=
  (ContinuousLoopSweep.evaluationHomotopy n).comp (TopCat.Homotopy.refl (ordinary P v₀))

def fullMap {n : ℕ} (P : Sphere n) (v₀ : equator P) : parameters P ⊗ TopCat.I ⟶ BorelEvaluation.sphere n :=
  (fullH P v₀).h

theorem fullMap_apply {n : ℕ} (P : Sphere n) (v₀ : equator P) (z : parameters P ⊗ TopCat.I) :
    fullMap P v₀ z = loop P v₀ z.1 z.2.down :=
  ClosedPathCircle.circle_coe (ClosedPathCircle.ofPath (loop P v₀ z.1)) z.2.down

theorem first_first {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    UncappedTimeSplit.first (UncappedTimeSplit.first (fullMap P v₀)) = (outgoingH P).h := by
  ext z : 1
  change fullMap P v₀ (z.1, IntervalTriangle.firstMap (IntervalTriangle.firstMap z.2)) = _
  rw [fullMap_apply]
  change loop P v₀ z.1 ((IntervalTriangle.firstMap (IntervalTriangle.firstMap z.2)).down) =
    arc (outgoing P z.1) z.2.down
  rw [← Path.extend_apply _ (IntervalTriangle.firstMap (IntervalTriangle.firstMap z.2)).down.property]
  change (loop P v₀ z.1).extend ((z.2.down : ℝ) / 2 / 2) = _
  convert MeridianLoopQuarterPaths.first P v₀ z.1 z.2.down using 1
  congr 1
  ring

theorem second_first {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    UncappedTimeSplit.second (UncappedTimeSplit.first (fullMap P v₀)) = (incomingH P).h := by
  ext z : 1
  change fullMap P v₀ (z.1, IntervalTriangle.firstMap (IntervalTriangle.secondMap z.2)) = _
  rw [fullMap_apply]
  change loop P v₀ z.1 ((IntervalTriangle.firstMap (IntervalTriangle.secondMap z.2)).down) =
    arc (incoming P z.1) z.2.down
  rw [← Path.extend_apply _ (IntervalTriangle.firstMap (IntervalTriangle.secondMap z.2)).down.property]
  change (loop P v₀ z.1).extend ((1 + (z.2.down : ℝ)) / 2 / 2) = _
  convert MeridianLoopQuarterPaths.second P v₀ z.1 z.2.down using 1
  congr 1
  ring

theorem first_second {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    UncappedTimeSplit.first (UncappedTimeSplit.second (fullMap P v₀)) = (returnIncomingH P v₀).h := by
  ext z : 1
  change fullMap P v₀ (z.1, IntervalTriangle.secondMap (IntervalTriangle.firstMap z.2)) = _
  rw [fullMap_apply]
  change loop P v₀ z.1 ((IntervalTriangle.secondMap (IntervalTriangle.firstMap z.2)).down) =
    (arc (incoming P v₀)).symm z.2.down
  rw [← Path.extend_apply _ (IntervalTriangle.secondMap (IntervalTriangle.firstMap z.2)).down.property]
  change (loop P v₀ z.1).extend ((1 + (z.2.down : ℝ) / 2) / 2) = _
  convert MeridianLoopQuarterPaths.third P v₀ z.1 z.2.down using 1
  congr 1
  ring

theorem second_second {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    UncappedTimeSplit.second (UncappedTimeSplit.second (fullMap P v₀)) = (returnOutgoingH P v₀).h := by
  ext z : 1
  change fullMap P v₀ (z.1, IntervalTriangle.secondMap (IntervalTriangle.secondMap z.2)) = _
  rw [fullMap_apply]
  change loop P v₀ z.1 ((IntervalTriangle.secondMap (IntervalTriangle.secondMap z.2)).down) =
    (arc (outgoing P v₀)).symm z.2.down
  rw [← Path.extend_apply _ (IntervalTriangle.secondMap (IntervalTriangle.secondMap z.2)).down.property]
  change (loop P v₀ z.1).extend ((1 + (1 + (z.2.down : ℝ)) / 2) / 2) = _
  convert MeridianLoopQuarterPaths.fourth P v₀ z.1 z.2.down using 1
  congr 1
  ring

theorem original_prism {n : ℕ} (P : Sphere n) (v₀ : equator P) (j : ℕ) :
    (push (ordinary P v₀)).f j ≫ (ContinuousLoopSweep.chainHomotopy n).hom j (j + 1) =
      UncappedTimeSplit.component (fullMap P v₀) j := by
  rw [fullMap, UncappedTimeSplit.prism_component]
  exact TimePrismNaturality.prism_pre (ContinuousLoopSweep.evaluationHomotopy n) (ordinary P v₀) j

theorem original_four_split {n : ℕ} (P : Sphere n) (v₀ : equator P) (j : ℕ) :
    (chains (parameters P)).iCycles j ≫
      ((push (ordinary P v₀)).f j ≫ (ContinuousLoopSweep.chainHomotopy n).hom j (j + 1)) =
    (chains (parameters P)).iCycles j ≫ ((outgoingH P).toSSet.chainComplexMap coeff).hom j (j + 1) +
    (chains (parameters P)).iCycles j ≫ ((incomingH P).toSSet.chainComplexMap coeff).hom j (j + 1) +
    (chains (parameters P)).iCycles j ≫ ((returnIncomingH P v₀).toSSet.chainComplexMap coeff).hom j (j + 1) +
    (chains (parameters P)).iCycles j ≫ ((returnOutgoingH P v₀).toSSet.chainComplexMap coeff).hom j (j + 1) +
    ((chains (parameters P)).iCycles j ≫ UncappedTimeSplit.fourComparison (fullMap P v₀) j) ≫
      (chains (BorelEvaluation.sphere n)).d (j + 2) (j + 1) := by
  rw [original_prism, UncappedTimeSplit.four_split, first_first, second_first, first_second, second_second,
    UncappedTimeSplit.prism_component, UncappedTimeSplit.prism_component,
    UncappedTimeSplit.prism_component, UncappedTimeSplit.prism_component]

end
end Finsler.MeridianSweepQuarterMaps
