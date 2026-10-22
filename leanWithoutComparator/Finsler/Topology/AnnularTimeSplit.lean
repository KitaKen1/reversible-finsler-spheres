module

public import Finsler.Topology.CappedTimeSplit
public import Finsler.Topology.AnnularCutComparison

/-! Apply the concrete shuffle triangle to the actual closed supported
and tested self-cut. The comparison is an explicit output chain. -/

@[expose] public section
namespace Finsler.AnnularTimeSplit

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : TopCat.{0}} (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (f : X ⊗ TopCat.I ⟶ parameters (m + 1))

def component (q : ℕ) : (chains X).X ((m + p) + q) ⟶
    (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  CappedTimeSplit.component f (m + p) (AnnularCutComparison.cut m p h hρr hr T hT) q

def comparison (q : ℕ) : (chains X).X ((m + p) + q) ⟶
    (chains (TopCat.of (SphereLoop (m + 1)))).X (q + 1) :=
  CappedTimeSplit.comparison f (m + p) (AnnularCutComparison.cut m p h hρr hr T hT) q

theorem cycle_boundary (q : ℕ) :
    ((chains X).iCycles ((m + p) + q) ≫ comparison m p h hρr hr T hT f q) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains X).iCycles ((m + p) + q) ≫
        (component m p h hρr hr T hT ((X ◁ IntervalTriangle.secondMap) ≫ f) q +
          component m p h hρr hr T hT f q +
          component m p h hρr hr T hT ((X ◁ IntervalTriangle.firstMap) ≫ f) q) :=
  CappedTimeSplit.cycle_boundary f (m + p) (AnnularCutComparison.cut m p h hρr hr T hT)
    (AnnularCutComparison.cut_boundary m p h hρr hr T hT) q

theorem full_split (q : ℕ) :
    (chains X).iCycles ((m + p) + q) ≫ component m p h hρr hr T hT f q =
      (chains X).iCycles ((m + p) + q) ≫
        component m p h hρr hr T hT ((X ◁ IntervalTriangle.firstMap) ≫ f) q +
      (chains X).iCycles ((m + p) + q) ≫
        component m p h hρr hr T hT ((X ◁ IntervalTriangle.secondMap) ≫ f) q +
      ((chains X).iCycles ((m + p) + q) ≫ comparison m p h hρr hr T hT f q) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q :=
  CappedTimeSplit.full_split f (m + p) (AnnularCutComparison.cut m p h hρr hr T hT)
    (AnnularCutComparison.cut_boundary m p h hρr hr T hT) q

end
end Finsler.AnnularTimeSplit
