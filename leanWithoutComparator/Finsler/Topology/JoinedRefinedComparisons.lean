module

public import Finsler.Topology.JoinedComparisonSource
public import Finsler.Topology.JoinedRefinedCut
public import Finsler.Topology.RefinedAnnularCollar
public import Finsler.Topology.CappedTimeSplit

/-! Actual triangle and double-prism boundary formulas in the genuine
filtered output complex. Source approximation preserves the diagonal
collar, so both actual side prisms vanish after the filtered lift.
Identification of different refined endpoint faces remains separate. -/

@[expose] public section
namespace Finsler.JoinedRefinedComparisons

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SelfCutThomCocycle
open Finsler.SupportedSelfCut Finsler.JoinedComparisonAdequacy Finsler.JoinedComparisonSource

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def planeFace (X : TopCat.{0}) (s : ClosedInterval) : TopCat.of (ClosedInterval × X) ⟶ TopCat.of (Outer X) :=
  AnnularTimeTrim.slice (TopCat.of (ClosedInterval × X)) s ≫ squareLift X

def squareHomotopy (X : TopCat.{0}) : TopCat.Homotopy (planeFace X 0) (planeFace X 1) :=
  TopCat.Homotopy.comp (TopCat.Homotopy.refl (squareLift X))
    (AnnularTimeTrim.cylinder (TopCat.of (ClosedInterval × X)))

theorem squareSource_eq (X : TopCat.{0}) (j : ℕ) :
    squareSource X j = AnnularTimeTrim.prism X j ≫
      ((squareHomotopy X).toSSet.chainComplexMap coeff).hom (j + 1) (j + 2) := by
  simp only [squareSource, AnnularTimeTrim.prism]
  rw [TimePrismNaturality.prism_post]
  rfl

theorem triangle_boundary (X Z : TopCat.{0}) (d : ℕ)
    (v : ∀ q, (chains (TopCat.of (Outer X))).X (d + q + 1) ⟶ (chains Z).X q)
    (hv : ∀ q, v (q + 1) ≫ (chains Z).d (q + 1) q =
      (chains (TopCat.of (Outer X))).d (d + q + 2) (d + q + 1) ≫ v q) (q : ℕ) :
    ((chains X).iCycles (d + q) ≫ triangleSource X (d + q) ≫ v (q + 1)) ≫
        (chains Z).d (q + 1) q =
      (chains X).iCycles (d + q) ≫
        (CappedTimeSplit.component ((X ◁ IntervalTriangle.secondMap) ≫ triangleLift X) d v q +
          CappedTimeSplit.component (triangleLift X) d v q +
          CappedTimeSplit.component ((X ◁ IntervalTriangle.firstMap) ≫ triangleLift X) d v q) := by
  simpa only [triangleSource, CappedTimeSplit.comparison, Category.assoc] using
    CappedTimeSplit.cycle_boundary (triangleLift X) d v hv q

variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (X : TopCat.{0}) {ι : Type*} (U : ι → Set (Outer X))
  (g : TopCat.of (Outer X) ⟶ parameters (m + 1)) (B : Set (SphereLoop (m + 1)))
  (v : ∀ q, (chains (TopCat.of (Outer X))).X ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q)
  (hv : ∀ q, v q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
    (TauCeti.singularSmallApprox (X := TopCat.of (Outer X)) coeff U).f ((m + p) + q + 1) ≫
      (push g).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)

include hv

theorem square_side_zero (t : ClosedInterval)
    (ht : ∀ (s : ClosedInterval) (x : X), distance (m + 1) (g ((s, t), x)) ≤ δ) (q : ℕ) :
    (push (AnnularTimeTrim.slice X t)).f ((m + p) + q) ≫
      (((squareHomotopy X).toSSet.chainComplexMap coeff).hom ((m + p) + q) ((m + p) + q + 1) ≫ v q) = 0 := by
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  apply RefinedAnnularCollar.filtered_prism_zero m p h hρr hr T hT U g B v hv
  intro z
  exact ht z.2.down z.1

theorem square_boundary
    (hcomm : ∀ q, v (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains (TopCat.of (Outer X))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v q)
    (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1) (g ((s, 0), x)) ≤ δ)
    (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1) (g ((s, 1), x)) ≤ δ) (q : ℕ) :
    ((chains X).iCycles ((m + p) + q) ≫ AnnularTimeTrim.prism X ((m + p) + q)) ≫
      (((push (planeFace X 0)).f ((m + p) + q + 1) -
        (push (planeFace X 1)).f ((m + p) + q + 1)) ≫ v q) =
      ((chains X).iCycles ((m + p) + q) ≫ squareSource X ((m + p) + q) ≫ v (q + 1)) ≫
        (chains (TopCat.of B)).d (q + 1) q := by
  have hs₀ := square_side_zero m p h hρr hr T hT X U g B v hv 0 h₀
  have hs₁ := square_side_zero m p h hρr hr T hT X U g B v hv 1 h₁
  have he := TimeCylinderComparison.cycle_boundary
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff)
    ((squareHomotopy X).toSSet.chainComplexMap coeff) (m + p) v hcomm hs₀ hs₁ q
  simpa only [squareSource_eq, AnnularTimeTrim.prism, Category.assoc, push, chains] using he

end
end Finsler.JoinedRefinedComparisons
