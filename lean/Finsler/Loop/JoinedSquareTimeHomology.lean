module

public import Finsler.Topology.JoinedRefinedComparisons

/-! The actual filtered time-square comparison descends to all input
homology in the identical retained target. The side terms vanish after
the actual refined cap; no ambient homology injection is used. -/

@[expose] public section
namespace Finsler.JoinedSquareTimeHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 500000

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

variable (hcomm : ∀ q, v (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
    (chains (TopCat.of (Outer X))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v q)
  (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1) (g ((s, 0), x)) ≤ δ)
  (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1) (g ((s, 1), x)) ≤ δ)
  (a b : DegreeLoweringHomology.Map (chains X) (chains (TopCat.of B)) (m + p))
  (ha : ∀ q, a.component q = AnnularTimeTrim.prism X ((m + p) + q) ≫
    (push (planeFace X 0)).f ((m + p) + q + 1) ≫ v q)
  (hb : ∀ q, b.component q = AnnularTimeTrim.prism X ((m + p) + q) ≫
    (push (planeFace X 1)).f ((m + p) + q + 1) ≫ v q)

include hv hcomm h₀ h₁ ha hb in
theorem homology_eq (q : ℕ) : a.homology q = b.homology q := by
  apply TimeCylinderComparison.homology_eq
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff)
    ((squareHomotopy X).toSSet.chainComplexMap coeff) (m + p) v hcomm
    (square_side_zero m p h hρr hr T hT X U g B v hv 0 h₀)
    (square_side_zero m p h hρr hr T hT X U g B v hv 1 h₁) a b
  · intro t
    exact ha t
  · intro t
    exact hb t

end
end Finsler.JoinedSquareTimeHomology
