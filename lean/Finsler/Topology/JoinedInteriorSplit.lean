module

public import Finsler.Topology.JoinedHalfTrim

/-! The actual original joined-loop operation splits into two common
interior-time operations plus one explicit sum of triangle and two
cylinder comparison chains. Filtered carrier estimates remain separate. -/

@[expose] public section
namespace Finsler.JoinedInteriorSplit

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section
variable {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (u : C(X, H1JoinContinuity.composable (m + 1)))
  (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)

def comparison (q : ℕ) : (chains (TopCat.of X)).X ((m + p) + q) ⟶
    (chains (TopCat.of (SphereLoop (m + 1)))).X (q + 1) :=
  AnnularTimeSplit.comparison m p h hρr hr T hT (JoinedTimeSplit.fullCylinder u) q +
    CylinderTimeTrim.comparison m p h hρr hr T hT (JoinedHalfCollars.firstFamily u) a ha ha1 q +
    CylinderTimeTrim.comparison m p h hρr hr T hT (JoinedHalfCollars.secondFamily u) a ha ha1 q

theorem cycle_boundary
    (hf₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (CylinderTimeTrim.homotopy (JoinedHalfCollars.firstFamily u) a ha ha1 (s, (0, x))) ≤ δ)
    (hf₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (CylinderTimeTrim.homotopy (JoinedHalfCollars.firstFamily u) a ha ha1 (s, (1, x))) ≤ δ)
    (hs₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (CylinderTimeTrim.homotopy (JoinedHalfCollars.secondFamily u) a ha ha1 (s, (0, x))) ≤ δ)
    (hs₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (CylinderTimeTrim.homotopy (JoinedHalfCollars.secondFamily u) a ha ha1 (s, (1, x))) ≤ δ) (q : ℕ) :
    (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
      ((push (TopCat.ofHom (JoinedTimeSplit.loopFamily u))).f ((m + p) + q) ≫
        (AnnularCutComparison.operation m p h hρr hr T hT).component q) =
      (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        AnnularTimeTrim.component m p h hρr hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1) q +
      (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        AnnularTimeTrim.component m p h hρr hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1) q +
      ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫ comparison m p h hρr hr T hT u a ha ha1 q) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q := by
  have hf := CylinderTimeTrim.cycle_boundary m p h hρr hr T hT
    (JoinedHalfCollars.firstFamily u) a ha ha1 hf₀ hf₁ q
  have hs := CylinderTimeTrim.cycle_boundary m p h hρr hr T hT
    (JoinedHalfCollars.secondFamily u) a ha ha1 hs₀ hs₁ q
  rw [Preadditive.comp_sub] at hf hs
  have hf' := sub_eq_iff_eq_add.mp hf
  have hs' := sub_eq_iff_eq_add.mp hs
  rw [JoinedTimeSplit.full_split, hf', hs']
  simp only [comparison, Preadditive.comp_add, Preadditive.add_comp]
  abel

end
end
end Finsler.JoinedInteriorSplit
