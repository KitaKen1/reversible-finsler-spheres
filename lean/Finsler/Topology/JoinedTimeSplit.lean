module

public import Finsler.Topology.AnnularTimeSplit
public import Finsler.Topology.JoinedHalfCollars
public import Finsler.Topology.AnnularTimeTrim

/-! The original annular operation on a genuine half-joined H1 loop family
is the sum of its actual first/second time cylinders plus an explicit
boundary. This does not yet supply filtered comparison carrier estimates. -/

@[expose] public section
namespace Finsler.JoinedTimeSplit

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : Type} [TopologicalSpace X] {n : ℕ}

def loopFamily (u : C(X, H1JoinContinuity.composable n)) : C(X, SphereLoop n) :=
  ⟨fun x => JoinedHalfCollars.pairJoin (u x), JoinedHalfCollars.continuous_pairJoin.comp u.continuous⟩

def fullCylinder (u : C(X, H1JoinContinuity.composable n)) :
    TopCat.of X ⊗ TopCat.I ⟶ parameters n :=
  (AnnularTimeTrim.cylinder (TopCat.of X)).h ≫ AnnularSelfCut.familyMap (loopFamily u)

theorem first_cylinder (u : C(X, H1JoinContinuity.composable n)) :
    ((TopCat.of X ◁ IntervalTriangle.firstMap) ≫ fullCylinder u) =
      (AnnularTimeTrim.cylinder (TopCat.of X)).h ≫ JoinedHalfCollars.firstFamily u := by
  ext z : 1
  rfl

theorem second_cylinder (u : C(X, H1JoinContinuity.composable n)) :
    ((TopCat.of X ◁ IntervalTriangle.secondMap) ≫ fullCylinder u) =
      (AnnularTimeTrim.cylinder (TopCat.of X)).h ≫ JoinedHalfCollars.secondFamily u := by
  ext z : 1
  rfl

section
variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem prism_component
    (f : TopCat.of (ClosedInterval × X) ⟶ parameters (m + 1)) (q : ℕ) :
    AnnularTimeSplit.component m p h hρr hr T hT
        ((AnnularTimeTrim.cylinder (TopCat.of X)).h ≫ f) q =
      AnnularTimeTrim.component m p h hρr hr T hT f q := by
  have hi : TimeTriangleSplit.interval (TopCat.of X) ((m + p) + q) ≫
      (push (AnnularTimeTrim.cylinder (TopCat.of X)).h).f ((m + p) + q + 1) =
      AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) :=
    TimeShuffleComparison.rectangle_eq_prism (AnnularTimeTrim.cylinder (TopCat.of X)) _
  calc
    _ = (TimeTriangleSplit.interval (TopCat.of X) ((m + p) + q) ≫
        (push (AnnularTimeTrim.cylinder (TopCat.of X)).h).f ((m + p) + q + 1)) ≫
          (push f).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q := by
      simp only [AnnularTimeSplit.component, CappedTimeSplit.component, push_comp,
        HomologicalComplex.comp_f, Category.assoc]
    _ = _ := by rw [hi]; rfl

theorem full_component (u : C(X, H1JoinContinuity.composable (m + 1))) (q : ℕ) :
    AnnularTimeSplit.component m p h hρr hr T hT (fullCylinder u) q =
      (push (TopCat.ofHom (loopFamily u))).f ((m + p) + q) ≫
        (AnnularCutComparison.operation m p h hρr hr T hT).component q := by
  unfold fullCylinder
  rw [prism_component, AnnularTimeTrim.full_component]

theorem full_split (u : C(X, H1JoinContinuity.composable (m + 1))) (q : ℕ) :
    (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        ((push (TopCat.ofHom (loopFamily u))).f ((m + p) + q) ≫
          (AnnularCutComparison.operation m p h hρr hr T hT).component q) =
      (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        AnnularTimeTrim.component m p h hρr hr T hT (JoinedHalfCollars.firstFamily u) q +
      (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        AnnularTimeTrim.component m p h hρr hr T hT (JoinedHalfCollars.secondFamily u) q +
      ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        AnnularTimeSplit.comparison m p h hρr hr T hT (fullCylinder u) q) ≫
          (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q := by
  have hb := AnnularTimeSplit.full_split m p h hρr hr T hT (fullCylinder u) q
  rw [full_component, first_cylinder, second_cylinder, prism_component, prism_component] at hb
  exact hb

end
end
end Finsler.JoinedTimeSplit
