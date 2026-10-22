module

public import Finsler.Topology.TimeTriangleSplit
public import Finsler.Topology.SmallCrossCarrier
public import Finsler.Topology.CarrierSubspaceFactor
public import Finsler.Topology.JoinedTimeSplit
public import Finsler.Topology.JoinLengthComparison

/-! The actual shuffle triangle keeps both parent simplex images. Its
actual joined-loop image factors through the original input-length cut.
This is a pre-cut carrier bound; the retained output bound is separate. -/

@[expose] public section
namespace Finsler.TimeTriangleCarrier

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SmallRectangleShuffle Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SobolevLength
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem right_simplex_parent (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ SingularChainCross.right X Y p q τ ∈
      supported (X ⊗ Y) (rectangles (parentFamily.{1} σ) (parentFamily.{1} τ)) (p + q) := by
  have hc := SmallCrossCarrier.cross_parent p q σ τ
  rw [SingularChainCross.component_simplex, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp] at hc
  rw [SingularChainCross.right_simplex]
  exact hc

theorem triangle_parent (X : TopCat.{0}) (j : ℕ) (σ : TopCat.toSSet.obj X _⦋j⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ TimeTriangleSplit.triangle X j ∈
      supported (X ⊗ TopCat.I)
        (rectangles (parentFamily.{1} σ) (parentFamily.{1} IntervalTriangle.triangle)) (j + 2) :=
  right_simplex_parent X TopCat.I j 2 σ IntervalTriangle.triangle

theorem triangle_push_factor {X Z : TopCat.{0}} (j : ℕ)
    (σ : TopCat.toSSet.obj X _⦋j⦌) (f : X ⊗ TopCat.I ⟶ Z) (B : Set Z)
    (hf : ∀ x ∈ Set.range (X.toSSetObjEquiv _ σ),
      ∀ t ∈ Set.range (TopCat.I.toSSetObjEquiv _ IntervalTriangle.triangle), f (x, t) ∈ B) :
    ∃ c : coeff ⟶ (chains (TopCat.of B)).X (j + 2),
      c ≫ (push (SupportedCap.subspaceMap Z B)).f (j + 2) =
        ((TopCat.toSSet.obj X).ιChainComplex σ ≫ TimeTriangleSplit.triangle X j) ≫
          (push f).f (j + 2) := by
  apply CarrierSubspaceFactor.push_factor
    (rectangles (parentFamily.{1} σ) (parentFamily.{1} IntervalTriangle.triangle)) f B _ (triangle_parent X j σ)
  intro i z hz
  exact hf z.1 hz.1 z.2 hz.2

def inputSublevel {n : ℕ} (F : ReversibleMetric n) (A : ℝ) : Set (parameters n) :=
  {z | length F z.2 < A}

theorem joined_input_length_factor {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n)) (A : ℝ)
    (j : ℕ) (σ : TopCat.toSSet.obj (TopCat.of X) _⦋j⦌)
    (hA : ∀ x ∈ Set.range ((TopCat.of X).toSSetObjEquiv _ σ),
      length F (u x).val.1 + length F (u x).val.2 < A) :
    ∃ c : coeff ⟶ (chains (TopCat.of (inputSublevel F A))).X (j + 2),
      c ≫ (push (SupportedCap.subspaceMap (parameters n) (inputSublevel F A))).f (j + 2) =
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫ TimeTriangleSplit.triangle (TopCat.of X) j) ≫
          (push (JoinedTimeSplit.fullCylinder u)).f (j + 2) := by
  apply triangle_push_factor j σ (JoinedTimeSplit.fullCylinder u) (inputSublevel F A)
  intro x hx t ht
  change length F (JoinedTimeSplit.loopFamily u x) < A
  have he : length F (JoinedTimeSplit.loopFamily u x) =
      length F (u x).val.1 + length F (u x).val.2 :=
    JoinLengthComparison.length_join F (1 / 2) (by norm_num) (by norm_num) _ _ (u x).property
  rw [he]
  exact hA x hx

end
end Finsler.TimeTriangleCarrier
