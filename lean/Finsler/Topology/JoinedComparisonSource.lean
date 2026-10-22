module

public import Finsler.Topology.JoinedFamilyNaturality
public import Finsler.Topology.TimeTriangleSplit
public import Finsler.Topology.AnnularTimeTrim

/-! The specified time triangle and both actual trimming double prisms
have genuine chain sources in the same two-time-plane product.
Their images under the three existing family maps are literal identities. -/

@[expose] public section
namespace Finsler.JoinedComparisonSource

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.JoinedComparisonAdequacy Finsler.JoinedFamilyNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def triangleLift (X : TopCat.{0}) : X ⊗ TopCat.I ⟶ TopCat.of (Outer X) :=
  TopCat.ofHom ⟨fun z => ((0, z.2.down), z.1),
    (continuous_const.prodMk (continuous_uliftDown.comp continuous_snd)).prodMk continuous_fst⟩

def squareLift (X : TopCat.{0}) : TopCat.of (ClosedInterval × (ClosedInterval × X)) ⟶
    TopCat.of (Outer X) :=
  TopCat.ofHom ⟨fun z => ((z.1, z.2.1), z.2.2),
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)⟩

def triangleSource (X : TopCat.{0}) (j : ℕ) : (chains X).X j ⟶
    (chains (TopCat.of (Outer X))).X (j + 2) :=
  TimeTriangleSplit.triangle X j ≫ (push (triangleLift X)).f (j + 2)

def squareSource (X : TopCat.{0}) (j : ℕ) : (chains X).X j ⟶
    (chains (TopCat.of (Outer X))).X (j + 2) :=
  AnnularTimeTrim.prism X j ≫
    AnnularTimeTrim.prism (TopCat.of (ClosedInterval × X)) (j + 1) ≫
    (push (squareLift X)).f (j + 2)

theorem square_post (X Y : TopCat.{0}) (j : ℕ) (f : TopCat.of (Outer X) ⟶ Y)
    {g h : TopCat.of (ClosedInterval × X) ⟶ Y} (H : TopCat.Homotopy g h)
    (he : H.h = (AnnularTimeTrim.cylinder (TopCat.of (ClosedInterval × X))).h ≫ squareLift X ≫ f) :
    squareSource X j ≫ (push f).f (j + 2) =
      AnnularTimeTrim.prism X j ≫ (H.toSSet.chainComplexMap coeff).hom (j + 1) (j + 2) := by
  have hp : AnnularTimeTrim.prism (TopCat.of (ClosedInterval × X)) (j + 1) ≫
      (push (squareLift X ≫ f)).f (j + 2) =
      (H.toSSet.chainComplexMap coeff).hom (j + 1) (j + 2) := by
    unfold AnnularTimeTrim.prism
    rw [TimePrismNaturality.prism_post]
    apply TimePrismNaturality.prism_congr
    exact he.symm
  unfold squareSource
  rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, ← push_comp, hp]

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)

theorem triangle_actual (j : ℕ) :
    triangleSource (TopCat.of X) j ≫ (push (globalMap u a ha ha1 0)).f (j + 2) =
      TimeTriangleSplit.triangle (TopCat.of X) j ≫ (push (JoinedTimeSplit.fullCylinder u)).f (j + 2) := by
  have he : triangleLift (TopCat.of X) ≫ globalMap u a ha ha1 0 = JoinedTimeSplit.fullCylinder u := by
    ext z : 1
    rfl
  unfold triangleSource
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp, he]

theorem first_double_actual (j : ℕ) :
    squareSource (TopCat.of X) j ≫ (push (globalMap u a ha ha1 1)).f (j + 2) =
      AnnularTimeTrim.prism (TopCat.of X) j ≫
        ((CylinderTimeTrim.homotopy (JoinedHalfCollars.firstFamily u) a ha ha1).toSSet.chainComplexMap coeff).hom
          (j + 1) (j + 2) := by
  apply square_post
  ext z : 1
  rfl

theorem second_double_actual (j : ℕ) :
    squareSource (TopCat.of X) j ≫ (push (globalMap u a ha ha1 2)).f (j + 2) =
      AnnularTimeTrim.prism (TopCat.of X) j ≫
        ((CylinderTimeTrim.homotopy (JoinedHalfCollars.secondFamily u) a ha ha1).toSSet.chainComplexMap coeff).hom
          (j + 1) (j + 2) := by
  apply square_post
  ext z : 1
  rfl

end
end Finsler.JoinedComparisonSource
