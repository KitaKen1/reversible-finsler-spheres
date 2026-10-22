module

public import Finsler.Loop.UniversalTimeTriangle
public import Finsler.Loop.SingularRightFullBoundary
public import Finsler.Loop.SingularLeftNaturality

/-! Actual universal triangle insertion with its FULL boundary,
including the source-boundary term. Postcomposition and independent
source-carrier preservation are proved on the real shuffle chains. -/
@[expose] public section
namespace Finsler.UniversalTimeTriangleChain
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def interval (X : TopCat.{0}) (p : ℕ) : (chains X).X p ⟶ (chains (X ⊗ TopCat.I)).X (p + 1) :=
  SingularChainCross.right X TopCat.I p 1 TimeShuffleComparison.intervalSimplex

def triangle (X : TopCat.{0}) (p : ℕ) : (chains X).X p ⟶ (chains (X ⊗ UniversalTimeTriangle.space)).X (p + 2) :=
  SingularChainCross.right X UniversalTimeTriangle.space p 2 UniversalTimeTriangle.simplex

def edge (X : TopCat.{0}) (i : Fin 3) (p : ℕ) : (chains X).X p ⟶ (chains (X ⊗ UniversalTimeTriangle.space)).X (p + 1) :=
  interval X p ≫ (push (X ◁ UniversalTimeTriangle.edgeMap i)).f (p + 1)

theorem full_boundary (X : TopCat.{0}) (p : ℕ) :
    triangle X (p + 1) ≫ (chains (X ⊗ UniversalTimeTriangle.space)).d (p + 3) (p + 2) =
      (chains X).d (p + 1) p ≫ triangle X p + edge X 0 (p + 1) + edge X 1 (p + 1) + edge X 2 (p + 1) := by
  have h := SingularRightFullBoundary.rightChain_boundary_two X UniversalTimeTriangle.space p
    ((TopCat.toSSet.obj UniversalTimeTriangle.space).ιChainComplex UniversalTimeTriangle.simplex)
  rw [UniversalTimeTriangle.chain_boundary] at h
  simpa only [SingularRightBoundary.rightChain_add, SingularRightNaturality.rightChain_map_simplex,
    SingularRightBoundary.rightChain_simplex, triangle, edge, interval, add_assoc] using h

theorem source_natural {X X' : TopCat.{0}} (g : X' ⟶ X) (p : ℕ) :
    (push g).f p ≫ triangle X p = triangle X' p ≫ (push (g ▷ UniversalTimeTriangle.space)).f (p + 2) :=
  SingularLeftNaturality.right_pre X' X UniversalTimeTriangle.space g p 2 UniversalTimeTriangle.simplex

def postTriangle {X Y : TopCat.{0}} (f : X ⊗ UniversalTimeTriangle.space ⟶ Y) (p : ℕ) :=
  triangle X p ≫ (push f).f (p + 2)

def postEdge {X Y : TopCat.{0}} (f : X ⊗ UniversalTimeTriangle.space ⟶ Y) (i : Fin 3) (p : ℕ) :=
  edge X i p ≫ (push f).f (p + 1)

theorem post_full_boundary {X Y : TopCat.{0}} (f : X ⊗ UniversalTimeTriangle.space ⟶ Y) (p : ℕ) :
    postTriangle f (p + 1) ≫ (chains Y).d (p + 3) (p + 2) =
      (chains X).d (p + 1) p ≫ postTriangle f p + postEdge f 0 (p + 1) + postEdge f 1 (p + 1) + postEdge f 2 (p + 1) := by
  calc
    _ = (triangle X (p + 1) ≫ (chains (X ⊗ UniversalTimeTriangle.space)).d (p + 3) (p + 2)) ≫ (push f).f (p + 2) := by
      simp only [postTriangle, Category.assoc, (push f).comm]
    _ = _ := by
      rw [full_boundary]
      simp only [postTriangle, postEdge, Preadditive.add_comp, Category.assoc]

theorem source_post_natural {X X' Y : TopCat.{0}} (g : X' ⟶ X) (f : X ⊗ UniversalTimeTriangle.space ⟶ Y) (p : ℕ) :
    (push g).f p ≫ postTriangle f p = postTriangle ((g ▷ UniversalTimeTriangle.space) ≫ f) p := by
  have hc := congrArg (fun h => h.f (p + 2)) (push_comp (g ▷ UniversalTimeTriangle.space) f)
  change (push ((g ▷ UniversalTimeTriangle.space) ≫ f)).f (p + 2) =
    (push (g ▷ UniversalTimeTriangle.space)).f (p + 2) ≫ (push f).f (p + 2) at hc
  unfold postTriangle
  rw [← Category.assoc, source_natural, Category.assoc, ← hc]

theorem source_cochain_natural {X X' Y : TopCat.{0}} (g : X' ⟶ X) (f : X ⊗ UniversalTimeTriangle.space ⟶ Y) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (p + 2)) :
    cochainPullback g p (postTriangle f p ≫ φ) = postTriangle ((g ▷ UniversalTimeTriangle.space) ≫ f) p ≫ φ := by
  change (push g).f p ≫ (postTriangle f p ≫ φ) = _
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun h => h ≫ φ) (source_post_natural g f p))

theorem source_carrier_zero {X X' Y : TopCat.{0}} (g : X' ⟶ X) (f : X ⊗ UniversalTimeTriangle.space ⟶ Y) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (p + 2))
    (hφ : cochainPullback ((g ▷ UniversalTimeTriangle.space) ≫ f) (p + 2) φ = 0) :
    cochainPullback g p (postTriangle f p ≫ φ) = 0 := by
  rw [source_cochain_natural]
  change triangle X' p ≫ cochainPullback ((g ▷ UniversalTimeTriangle.space) ≫ f) (p + 2) φ = 0
  rw [hφ, comp_zero]

end
end Finsler.UniversalTimeTriangleChain
