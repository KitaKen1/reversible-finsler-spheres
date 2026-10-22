module

public import Finsler.Topology.SingularTimeModelComparison

/-! Expose the FULL boundary of the existing natural double prism.
Unlike its cycle restriction, this identity retains the source-boundary
term, so it applies to an interval-inserted input with nonzero boundary. -/
@[expose] public section
namespace Finsler.SingularTimeFullComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.IntervalSobolev
open Finsler.SupportedCapNaturality Finsler.SingularTimeCylinderMaps
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

def difference (X Y : TopCat.{0}) (N : ℕ) :=
  (SmallRectangleCross.ambient X Y).f N ≫ ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) -
    (FullTensorTimePrism.prism X Y).hom N (N + 1) ≫
      (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (N + 1)

theorem simplicial_boundary_zero (K L : SSet.{0}) :
    SimplicialTimeModelComparison.doublePrism 0 K L ≫
      ((TripleTimeModelExtension.target K L).chainComplex coeff).d 2 1 =
    SimplicialTimeModelComparison.difference 0 K L :=
  NaturalDegreeOneFilling.boundary_zero SimplicialTimeModelComparison.difference
    (fun N {_K _K' _L _L'} f g => SimplicialTimeModelComparison.difference_naturality f g N)
    SimplicialTimeModelComparison.difference_zero K L

theorem simplicial_boundary_succ (K L : SSet.{0}) (N : ℕ) :
    SimplicialTimeModelComparison.doublePrism (N + 1) K L ≫
      ((TripleTimeModelExtension.target K L).chainComplex coeff).d (N + 3) (N + 2) =
    SimplicialTimeModelComparison.difference (N + 1) K L +
      (K.chainComplex coeff ⊗ L.chainComplex coeff).d (N + 1) N ≫
        SimplicialTimeModelComparison.doublePrism N K L :=
  NaturalDegreeOneFilling.boundary_succ SimplicialTimeModelComparison.difference
    (fun N {_K _K' _L _L'} f g => SimplicialTimeModelComparison.difference_naturality f g N)
    SimplicialTimeModelComparison.difference_zero SimplicialTimeModelComparison.difference_comm N K L

theorem boundary_zero (X Y : TopCat.{0}) :
    SingularTimeModelComparison.doublePrism X Y 0 ≫
      (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d 2 1 = difference X Y 0 := by
  rw [SingularTimeModelComparison.doublePrism, Category.assoc,
    (SSet.chainComplexMap (modelMap X Y) coeff).comm, ← Category.assoc,
    simplicial_boundary_zero]
  exact (SingularTimeModelComparison.difference_component X Y 0).symm

theorem boundary_succ (X Y : TopCat.{0}) (N : ℕ) :
    SingularTimeModelComparison.doublePrism X Y (N + 1) ≫
      (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d (N + 3) (N + 2) =
    difference X Y (N + 1) + (chains X ⊗ chains Y).d (N + 1) N ≫
      SingularTimeModelComparison.doublePrism X Y N := by
  rw [SingularTimeModelComparison.doublePrism, Category.assoc,
    (SSet.chainComplexMap (modelMap X Y) coeff).comm, ← Category.assoc,
    simplicial_boundary_succ, Preadditive.add_comp, Category.assoc]
  rw [← SingularTimeModelComparison.difference_component]
  rfl

theorem scalar_comparison (X Y : TopCat.{0}) (N : ℕ)
    (T : singularCochainGroup (ZMod 2) (X ⊗ TopCat.of (ClosedInterval × Y)) (N + 2))
    (hT : cochainCoboundary (ZMod 2) (X ⊗ TopCat.of (ClosedInterval × Y)) (N + 2) T = 0) :
    difference X Y (N + 1) ≫ T =
      -((chains X ⊗ chains Y).d (N + 1) N ≫ SingularTimeModelComparison.doublePrism X Y N ≫ T) := by
  have h := congrArg (fun f => f ≫ T) (boundary_succ X Y N)
  have ht : (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d (N + 3) (N + 2) ≫ T = 0 := hT
  simp only [Category.assoc, Preadditive.add_comp, ht, comp_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end
end Finsler.SingularTimeFullComparison
