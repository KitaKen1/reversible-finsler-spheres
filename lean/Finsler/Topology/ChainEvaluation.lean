module

public import Finsler.Topology.Kronecker
public import Finsler.Topology.CochainClass
public import Finsler.Topology.CochainComparison

/-! Evaluate a closed cochain on the actual homology cokernel, naturally.
This uses the same cycles and quotient maps as the project's existing
Kronecker pairing, not an abstract replacement for homology. -/

@[expose] public section

namespace Finsler.ChainEvaluation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)

theorem cycles_boundary_zero (n : ℕ) (φ : C.X n ⟶ coeff) (hφ : C.d (n + 1) n ≫ φ = 0) :
    C.toCycles (n + 1) n ≫ (C.iCycles n ≫ φ) = 0 := by
  rw [← Category.assoc, C.toCycles_i, hφ]

def evaluation (n : ℕ) (φ : C.X n ⟶ coeff) (hφ : C.d (n + 1) n ≫ φ = 0) :
    C.homology n ⟶ coeff :=
  (C.homologyIsCokernel (n + 1) n ((ComplexShape.down ℕ).prev_eq' rfl)).desc
    (CokernelCofork.ofπ (C.iCycles n ≫ φ) (cycles_boundary_zero C n φ hφ))

theorem homologyπ_evaluation (n : ℕ) (φ : C.X n ⟶ coeff) (hφ : C.d (n + 1) n ≫ φ = 0) :
    C.homologyπ n ≫ evaluation C n φ hφ = C.iCycles n ≫ φ :=
  (C.homologyIsCokernel (n + 1) n ((ComplexShape.down ℕ).prev_eq' rfl)).fac
    (CokernelCofork.ofπ (C.iCycles n ≫ φ) (cycles_boundary_zero C n φ hφ))
    WalkingParallelPair.one

theorem naturality {D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : C ⟶ D)
    (n : ℕ) (φ : D.X n ⟶ coeff) (hφ : D.d (n + 1) n ≫ φ = 0)
    (h : C.d (n + 1) n ≫ (f.f n ≫ φ) = 0) :
    evaluation C n (f.f n ≫ φ) h =
      HomologicalComplex.homologyMap f n ≫ evaluation D n φ hφ := by
  apply (cancel_epi (C.homologyπ n)).mp
  rw [homologyπ_evaluation, HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_evaluation, HomologicalComplex.cyclesMap_i_assoc]

theorem apply_cycle (n : ℕ) (φ : C.X n ⟶ coeff) (hφ : C.d (n + 1) n ≫ φ = 0)
    (c : C.cycles n) :
    (evaluation C n φ hφ).hom ((C.homologyπ n).hom c) = φ.hom ((C.iCycles n).hom c) :=
  ConcreteCategory.congr_hom (homologyπ_evaluation C n φ hφ) c

theorem pool_comparison (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    evaluation (chainCxZMod2 X) n φ hφ =
      ModuleCat.ofHom ((kroneckerMap X n).hom (cocycleClass X n φ hφ)) := by
  apply (cancel_epi ((chainCxZMod2 X).homologyπ n)).mp
  rw [homologyπ_evaluation]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change φ.hom (((chainCxZMod2 X).iCycles n).hom c) =
    (kroneckerMap X n).hom (cocycleClass X n φ hφ) (((chainCxZMod2 X).homologyπ n).hom c)
  rw [kroneckerMap_cocycleClass, kroneckerFunctional_apply]


end
end Finsler.ChainEvaluation
