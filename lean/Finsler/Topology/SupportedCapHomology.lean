module

public import Finsler.Topology.SupportedCap
public import Finsler.Topology.DegreeLoweringHomology

/-! The supported cap lands in actual neighborhood homology. After inclusion
it is exactly the existing cap product, since the actual small approximation
is chain homotopic to the identity. No comparison or filling assumption is used. -/

@[expose] public section

namespace Finsler.SupportedCapHomology

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def absoluteOperation (X : TopCat.{0}) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    DegreeLoweringHomology.Map (chains X) (chains X) p where
  component q := absoluteChain X p q (p + q) rfl φ
  comm q := by
    convert RelativeCapBoundary.absolute_chain_boundary X p q (p + q) rfl φ hφ using 1

theorem absolute_cycles (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (absoluteOperation X p φ hφ).cycles q =
      RelativeCapBoundary.absoluteCycleOf X p q (p + q) rfl φ hφ := by
  apply (cancel_mono ((chains X).iCycles q)).mp
  rw [DegreeLoweringHomology.Map.cycles_i, RelativeCapBoundary.absolute_cycle_i]
  rfl

theorem absolute_homology (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (absoluteOperation X p φ hφ).homology q =
      ModuleCat.ofHom (PoolCap.cap X p q (p + q) rfl (cocycleClass X p φ hφ)) := by
  apply (cancel_epi ((chains X).homologyπ (p + q))).mp
  rw [DegreeLoweringHomology.Map.homologyπ_homology, absolute_cycles]
  exact (RelativeCapBoundary.absolute_cap_class X p q (p + q) rfl φ hφ).symm

def operation (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hsupport : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hclosed : cochainCoboundary (ZMod 2) X p φ = 0) :
    DegreeLoweringHomology.Map (chains X) (chains (TopCat.of B)) p where
  component q := SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hsupport
  comm q := by
    convert SupportedCap.cut_boundary X A B hA hB hcover p q (p + q) rfl φ hsupport hclosed using 1

theorem ambient_comparison (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hsupport : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hclosed : cochainCoboundary (ZMod 2) X p φ = 0) :
    (operation X A B hA hB hcover p φ hsupport hclosed).homology q ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map (SupportedCap.subspaceMap X B)) coeff) q =
      ModuleCat.ofHom (PoolCap.cap X p q (p + q) rfl (cocycleClass X p φ hclosed)) := by
  let c := operation X A B hA hB hcover p φ hsupport hclosed
  let a := absoluteOperation X p φ hclosed
  let j := SSet.chainComplexMap (TopCat.toSSet.map (SupportedCap.subspaceMap X B)) coeff
  let approx := TauCeti.singularSmallApprox coeff (SupportedCap.cover X A B)
  have he : (c.post j).homology q = (a.pre approx).homology q := by
    apply DegreeLoweringHomology.Map.homology_eq_of_components
    intro k
    exact SupportedCap.cut_inclusion X A B hA hB hcover p k (p + k) rfl φ hsupport
  calc
    _ = (c.post j).homology q := (c.post_homology j q).symm
    _ = (a.pre approx).homology q := he
    _ = HomologicalComplex.homologyMap approx (p + q) ≫ a.homology q := a.pre_homology approx q
    _ = a.homology q := by
      have h := (TauCeti.singularSmallApproxHomotopy coeff (SupportedCap.cover X A B)).homologyMap_eq (p + q)
      rw [HomologicalComplex.homologyMap_id] at h
      rw [← h, Category.id_comp]
    _ = _ := absolute_homology X p q φ hclosed

theorem nonzero_of_cap_ne_zero (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hsupport : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hclosed : cochainCoboundary (ZMod 2) X p φ = 0)
    (x : (chains X).homology (p + q))
    (hx : PoolCap.cap X p q (p + q) rfl (cocycleClass X p φ hclosed) x ≠ 0) :
    ((operation X A B hA hB hcover p φ hsupport hclosed).homology q).hom x ≠ 0 := by
  intro hz
  have he := ConcreteCategory.congr_hom
    (ambient_comparison X A B hA hB hcover p q φ hsupport hclosed) x
  change (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (TopCat.toSSet.map (SupportedCap.subspaceMap X B)) coeff) q).hom
        (((operation X A B hA hB hcover p φ hsupport hclosed).homology q).hom x) =
    PoolCap.cap X p q (p + q) rfl (cocycleClass X p φ hclosed) x at he
  rw [hz, map_zero] at he
  exact hx he.symm

end
end Finsler.SupportedCapHomology
