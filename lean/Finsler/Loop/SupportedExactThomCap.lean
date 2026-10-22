module

public import Finsler.Topology.SupportedCapCochain
public import Finsler.Topology.CochainClass
public import Finsler.Topology.SupportedCapNaturality

/-! The ORIGINAL supported cap of an ACTUAL supported coboundary
has an explicit neighborhood-valued primitive cap. After ANY closed
near-neighborhood output cochain, the complete scalar cochain is a
true coboundary. All original small approximation and localization
maps are kept; the source input is not assumed an absolute cycle. -/
@[expose] public section
namespace Finsler.SupportedExactThomCap
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hcover : A ∪ B = Set.univ) (p : ℕ) (κ : singularCochainGroup (ZMod 2) X p)
  (hκ : cochainPullback (SupportedCap.subspaceMap X A) p κ = 0)

include hκ in
theorem coboundary_supported :
    cochainPullback (SupportedCap.subspaceMap X A) (p + 1) (cochainCoboundary (ZMod 2) X p κ) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X A).op).comm p (p + 1)) κ
  change ((cochainCxZMod2 (TopCat.of A)).d p (p + 1)).hom
    (cochainPullback (SupportedCap.subspaceMap X A) p κ) =
    cochainPullback (SupportedCap.subspaceMap X A) (p + 1) (cochainCoboundary (ZMod 2) X p κ) at he
  rw [hκ, map_zero] at he
  exact he.symm

def correction (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    singularCochainGroup (ZMod 2) X (p + q) :=
  SupportedCap.cut X A B hA hB hcover p q (p + q) rfl κ hκ ≫ ψ

def cochain (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    singularCochainGroup (ZMod 2) X (p + q + 1) :=
  SupportedCap.cut X A B hA hB hcover (p + 1) q (p + q + 1) (by omega)
    (cochainCoboundary (ZMod 2) X p κ) (coboundary_supported X A p κ hκ) ≫ ψ

theorem correction_boundary (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X (p + q) (correction X A B hA hB hcover p κ hκ q ψ) =
      cochain X A B hA hB hcover p κ hκ q ψ := by
  have he := congrArg (fun a => a ≫ ψ)
    (SupportedCapCochain.cut_coboundary X A B hA hB hcover p q (p + q) rfl κ hκ
      (coboundary_supported X A p κ hκ))
  change (chains (TopCat.of B)).d (q + 1) q ≫ ψ = 0 at hψ
  simp only [Category.assoc, hψ, comp_zero, Preadditive.sub_comp] at he
  exact sub_eq_zero.mp he.symm

theorem cochain_closed (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X (p + q + 1) (cochain X A B hA hB hcover p κ hκ q ψ) = 0 := by
  rw [← correction_boundary X A B hA hB hcover p κ hκ q ψ hψ]
  exact CochainClass.closed_boundary (cochainCxZMod2 X) (p + q) (p + q + 1) _

theorem cochain_class_zero (q : ℕ) (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    CochainClass.classOf (cochainCxZMod2 X) (p + q + 1) (cochain X A B hA hB hcover p κ hκ q ψ)
      (cochain_closed X A B hA hB hcover p κ hκ q ψ hψ) = 0 := by
  have he := correction_boundary X A B hA hB hcover p κ hκ q ψ hψ
  have hb := CochainClass.closed_boundary (cochainCxZMod2 X) (p + q) (p + q + 1)
    (correction X A B hA hB hcover p κ hκ q ψ)
  exact (CochainClass.classOf_congr (cochainCxZMod2 X) (p + q + 1) he.symm _ hb).trans
    (CochainClass.classOf_boundary (cochainCxZMod2 X) (p + q) (p + q + 1) _ hb)

end
end Finsler.SupportedExactThomCap
