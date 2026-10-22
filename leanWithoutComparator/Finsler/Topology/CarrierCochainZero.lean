module

public import Finsler.Topology.SupportedCapNaturality

/-! Literal cochain and cap annihilation on arbitrary carrier families.
The cover need not be open and no homology monomorphism is used. -/

@[expose] public section
namespace Finsler.CarrierCochainZero

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {X : TopCat.{0}} {ι : Type*} (W : ι → Set X)

theorem small_zero (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (W i)) n φ = 0) :
    (inclusion X W).f n ≫ φ = 0 := by
  apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
  intro σ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X W σ.val).mp σ.property
  have hz := congrArg
    (fun z => (TopCat.toSSet.obj (TopCat.of (W i))).ιChainComplex
      (SupportedCap.simplexLift X (W i) σ.val hi) ≫ z) (hφ i)
  change (TopCat.toSSet.obj (TopCat.of (W i))).ιChainComplex
      (SupportedCap.simplexLift X (W i) σ.val hi) ≫
        ((SSet.chainComplexMap (TopCat.toSSet.map (SupportedCap.subspaceMap X (W i))) coeff).f n ≫ φ) = _ at hz
  rw [SSet.ι_chainComplexMap_f_assoc, SupportedCap.simplexLift_image, comp_zero] at hz
  simp only [inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
  change (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ φ = 0
  exact hz

theorem carried_zero (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (W i)) n φ = 0)
    {c : coeff ⟶ (chains X).X n} (hc : c ∈ supported X W n) : c ≫ φ = 0 := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hc
  rw [Category.assoc, small_zero W n φ hφ, comp_zero]

theorem cap_zero (k t m : ℕ) (h : k + t = m)
    (φ : singularCochainGroup (ZMod 2) X k)
    (hφ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (W i)) k φ = 0)
    {c : coeff ⟶ (chains X).X m} (hc : c ∈ supported X W m) :
    c ≫ absoluteChain X k t m h φ = 0 := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hc
  have hz : (inclusion X W).f m ≫ absoluteChain X k t m h φ = 0 := by
    apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
    intro σ
    obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X W σ.val).mp σ.property
    simp only [inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
    change (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ absoluteChain X k t m h φ = 0
    exact SupportedCap.cap_zero_on_simplex X (W i) k t m h φ (hφ i) σ.val hi
  rw [Category.assoc, hz, comp_zero]

end
end Finsler.CarrierCochainZero
