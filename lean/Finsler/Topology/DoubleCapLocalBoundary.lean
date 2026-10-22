module

public import Finsler.Topology.PartialDoubleCap
public import Finsler.Topology.AdequateTubeCochain
public import Finsler.Topology.SupportedCapCochain

/-! The actual successive-cap boundary identity on adequate small
chains. A tested cochain is extended by zero from its genuine domain;
only local closure on the far/tube cover is used. -/

@[expose] public section
namespace Finsler.DoubleCapLocalBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem cap_assoc (X : TopCat.{0}) (k p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p) :
    PartialDoubleCap.cap X k p q φ ψ =
      absoluteChain X (k + p) q (k + (p + q)) (by omega) (cochainCup k p φ ψ) := by
  have ha := TopCat.capChain_alexanderWhitneyDiagonal_assoc X (ZMod 2)
    (show k + (p + q) = k + (p + q) from rfl) (show p + q = p + q from rfl) φ ψ
  exact ha.trans (congrArg (absoluteChain X (k + p) q (k + (p + q)) (by omega))
    (PoolCupComparison.cochain_comparison X k p φ ψ))

theorem boundary_of_parts (X : TopCat.{0}) {ι : Type*} (W : ι → Set X) (k p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (hδ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (W i)) (k + p + 1)
      (cochainCoboundary (ZMod 2) X (k + p) (cochainCup k p φ ψ)) = 0) (q : ℕ) :
    ((inclusion X W).f (k + (p + (q + 1))) ≫ PartialDoubleCap.cap X k p (q + 1) φ ψ) ≫
      (chains X).d (q + 1) q =
        (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
          ((inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ) := by
  have hz : (inclusion X W).f (k + (p + (q + 1))) ≫
      absoluteChain X (k + p + 1) q (k + (p + (q + 1))) (by omega)
        (cochainCoboundary (ZMod 2) X (k + p) (cochainCup k p φ ψ)) = 0 := by
    apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
    intro σ
    have hc := TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) (U := W) σ
    simp only [inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
    change (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ _ = 0
    exact CarrierCochainZero.cap_zero W (k + p + 1) q (k + (p + (q + 1))) (by omega) _ hδ hc
  have hd : absoluteChain X (k + p) (q + 1) (k + (p + (q + 1))) (by omega) (cochainCup k p φ ψ) ≫
      (chains X).d (q + 1) q =
      (chains X).d (k + (p + (q + 1))) (k + (p + q)) ≫
        absoluteChain X (k + p) q (k + (p + q)) (by omega) (cochainCup k p φ ψ) -
      absoluteChain X (k + p + 1) q (k + (p + (q + 1))) (by omega)
        (cochainCoboundary (ZMod 2) X (k + p) (cochainCup k p φ ψ)) :=
    SupportedCapCochain.absolute_coboundary X (k + p) q (k + (p + q)) (by omega) _
  rw [cap_assoc, cap_assoc, Category.assoc, hd, Preadditive.comp_sub, hz, sub_zero,
    ← Category.assoc, (inclusion X W).comm, Category.assoc]

private theorem restriction_zero_of_subset (X : TopCat.{0}) (U V : Set X) (hUV : U ⊆ V)
    (N : ℕ) (ξ : singularCochainGroup (ZMod 2) X N)
    (hV : cochainPullback (SupportedCap.subspaceMap X V) N ξ = 0) :
    cochainPullback (SupportedCap.subspaceMap X U) N ξ = 0 := by
  let f := restriction (𝟙 X) U V hUV
  have he : f ≫ SupportedCap.subspaceMap X V = SupportedCap.subspaceMap X U := by
    ext z : 1
    rfl
  have hz := congrArg (cochainPullback f N) hV
  rw [← pullback_comp, he] at hz
  simpa only [cochainPullback, map_zero] using hz

theorem boundary_on_tube_cover (X : TopCat.{0}) {ι : Type*} (W : ι → Set X) (A D : Set X)
    (hW : ∀ i, W i ⊆ A ∨ W i ⊆ D) (k p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k)
    (hφ : cochainCoboundary (ZMod 2) X k φ = 0)
    (hA : cochainPullback (SupportedCap.subspaceMap X A) k φ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) p)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) p ψ = 0) (q : ℕ) :
    ((inclusion X W).f (k + (p + (q + 1))) ≫
      PartialDoubleCap.cap X k p (q + 1) φ (TubeCochainExtension.extend X D p ψ)) ≫
        (chains X).d (q + 1) q =
      (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
        ((inclusion X W).f (k + (p + q)) ≫
          PartialDoubleCap.cap X k p q φ (TubeCochainExtension.extend X D p ψ)) := by
  apply boundary_of_parts X W k p φ (TubeCochainExtension.extend X D p ψ) _ q
  intro i
  have hparts := AdequateTubeCochain.boundary_parts_zero X A D k p φ hφ hA ψ hψ
  rcases hW i with hi | hi
  · exact restriction_zero_of_subset X (W i) A hi (k + p + 1) _ (hparts false)
  · exact restriction_zero_of_subset X (W i) D hi (k + p + 1) _ (hparts true)

end
end Finsler.DoubleCapLocalBoundary
