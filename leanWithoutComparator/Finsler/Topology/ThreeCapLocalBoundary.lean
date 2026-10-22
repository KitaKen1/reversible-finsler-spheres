module

public import Finsler.Topology.DoubleCapLocalBoundary
public import Finsler.Topology.DiagonalCutSwap
public import Finsler.Topology.ThreeCapBlockVanishing

/-! Local closure and the actual three-cap boundary equation. Only the
restrictions to the genuine common domain are assumed closed. No global
closure of a cochain extended by zero is used. -/

@[expose] public section
namespace Finsler.ThreeCapLocalBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.ThreeCapBlockVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

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

private theorem boundary_restriction_of_zero (X : TopCat.{0}) (U : Set X) (N : ℕ)
    (ξ : singularCochainGroup (ZMod 2) X N)
    (h : cochainPullback (SupportedCap.subspaceMap X U) N ξ = 0) :
    cochainPullback (SupportedCap.subspaceMap X U) (N + 1)
      (cochainCoboundary (ZMod 2) X N ξ) = 0 := by
  rw [← DiagonalCutSwap.pullback_coboundary, h]
  change ((cochainCxZMod2 (TopCat.of U)).d N (N + 1)).hom 0 = 0
  exact map_zero _

theorem cup_boundary_on_cover (X : TopCat.{0}) {ι : Type*} (W : ι → Set X)
    (A B D : Set X) (hW : ∀ i, W i ⊆ A ∨ W i ⊆ B ∨ W i ⊆ D)
    (a b c : ℕ) (J : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) X b) (ψ : singularCochainGroup (ZMod 2) X c)
    (hA : cochainPullback (SupportedCap.subspaceMap X A) a J = 0)
    (hB : cochainPullback (SupportedCap.subspaceMap X B) b φ = 0)
    (hJ : cochainCoboundary (ZMod 2) (TopCat.of D) a
      (cochainPullback (SupportedCap.subspaceMap X D) a J) = 0)
    (hφ : cochainCoboundary (ZMod 2) (TopCat.of D) b
      (cochainPullback (SupportedCap.subspaceMap X D) b φ) = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) c
      (cochainPullback (SupportedCap.subspaceMap X D) c ψ) = 0) :
    ∀ i, cochainPullback (SupportedCap.subspaceMap X (W i)) (a + (b + c) + 1)
      (cochainCoboundary (ZMod 2) X (a + (b + c))
        (cochainCup a (b + c) J (cochainCup b c φ ψ))) = 0 := by
  intro i
  rcases hW i with hi | hi | hi
  · apply restriction_zero_of_subset X (W i) A hi
    apply boundary_restriction_of_zero
    rw [cochainCup_naturality, hA, cochainCup_zero_left]
  · apply restriction_zero_of_subset X (W i) B hi
    apply boundary_restriction_of_zero
    rw [cochainCup_naturality, cochainCup_naturality, hB, cochainCup_zero_left,
      cochainCup_zero_right]
  · apply restriction_zero_of_subset X (W i) D hi
    rw [← DiagonalCutSwap.pullback_coboundary, cochainCup_naturality, cochainCup_naturality]
    exact cochainCupZMod2_respects_cocycles a (b + c) _ _ hJ
      (cochainCupZMod2_respects_cocycles b c _ _ hφ hψ)

theorem three_cap_cup (X : TopCat.{0}) (a b c d : ℕ)
    (J : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) X b) (ψ : singularCochainGroup (ZMod 2) X c) :
    threeCap X a b c d J φ ψ =
      absoluteChain X (a + (b + c)) d (a + b + c + d) (by omega)
        (cochainCup a (b + c) J (cochainCup b c φ ψ)) := by
  change absoluteChain X a (b + (c + d)) (a + b + c + d) (by omega) J ≫
    PartialDoubleCap.cap X b c d φ ψ = _
  rw [DoubleCapLocalBoundary.cap_assoc]
  have ha := TopCat.capChain_alexanderWhitneyDiagonal_assoc X (ZMod 2)
    (show a + (b + (c + d)) = a + b + c + d by omega)
    (show (b + c) + d = b + (c + d) by omega) J (cochainCup b c φ ψ)
  exact ha.trans (congrArg (absoluteChain X (a + (b + c)) d (a + b + c + d) (by omega))
    (PoolCupComparison.cochain_comparison X a (b + c) J (cochainCup b c φ ψ)))

theorem boundary_of_parts (X : TopCat.{0}) {ι : Type*} (W : ι → Set X) (a b c : ℕ)
    (J : singularCochainGroup (ZMod 2) X a)
    (φ : singularCochainGroup (ZMod 2) X b) (ψ : singularCochainGroup (ZMod 2) X c)
    (hδ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (W i)) (a + (b + c) + 1)
      (cochainCoboundary (ZMod 2) X (a + (b + c))
        (cochainCup a (b + c) J (cochainCup b c φ ψ))) = 0) (q : ℕ) :
    ((inclusion X W).f (a + b + c + (q + 1)) ≫ threeCap X a b c (q + 1) J φ ψ) ≫
      (chains X).d (q + 1) q =
        (small X W).d (a + b + c + (q + 1)) (a + b + c + q) ≫
          ((inclusion X W).f (a + b + c + q) ≫ threeCap X a b c q J φ ψ) := by
  let ξ := cochainCup a (b + c) J (cochainCup b c φ ψ)
  have hz : (inclusion X W).f (a + b + c + (q + 1)) ≫
      absoluteChain X (a + (b + c) + 1) q (a + b + c + (q + 1)) (by omega)
        (cochainCoboundary (ZMod 2) X (a + (b + c)) ξ) = 0 := by
    apply SSet.chainComplex_hom_ext (X := (X.smallSingularSubcomplex W : SSet)) (R := coeff)
    intro σ
    have hc := TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) (U := W) σ
    simp only [inclusion, SSet.ι_chainComplexMap_f_assoc, comp_zero]
    change (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ _ = 0
    exact CarrierCochainZero.cap_zero W (a + (b + c) + 1) q
      (a + b + c + (q + 1)) (by omega) _ hδ hc
  have hd : absoluteChain X (a + (b + c)) (q + 1) (a + b + c + (q + 1)) (by omega) ξ ≫
      (chains X).d (q + 1) q =
      (chains X).d (a + b + c + (q + 1)) (a + b + c + q) ≫
        absoluteChain X (a + (b + c)) q (a + b + c + q) (by omega) ξ -
      absoluteChain X (a + (b + c) + 1) q (a + b + c + (q + 1)) (by omega)
        (cochainCoboundary (ZMod 2) X (a + (b + c)) ξ) :=
    SupportedCapCochain.absolute_coboundary X (a + (b + c)) q (a + b + c + q) (by omega) ξ
  rw [three_cap_cup, three_cap_cup, Category.assoc, hd, Preadditive.comp_sub, hz, sub_zero,
    ← Category.assoc, (inclusion X W).comm, Category.assoc]

end
end Finsler.ThreeCapLocalBoundary
