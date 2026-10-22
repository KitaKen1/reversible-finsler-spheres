module

public import Finsler.Topology.SupportedCap

/-! The full cochain boundary identity for the actual neighborhood-valued cut.
The primitive keeps its support; closedness is not assumed in this identity. -/

@[expose] public section

namespace Finsler.SupportedCapCochain

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedCap
open Finsler.RelativeCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

theorem absolute_sub (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ ψ : singularCochainGroup (ZMod 2) X p) :
    absoluteChain X p q n h (φ - ψ) = absoluteChain X p q n h φ - absoluteChain X p q n h ψ :=
  map_sub _ φ ψ

theorem absolute_coboundary (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (κ : singularCochainGroup (ZMod 2) X p) :
    absoluteChain X p (q + 1) (n + 1) (by omega) κ ≫ (chains X).d (q + 1) q =
      (chains X).d (n + 1) n ≫ absoluteChain X p q n h κ -
        absoluteChain X (p + 1) q (n + 1) (by omega) (cochainCoboundary (ZMod 2) X p κ) := by
  have hd := TauCeti.ChainComplex.capChain_comp_d (k := ZMod 2) (diagonal X)
    ((TopCat.toSSet.obj X).chainComplexPairing (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom)
    p q n h κ
  exact hd.trans (sign_smul p _)

theorem localized_sub (X : TopCat.{0}) (A B : Set X)
    (p q n : ℕ) (h : p + q = n) (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (hψ : cochainPullback (subspaceMap X A) p ψ = 0)
    (hs : cochainPullback (subspaceMap X A) p (φ - ψ) = 0) :
    localizedCap X A B p q n h (φ - ψ) hs =
      localizedCap X A B p q n h φ hφ - localizedCap X A B p q n h ψ hψ := by
  haveI := subspacePush_mono X B q
  apply (cancel_mono ((SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff).f q)).mp
  rw [Preadditive.sub_comp, localizedCap_inclusion, localizedCap_inclusion,
    localizedCap_inclusion, absolute_sub, Preadditive.comp_sub]

theorem localized_coboundary (X : TopCat.{0}) (A B : Set X)
    (p q n : ℕ) (h : p + q = n) (κ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (subspaceMap X A) p κ = 0)
    (hd : cochainPullback (subspaceMap X A) (p + 1) (cochainCoboundary (ZMod 2) X p κ) = 0) :
    localizedCap X A B p (q + 1) (n + 1) (by omega) κ hs ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small X (cover X A B)).d (n + 1) n ≫ localizedCap X A B p q n h κ hs -
        localizedCap X A B (p + 1) q (n + 1) (by omega)
          (cochainCoboundary (ZMod 2) X p κ) hd := by
  let j := SSet.chainComplexMap (TopCat.toSSet.map (subspaceMap X B)) coeff
  haveI : Mono (j.f q) := subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  calc
    _ = localizedCap X A B p (q + 1) (n + 1) (by omega) κ hs ≫
        (j.f (q + 1) ≫ (chains X).d (q + 1) q) := by
      rw [Category.assoc, ← HomologicalComplex.Hom.comm]
    _ = (inclusion X (cover X A B)).f (n + 1) ≫
        (absoluteChain X p (q + 1) (n + 1) (by omega) κ ≫ (chains X).d (q + 1) q) := by
      rw [← Category.assoc, localizedCap_inclusion, Category.assoc]
    _ = (inclusion X (cover X A B)).f (n + 1) ≫
        ((chains X).d (n + 1) n ≫ absoluteChain X p q n h κ -
          absoluteChain X (p + 1) q (n + 1) (by omega) (cochainCoboundary (ZMod 2) X p κ)) := by
      rw [absolute_coboundary X p q n h κ]
    _ = _ := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
        localizedCap_inclusion, ← Category.assoc, HomologicalComplex.Hom.comm,
        Category.assoc, localizedCap_inclusion]

theorem cut_sub (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q n : ℕ) (h : p + q = n)
    (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (hψ : cochainPullback (subspaceMap X A) p ψ = 0)
    (hs : cochainPullback (subspaceMap X A) p (φ - ψ) = 0) :
    cut X A B hA hB hcover p q n h (φ - ψ) hs =
      cut X A B hA hB hcover p q n h φ hφ - cut X A B hA hB hcover p q n h ψ hψ := by
  rw [cut, cut, cut, localized_sub X A B p q n h φ ψ hφ hψ hs, Preadditive.comp_sub]

theorem cut_coboundary (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q n : ℕ) (h : p + q = n)
    (κ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (subspaceMap X A) p κ = 0)
    (hd : cochainPullback (subspaceMap X A) (p + 1) (cochainCoboundary (ZMod 2) X p κ) = 0) :
    cut X A B hA hB hcover p (q + 1) (n + 1) (by omega) κ hs ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains X).d (n + 1) n ≫ cut X A B hA hB hcover p q n h κ hs -
        cut X A B hA hB hcover (p + 1) q (n + 1) (by omega)
          (cochainCoboundary (ZMod 2) X p κ) hd := by
  rw [cut, Category.assoc, localized_coboundary X A B p q n h κ hs hd,
    Preadditive.comp_sub, ← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc]
  rfl

end
end Finsler.SupportedCapCochain

