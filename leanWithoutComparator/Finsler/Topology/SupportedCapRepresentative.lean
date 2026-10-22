module

public import Finsler.Topology.SupportedCapCochain
public import Finsler.Topology.DegreeLoweringExact
public import Finsler.Topology.SupportedCapHomology

/-! A supported cochain primitive identifies actual neighborhood homology actions. -/

@[expose] public section

namespace Finsler.SupportedCapRepresentative

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCap
open Finsler.SupportedCapCochain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem support_sub (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (hψ : cochainPullback (subspaceMap X A) p ψ = 0) :
    cochainPullback (subspaceMap X A) p (φ - ψ) = 0 := by
  change (((singularCochainComplexZMod2.map (subspaceMap X A).op).f p).hom (φ - ψ)) = 0
  rw [map_sub]
  change cochainPullback (subspaceMap X A) p φ - cochainPullback (subspaceMap X A) p ψ = 0
  rw [hφ, hψ, sub_self]

theorem cut_congr (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q n : ℕ) (h : p + q = n)
    (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainPullback (subspaceMap X A) p φ = 0)
    (hψ : cochainPullback (subspaceMap X A) p ψ = 0) (he : φ = ψ) :
    cut X A B hA hB hcover p q n h φ hφ = cut X A B hA hB hcover p q n h ψ hψ := by
  subst ψ
  rfl

theorem homology_eq (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X (p + 1))
    (hφ : cochainPullback (subspaceMap X A) (p + 1) φ = 0)
    (hψ : cochainPullback (subspaceMap X A) (p + 1) ψ = 0)
    (hcφ : cochainCoboundary (ZMod 2) X (p + 1) φ = 0)
    (hcψ : cochainCoboundary (ZMod 2) X (p + 1) ψ = 0)
    (κ : singularCochainGroup (ZMod 2) X p)
    (hκ : cochainPullback (subspaceMap X A) p κ = 0)
    (he : cochainCoboundary (ZMod 2) X p κ = φ - ψ) :
    (SupportedCapHomology.operation X A B hA hB hcover (p + 1) φ hφ hcφ).homology q =
      (SupportedCapHomology.operation X A B hA hB hcover (p + 1) ψ hψ hcψ).homology q := by
  have hdiff := support_sub X A (p + 1) φ ψ hφ hψ
  have hdκ : cochainPullback (subspaceMap X A) (p + 1)
      (cochainCoboundary (ZMod 2) X p κ) = 0 := by rw [he]; exact hdiff
  have hd := cut_coboundary X A B hA hB hcover p q (p + q) rfl κ hκ hdκ
  have aux (N : ℕ) (hN : N = p + q + 1) (h1 : p + (q + 1) = N) (h2 : (p + 1) + q = N) :
      cut X A B hA hB hcover p (q + 1) N h1 κ hκ ≫ (chains (TopCat.of B)).d (q + 1) q =
        (chains X).d N (p + q) ≫ cut X A B hA hB hcover p q (p + q) rfl κ hκ -
          cut X A B hA hB hcover (p + 1) q N h2 (cochainCoboundary (ZMod 2) X p κ) hdκ := by
    subst N
    exact hd
  have hd' : cut X A B hA hB hcover p (q + 1) ((p + 1) + q) (by omega) κ hκ ≫
        (chains (TopCat.of B)).d (q + 1) q =
      (chains X).d ((p + 1) + q) (p + q) ≫ cut X A B hA hB hcover p q (p + q) rfl κ hκ -
        cut X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl
          (cochainCoboundary (ZMod 2) X p κ) hdκ := by
    exact aux ((p + 1) + q) (by omega) (by omega) rfl
  have hcs : cut X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl
      (cochainCoboundary (ZMod 2) X p κ) hdκ =
      cut X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl φ hφ -
        cut X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl ψ hψ :=
    (cut_congr X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl
      _ _ hdκ hdiff he).trans (cut_sub X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl
        φ ψ hφ hψ hdiff)
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (-cut X A B hA hB hcover p (q + 1) ((p + 1) + q) (by omega) κ hκ)
  have hz := congrArg (fun m => (chains X).iCycles ((p + 1) + q) ≫ m) hd'
  rw [hcs] at hz
  simp only [Preadditive.comp_sub, ← Category.assoc, (chains X).iCycles_d,
    zero_comp, zero_sub] at hz
  change (chains X).iCycles ((p + 1) + q) ≫
    (cut X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl φ hφ -
      cut X A B hA hB hcover (p + 1) q ((p + 1) + q) rfl ψ hψ) = _
  simp only [Preadditive.comp_sub, Preadditive.comp_neg, Preadditive.neg_comp]
  simpa only [neg_neg] using (congrArg Neg.neg hz).symm

end
end Finsler.SupportedCapRepresentative

