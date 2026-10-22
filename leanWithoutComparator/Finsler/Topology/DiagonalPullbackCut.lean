module

public import Finsler.Topology.DiagonalCocycle
public import Finsler.Topology.SupportedCap

/-! A genuine diagonal Thom cut on any pullback of the sphere diagonal.
For maps f,g : X → Sⁿ it lands in chains of any open neighborhood of f=g.
It uses the supported relative diagonal cocycle and the actual small-chain
retraction. Filtered loop cut--join, its unit and UF remain separate. -/

@[expose] public section

namespace Finsler.DiagonalPullbackCut

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison
open Finsler.BorelEvaluation
open Finsler.DiagonalGeometry Finsler.DiagonalCohomology Finsler.DiagonalCocycle
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def exclusion {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) : Set X :=
  {x | f x ≠ g x}

def pairEvaluation {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) : X ⟶ product n :=
  TopCat.ofHom ⟨fun x => (f x, g x), f.hom.continuous.prodMk g.hom.continuous⟩

def evaluationPair {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    TopPair.ofSubset (exclusion f g) ⟶ diagonalPair n :=
  TopPair.ofSubsetMap (B := exclusion f g) (B' := deleted n) (pairEvaluation f g)
    (by intro x hx; exact hx)

theorem evaluationPair_fst {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    TopPair.Hom.fst (evaluationPair f g) = pairEvaluation f g := by
  ext x : 1
  exact TopPair.ofSubsetMap_fst_apply (B := exclusion f g) (B' := deleted n)
    (pairEvaluation f g) (by intro y hy; exact hy) x

def cocycle {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    singularCochainGroup (ZMod 2) X n :=
  RelativeCupCochain.toAmbient (TopPair.ofSubset (exclusion f g)) n
    (RelativeCupCochain.pullback (evaluationPair f g) n (relativeCocycle n hn))

theorem cocycle_comparison {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    cocycle hn f g = cochainPullback (pairEvaluation f g) n (ambientCocycle n hn) := by
  unfold cocycle
  rw [RelativeCupCochain.toAmbient_pullback, evaluationPair_fst]
  rfl

theorem cocycle_closed {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    cochainCoboundary (ZMod 2) X n (cocycle hn f g) = 0 := by
  rw [cocycle_comparison]
  exact CochainClass.closed_map (cochainCxZMod2 (product n))
    (singularCochainComplexZMod2.map (pairEvaluation f g).op)
    n (ambientCocycle n hn) (ambient_closed n hn)

theorem cocycle_supported {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    cochainPullback (SupportedCap.subspaceMap X (exclusion f g)) n (cocycle hn f g) = 0 :=
  RelativeCupCochain.restriction_toAmbient (TopPair.ofSubset (exclusion f g)) n
    (RelativeCupCochain.pullback (evaluationPair f g) n (relativeCocycle n hn))

theorem exclusion_open {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    IsOpen (exclusion f g) :=
  (isClosed_eq f.hom.continuous g.hom.continuous).isOpen_compl

theorem neighborhood_cover {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) (B : Set X)
    (hdiag : ∀ x, f x = g x → x ∈ B) : exclusion f g ∪ B = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : f x = g x
  · exact Or.inr (hdiag x h)
  · exact Or.inl h

def cut {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n)
    (B : Set X) (hB : IsOpen B) (hdiag : ∀ x, f x = g x → x ∈ B) (q : ℕ) :
    (chains X).X (n + q) ⟶ (chains (TopCat.of B)).X q :=
  SupportedCap.cut X (exclusion f g) B (exclusion_open f g) hB
    (neighborhood_cover f g B hdiag) n q (n + q) rfl (cocycle hn f g) (cocycle_supported hn f g)

theorem cut_comparison {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n)
    (B : Set X) (hB : IsOpen B) (hdiag : ∀ x, f x = g x → x ∈ B) (q : ℕ) :
    cut hn f g B hB hdiag q ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (SupportedCap.subspaceMap X B)) coeff).f q =
      (TauCeti.singularSmallApprox coeff (SupportedCap.cover X (exclusion f g) B)).f (n + q) ≫
        absoluteChain X n q (n + q) rfl (cocycle hn f g) :=
  SupportedCap.cut_inclusion X (exclusion f g) B (exclusion_open f g) hB
    (neighborhood_cover f g B hdiag) n q (n + q) rfl (cocycle hn f g) (cocycle_supported hn f g)

theorem cut_boundary {n : ℕ} (hn : 1 ≤ n) {X : TopCat.{0}} (f g : X ⟶ sphere n)
    (B : Set X) (hB : IsOpen B) (hdiag : ∀ x, f x = g x → x ∈ B) (q : ℕ) :
    cut hn f g B hB hdiag (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains X).d (n + (q + 1)) (n + q) ≫ cut hn f g B hB hdiag q := by
  unfold cut
  convert
    SupportedCap.cut_boundary X (exclusion f g) B (exclusion_open f g) hB
      (neighborhood_cover f g B hdiag) n q (n + q) rfl (cocycle hn f g)
      (cocycle_supported hn f g) (cocycle_closed hn f g) using 1


end
end Finsler.DiagonalPullbackCut
