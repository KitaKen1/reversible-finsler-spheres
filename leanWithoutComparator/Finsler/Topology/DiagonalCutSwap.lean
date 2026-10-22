module

public import Finsler.Topology.SupportedCapRepresentative
public import Finsler.Topology.DiagonalSwapPrimitive
public import Finsler.Topology.DiagonalCutNaturality

/-! The specified diagonal Thom cut is symmetric directly in neighborhood homology.
The correction comes from the actual supported relative diagonal primitive. -/

@[expose] public section

namespace Finsler.DiagonalCutSwap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalCohomology Finsler.DiagonalSymmetry Finsler.DiagonalSwapPrimitive
open Finsler.DiagonalGeometry
open Finsler.DiagonalPullbackCut Finsler.SmallChainCarrier Finsler.SupportedCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) Y p) :
    cochainPullback f p (φ - ψ) = cochainPullback f p φ - cochainPullback f p ψ :=
  map_sub ((singularCochainComplexZMod2.map f.op).f p).hom φ ψ

theorem pullback_coboundary {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (κ : singularCochainGroup (ZMod 2) Y p) :
    cochainCoboundary (ZMod 2) X p (cochainPullback f p κ) =
      cochainPullback f (p + 1) (cochainCoboundary (ZMod 2) Y p κ) :=
  ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm p (p + 1)) κ

theorem pairEvaluation_exchange {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    pairEvaluation f g ≫ exchange n = pairEvaluation g f := by
  ext x : 1
  rfl

theorem exclusion_swap {n : ℕ} {X : TopCat.{0}} (f g : X ⟶ sphere n) :
    exclusion g f = exclusion f g := by
  ext x
  exact ne_comm

def primitive (p : ℕ) (hp : 1 ≤ p) {X : TopCat.{0}} (f g : X ⟶ sphere (p + 1)) :
    singularCochainGroup (ZMod 2) X p :=
  cochainPullback (pairEvaluation f g) p (ambientPrimitive (p + 1) (by omega))

theorem primitive_supported (p : ℕ) (hp : 1 ≤ p) {X : TopCat.{0}}
    (f g : X ⟶ sphere (p + 1)) :
    cochainPullback (subspaceMap X (exclusion f g)) p (primitive p hp f g) = 0 := by
  have hs : cochainPullback (subspaceMap (product (p + 1)) (deleted (p + 1))) p
      (ambientPrimitive (p + 1) (by omega)) = 0 := ambientPrimitive_supported (p + 1) (by omega)
  exact SupportedCapNaturality.pullback_support (pairEvaluation f g) (exclusion f g)
    (deleted (p + 1)) (fun _ hx => hx) p (ambientPrimitive (p + 1) (by omega)) hs

theorem primitive_boundary (p : ℕ) (hp : 1 ≤ p) {X : TopCat.{0}}
    (f g : X ⟶ sphere (p + 1)) :
    cochainCoboundary (ZMod 2) X p (primitive p hp f g) =
      cocycle (by omega : 1 ≤ p + 1) g f - cocycle (by omega : 1 ≤ p + 1) f g := by
  rw [primitive, pullback_coboundary]
  have hb : cochainCoboundary (ZMod 2) (product (p + 1)) p
      (ambientPrimitive (p + 1) (by omega)) =
      cochainPullback (exchange (p + 1)) (p + 1) (DiagonalCocycle.ambientCocycle (p + 1) (by omega)) -
        DiagonalCocycle.ambientCocycle (p + 1) (by omega) :=
    ambientPrimitive_boundary (p + 1) (by omega)
  rw [hb, pullback_sub, ← SupportedCapNaturality.pullback_comp, pairEvaluation_exchange,
    ← cocycle_comparison, ← cocycle_comparison]

theorem homology_swap (p : ℕ) (hp : 1 ≤ p) {X : TopCat.{0}}
    (f g : X ⟶ sphere (p + 1)) (B : Set X) (hB : IsOpen B)
    (hdiag : ∀ x, f x = g x → x ∈ B) (q : ℕ) :
    (DiagonalCutNaturality.operation (by omega : 1 ≤ p + 1) f g B hB hdiag).homology q =
      (DiagonalCutNaturality.operation (by omega : 1 ≤ p + 1) g f B hB
        (fun x hx => hdiag x hx.symm)).homology q := by
  let A := exclusion f g
  have hs : cochainPullback (subspaceMap X A) (p + 1) (cocycle (by omega) g f) = 0 := by
    change cochainPullback (subspaceMap X (exclusion f g)) (p + 1) _ = 0
    rw [← exclusion_swap f g]
    exact cocycle_supported (by omega) g f
  have he := SupportedCapRepresentative.homology_eq X A B (exclusion_open (n := p + 1) f g) hB
    (neighborhood_cover (n := p + 1) f g B hdiag) p q
    (cocycle (by omega) g f) (cocycle (by omega) f g) hs (cocycle_supported (by omega) f g)
    (cocycle_closed (by omega) g f) (cocycle_closed (by omega) f g)
    (primitive p hp f g) (primitive_supported p hp f g) (primitive_boundary p hp f g)
  simpa only [DiagonalCutNaturality.operation, exclusion_swap f g, A] using he.symm

end
end Finsler.DiagonalCutSwap

