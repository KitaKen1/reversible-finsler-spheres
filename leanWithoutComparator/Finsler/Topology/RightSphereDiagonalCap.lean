module

public import Finsler.Topology.CrossRightProjectionCap
public import Finsler.Topology.DiagonalCutNaturality
public import Finsler.Topology.DiagonalPullbackClass

/-! The full diagonal Thom cut on X times the sphere projects back to X. -/

@[expose] public section

namespace Finsler.RightSphereDiagonalCap

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.SphereUnitCandidate Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem diagonal_projection_cap (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) (g : X ⟶ sphere n)
    (k : ℕ) (x : PoolCap.homology X k) :
    (PoolCap.push (fst X (sphere n)) k).hom
      (PoolCap.cap (X ⊗ sphere n) n k (n + k) rfl
        ((cohPullback (fst X (sphere n)) n).hom ((cohPullback g n).hom (topClass n hn)) +
          (cohPullback (snd X (sphere n)) n).hom (topClass n hn))
        (FilteredBilinearLoopProduct.cross X (sphere n) k n (n + k) (Nat.add_comm k n)
          x (fundamental n hn))) = x := by
  rw [PoolCap.add_left, map_add, CrossRightProjectionCap.projection_cap_zero X (sphere n) k n
    (n + k) (Nat.add_comm k n) (by omega), CrossRightProjectionCap.sphere_projection_cap, zero_add]

theorem diagonal_cocycle_class (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) (g : X ⟶ sphere n) :
    cocycleClass (X ⊗ sphere n) n
      (DiagonalPullbackCut.cocycle hn (fst X (sphere n) ≫ g) (snd X (sphere n)))
      (DiagonalPullbackCut.cocycle_closed hn (fst X (sphere n) ≫ g) (snd X (sphere n))) =
      (cohPullback (fst X (sphere n)) n).hom ((cohPullback g n).hom (topClass n hn)) +
        (cohPullback (snd X (sphere n)) n).hom (topClass n hn) := by
  exact (DiagonalPullbackClass.cocycle_class hn (fst X (sphere n) ≫ g) (snd X (sphere n))).trans
    (by rw [Cup.pullback_comp])

def operation (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) (g : X ⟶ sphere n)
    (B : Set (X × sphere n)) (hB : IsOpen B)
    (hdiag : ∀ z : X ⊗ sphere n, (fst X (sphere n) ≫ g) z = (snd X (sphere n)) z → z ∈ B) :=
  DiagonalCutNaturality.operation hn (fst X (sphere n) ≫ g) (snd X (sphere n)) B hB hdiag

theorem cut_projection (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) (g : X ⟶ sphere n)
    (B : Set (X × sphere n)) (hB : IsOpen B)
    (hdiag : ∀ z : X ⊗ sphere n, (fst X (sphere n) ≫ g) z = (snd X (sphere n)) z → z ∈ B)
    (k : ℕ) (x : PoolCap.homology X k) :
    (PoolCap.push (SupportedCap.subspaceMap (X ⊗ sphere n) B ≫ fst X (sphere n)) k).hom
      (((operation n hn X g B hB hdiag).homology k).hom
        (FilteredBilinearLoopProduct.cross X (sphere n) k n (n + k) (Nat.add_comm k n)
          x (fundamental n hn))) = x := by
  let j := SupportedCap.subspaceMap (X ⊗ sphere n) B
  let f := fst X (sphere n) ≫ g
  let s := snd X (sphere n)
  let φ := DiagonalPullbackCut.cocycle hn f s
  have hc := DiagonalPullbackCut.cocycle_closed hn f s
  let z := FilteredBilinearLoopProduct.cross X (sphere n) k n (n + k) (Nat.add_comm k n)
    x (fundamental n hn)
  have he := SupportedCapHomology.ambient_comparison (X ⊗ sphere n)
    (DiagonalPullbackCut.exclusion f s) B (DiagonalPullbackCut.exclusion_open (n := n) f s) hB
    (DiagonalPullbackCut.neighborhood_cover (n := n) f s B hdiag) n k φ
    (DiagonalPullbackCut.cocycle_supported hn f s) hc
  calc
    _ = (PoolCap.push (fst X (sphere n)) k).hom
        ((PoolCap.push j k).hom (((operation n hn X g B hB hdiag).homology k).hom z)) :=
      ConcreteCategory.congr_hom
        (((singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff).map_comp j (fst X (sphere n))) _
    _ = (PoolCap.push (fst X (sphere n)) k).hom
        (PoolCap.cap (X ⊗ sphere n) n k (n + k) rfl
          (cocycleClass (X ⊗ sphere n) n φ hc) z) :=
      congrArg (PoolCap.push (fst X (sphere n)) k).hom (ConcreteCategory.congr_hom he z)
    _ = x := by
      rw [diagonal_cocycle_class]
      exact diagonal_projection_cap n hn X g k x

theorem cut_ne_zero (n : ℕ) (hn : 1 ≤ n) (X : TopCat.{0}) (g : X ⟶ sphere n)
    (B : Set (X × sphere n)) (hB : IsOpen B)
    (hdiag : ∀ z : X ⊗ sphere n, (fst X (sphere n) ≫ g) z = (snd X (sphere n)) z → z ∈ B)
    (k : ℕ) (x : PoolCap.homology X k) (hx : x ≠ 0) :
    ((operation n hn X g B hB hdiag).homology k).hom
      (FilteredBilinearLoopProduct.cross X (sphere n) k n (n + k) (Nat.add_comm k n)
        x (fundamental n hn)) ≠ 0 := by
  intro h
  have he := cut_projection n hn X g B hB hdiag k x
  rw [h, map_zero] at he
  exact hx he.symm

end
end Finsler.RightSphereDiagonalCap

