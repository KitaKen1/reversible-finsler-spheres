module

public import Finsler.Topology.CrossProjectionCap
public import Finsler.Topology.CrossProjectionZero
public import Finsler.Topology.DiagonalPullbackClass

/-! The full actual diagonal class gives the identity after the sphere-factor
Thom cut and projection. This includes the second projection term: it vanishes
by actual external-product naturality and positive-degree point homology. -/

@[expose] public section

namespace Finsler.SphereDiagonalCap

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.SphereUnitCandidate Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem diagonal_projection_cap (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    (k : ℕ) (y : PoolCap.homology Y k) :
    (PoolCap.push (snd (sphere n) Y) k).hom
      (PoolCap.cap (sphere n ⊗ Y) n k (n + k) rfl
        ((cohPullback (fst (sphere n) Y) n).hom (topClass n hn) +
          (cohPullback (snd (sphere n) Y) n).hom ((cohPullback g n).hom (topClass n hn)))
        (FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y)) = y := by
  rw [PoolCap.add_left, map_add, CrossProjectionCap.sphere_projection_cap,
    CrossProjectionZero.projection_cap_zero (sphere n) Y n k (by omega), add_zero]

theorem diagonal_cocycle_class (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n) :
    cocycleClass (sphere n ⊗ Y) n
      (DiagonalPullbackCut.cocycle hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g))
      (DiagonalPullbackCut.cocycle_closed hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g)) =
      (cohPullback (fst (sphere n) Y) n).hom (topClass n hn) +
        (cohPullback (snd (sphere n) Y) n).hom ((cohPullback g n).hom (topClass n hn)) := by
  have he := DiagonalPullbackClass.cocycle_class hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g)
  exact he.trans (by rw [Cup.pullback_comp])

def operation (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    (B : Set (sphere n × Y)) (hB : IsOpen B)
    (hdiag : ∀ z : sphere n ⊗ Y, (fst (sphere n) Y) z = (snd (sphere n) Y ≫ g) z → z ∈ B) :=
  SupportedCapHomology.operation (sphere n ⊗ Y)
    (DiagonalPullbackCut.exclusion (fst (sphere n) Y) (snd (sphere n) Y ≫ g)) B
    (DiagonalPullbackCut.exclusion_open (n := n) (fst (sphere n) Y) (snd (sphere n) Y ≫ g)) hB
    (DiagonalPullbackCut.neighborhood_cover (n := n) (fst (sphere n) Y) (snd (sphere n) Y ≫ g) B hdiag) n
    (DiagonalPullbackCut.cocycle hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g))
    (DiagonalPullbackCut.cocycle_supported hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g))
    (DiagonalPullbackCut.cocycle_closed hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g))

theorem cut_projection (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    (B : Set (sphere n × Y)) (hB : IsOpen B)
    (hdiag : ∀ z : sphere n ⊗ Y, (fst (sphere n) Y) z = (snd (sphere n) Y ≫ g) z → z ∈ B)
    (k : ℕ) (y : PoolCap.homology Y k) :
    (PoolCap.push (SupportedCap.subspaceMap (sphere n ⊗ Y) B ≫ snd (sphere n) Y) k).hom
      (((operation n hn Y g B hB hdiag).homology k).hom
        (FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y)) = y := by
  let j := SupportedCap.subspaceMap (sphere n ⊗ Y) B
  let φ := DiagonalPullbackCut.cocycle hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g)
  have hφ := DiagonalPullbackCut.cocycle_closed hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g)
  let x := FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y
  have he := SupportedCapHomology.ambient_comparison (sphere n ⊗ Y)
    (DiagonalPullbackCut.exclusion (fst (sphere n) Y) (snd (sphere n) Y ≫ g)) B
    (DiagonalPullbackCut.exclusion_open (n := n) (fst (sphere n) Y) (snd (sphere n) Y ≫ g)) hB
    (DiagonalPullbackCut.neighborhood_cover (n := n) (fst (sphere n) Y) (snd (sphere n) Y ≫ g) B hdiag) n k φ
    (DiagonalPullbackCut.cocycle_supported hn (fst (sphere n) Y) (snd (sphere n) Y ≫ g)) hφ
  calc
    _ = (PoolCap.push (snd (sphere n) Y) k).hom
        ((PoolCap.push j k).hom (((operation n hn Y g B hB hdiag).homology k).hom x)) :=
      ConcreteCategory.congr_hom
        (((singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff).map_comp j (snd (sphere n) Y)) _
    _ = (PoolCap.push (snd (sphere n) Y) k).hom
        (PoolCap.cap (sphere n ⊗ Y) n k (n + k) rfl
          (cocycleClass (sphere n ⊗ Y) n φ hφ) x) :=
      congrArg (PoolCap.push (snd (sphere n) Y) k).hom (ConcreteCategory.congr_hom he x)
    _ = y := by
      rw [diagonal_cocycle_class]
      exact diagonal_projection_cap n hn Y g k y

theorem cut_ne_zero (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    (B : Set (sphere n × Y)) (hB : IsOpen B)
    (hdiag : ∀ z : sphere n ⊗ Y, (fst (sphere n) Y) z = (snd (sphere n) Y ≫ g) z → z ∈ B)
    (k : ℕ) (y : PoolCap.homology Y k) (hy : y ≠ 0) :
    ((operation n hn Y g B hB hdiag).homology k).hom
      (FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y) ≠ 0 := by
  intro h
  have he := cut_projection n hn Y g B hB hdiag k y
  rw [h, map_zero] at he
  exact hy he.symm


end
end Finsler.SphereDiagonalCap
