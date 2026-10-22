module

public import Finsler.Topology.RightConstantJoinHomotopy

/-! The genuine constant-loop fundamental class is a filtered right unit. -/

@[expose] public section

namespace Finsler.FilteredRightUnit

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.H1NearJoin
open Finsler.SphereUnitCandidate Finsler.RightConstantThomUnit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def inclusion {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    TopCat.of (lev F p) ⟶ TopCat.of (lev F (p + (q + ε))) :=
  TopCat.ofHom ⟨fun u => ⟨u.val, lev_mono F (by linarith) u.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def projection {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    TopCat.of (neighborhood F p hq hε) ⟶ TopCat.of (lev F p) :=
  SupportedCap.subspaceMap (TopCat.of (lev F p) ⊗ sphere n) (neighborhood F p hq hε) ≫
    fst (TopCat.of (lev F p)) (sphere n)

theorem joined_factor {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    restriction F p hq hε ≫ NearJoinChains.nearJoinMorphism F hp hq hε =
      TopCat.ofHom (RightConstantJoinHomotopy.joined F hp hq hε) := by ext z : 1; rfl

theorem original_factor {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    TopCat.ofHom (RightConstantJoinHomotopy.original F hp hq hε) =
      projection F p hq hε ≫ inclusion F hp hq hε := by ext z : 1; rfl

theorem homology_join_factor {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    PoolCap.push (restriction F p hq hε) k ≫
        PoolCap.push (NearJoinChains.nearJoinMorphism F hp hq hε) k =
      PoolCap.push (projection F p hq hε) k ≫ PoolCap.push (inclusion F hp hq hε) k := by
  let H := (singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff
  calc
    _ = PoolCap.push (restriction F p hq hε ≫ NearJoinChains.nearJoinMorphism F hp hq hε) k :=
      (H.map_comp _ _).symm
    _ = PoolCap.push (TopCat.ofHom (RightConstantJoinHomotopy.joined F hp hq hε)) k :=
      congrArg (fun f => PoolCap.push f k) (joined_factor F hp hq hε)
    _ = PoolCap.push (TopCat.ofHom (RightConstantJoinHomotopy.original F hp hq hε)) k :=
      RightConstantJoinHomotopy.homology_joined F hp hq hε k
    _ = PoolCap.push (projection F p hq hε ≫ inclusion F hp hq hε) k :=
      congrArg (fun f => PoolCap.push f k) (original_factor F hp hq hε)
    _ = _ := H.map_comp _ _

theorem right_unit {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ)
    (x : PoolCap.homology (TopCat.of (lev F p)) k) :
    FilteredBilinearLoopProduct.product hn F hp hq hε k n k (Nat.add_comm k n) x (candidate hn F q) =
      (PoolCap.push (inclusion F hp hq hε) k).hom x := by
  rw [FilteredBilinearLoopProduct.product_thom_factor, RightConstantThomUnit.thom_factor]
  let z := ((sphereOperation hn F p hq hε).homology k).hom
    (FilteredBilinearLoopProduct.cross (TopCat.of (lev F p)) (sphere n) k n (n + k) (Nat.add_comm k n)
      x (fundamental n hn))
  change (PoolCap.push (NearJoinChains.nearJoinMorphism F hp hq hε) k).hom
    ((PoolCap.push (restriction F p hq hε) k).hom z) = _
  calc
    _ = (PoolCap.push (inclusion F hp hq hε) k).hom
        ((PoolCap.push (projection F p hq hε) k).hom z) :=
      ConcreteCategory.congr_hom (homology_join_factor F hp hq hε k) z
    _ = _ := congrArg (PoolCap.push (inclusion F hp hq hε) k).hom
      (RightSphereDiagonalCap.cut_projection n hn (TopCat.of (lev F p)) (evaluation F p)
        (neighborhood F p hq hε) (neighborhood_open F p hq hε)
        (neighborhood_diagonal F p hq hε) k x)

end
end Finsler.FilteredRightUnit
