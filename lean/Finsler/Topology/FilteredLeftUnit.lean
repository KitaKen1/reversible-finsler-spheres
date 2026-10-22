module

public import Finsler.Topology.ConstantJoinHomotopy

/-! The actual constant-loop fundamental class acts as a filtered left unit,
with exactly the original inclusion into the controlled output cut. -/

@[expose] public section

namespace Finsler.FilteredLeftUnit

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.H1NearJoin
open Finsler.SphereUnitCandidate Finsler.ConstantThomUnit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def inclusion {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    TopCat.of (lev F q) ⟶ TopCat.of (lev F (p + (q + ε))) :=
  TopCat.ofHom ⟨fun u => ⟨u.val, lev_mono F (by linarith) u.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def projection {n : ℕ} (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    TopCat.of (neighborhood F p hq hε) ⟶ TopCat.of (lev F q) :=
  SupportedCap.subspaceMap (sphere n ⊗ TopCat.of (lev F q)) (neighborhood F p hq hε) ≫
    snd (sphere n) (TopCat.of (lev F q))

theorem joined_factor {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    restriction F p hq hε ≫ NearJoinChains.nearJoinMorphism F hp hq hε =
      TopCat.ofHom (ConstantJoinHomotopy.joined F hp hq hε) := by
  ext z : 1
  rfl

theorem original_factor {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    TopCat.ofHom (ConstantJoinHomotopy.original F hp hq hε) =
      projection F p hq hε ≫ inclusion F hp hq hε := by
  ext z : 1
  rfl

theorem homology_join_factor {n : ℕ} (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ) :
    PoolCap.push (restriction F p hq hε) k ≫
        PoolCap.push (NearJoinChains.nearJoinMorphism F hp hq hε) k =
      PoolCap.push (projection F p hq hε) k ≫ PoolCap.push (inclusion F hp hq hε) k := by
  let H := (singularHomologyFunctor (ModuleCat (ZMod 2)) k).obj coeff
  calc
    _ = PoolCap.push (restriction F p hq hε ≫ NearJoinChains.nearJoinMorphism F hp hq hε) k :=
      (H.map_comp _ _).symm
    _ = PoolCap.push (TopCat.ofHom (ConstantJoinHomotopy.joined F hp hq hε)) k :=
      congrArg (fun f => PoolCap.push f k) (joined_factor F hp hq hε)
    _ = PoolCap.push (TopCat.ofHom (ConstantJoinHomotopy.original F hp hq hε)) k :=
      ConstantJoinHomotopy.homology_joined F hp hq hε k
    _ = PoolCap.push (projection F p hq hε ≫ inclusion F hp hq hε) k :=
      congrArg (fun f => PoolCap.push f k) (original_factor F hp hq hε)
    _ = _ := H.map_comp _ _

theorem left_unit {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (k : ℕ)
    (y : PoolCap.homology (TopCat.of (lev F q)) k) :
    FilteredBilinearLoopProduct.product hn F hp hq hε n k k rfl (candidate hn F p) y =
      (PoolCap.push (inclusion F hp hq hε) k).hom y := by
  rw [FilteredBilinearLoopProduct.product_thom_factor, ConstantThomUnit.thom_factor]
  let x := ((sphereOperation hn F p hq hε).homology k).hom
    (FilteredBilinearLoopProduct.cross (sphere n) (TopCat.of (lev F q)) n k (n + k) rfl
      (fundamental n hn) y)
  change (PoolCap.push (NearJoinChains.nearJoinMorphism F hp hq hε) k).hom
    ((PoolCap.push (restriction F p hq hε) k).hom x) = _
  calc
    _ = (PoolCap.push (inclusion F hp hq hε) k).hom
        ((PoolCap.push (projection F p hq hε) k).hom x) :=
      ConcreteCategory.congr_hom (homology_join_factor F hp hq hε k) x
    _ = _ := congrArg (PoolCap.push (inclusion F hp hq hε) k).hom
      (SphereDiagonalCap.cut_projection n hn (TopCat.of (lev F q)) (evaluation F q)
        (neighborhood F p hq hε) (neighborhood_open F p hq hε)
        (neighborhood_diagonal F p hq hε) k y)

end
end Finsler.FilteredLeftUnit

