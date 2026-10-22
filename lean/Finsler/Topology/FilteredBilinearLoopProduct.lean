module

public import Finsler.Topology.FilteredLoopProductHomology
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-! The actual external homology product supplies a bilinear filtered loop
product. The fixed Tau Ceti shuffle construction is used with coefficient
multiplication and TopCat's chosen concrete product. No unit is assumed. -/

@[expose] public section

namespace Finsler.FilteredBilinearLoopProduct

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.FilteredLoopProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def crossMap (X Y : TopCat.{0}) (i j m : ℕ) (h : i + j = m) :
    PoolCap.homology X i ⊗ PoolCap.homology Y j ⟶ PoolCap.homology (TopCat.of (X × Y)) m :=
  TopCat.singularHomologyCross X Y coeff coeff i j m h ≫
    ((singularHomologyFunctor (ModuleCat (ZMod 2)) m).map (λ_ coeff).hom).app (X ⊗ Y)

def cross (X Y : TopCat.{0}) (i j m : ℕ) (h : i + j = m) :
    PoolCap.homology X i →ₗ[ZMod 2]
      PoolCap.homology Y j →ₗ[ZMod 2] PoolCap.homology (TopCat.of (X × Y)) m :=
  (TensorProduct.mk (ZMod 2) (PoolCap.homology X i) (PoolCap.homology Y j)).compr₂
    (crossMap X Y i j m h).hom

theorem cross_apply (X Y : TopCat.{0}) (i j m : ℕ) (h : i + j = m)
    (x : PoolCap.homology X i) (y : PoolCap.homology Y j) :
    cross X Y i j m h x y = (crossMap X Y i j m h).hom (x ⊗ₜ[ZMod 2] y) := rfl

def product {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (i j k : ℕ) (h : i + j = n + k) :
    PoolCap.homology (TopCat.of (lev F p)) i →ₗ[ZMod 2]
      PoolCap.homology (TopCat.of (lev F q)) j →ₗ[ZMod 2]
        PoolCap.homology (TopCat.of (lev F (p + (q + ε)))) k :=
  (cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) i j (n + k) h).compr₂
    (FilteredLoopProductHomology.homology hn F hp hq hε k).hom

theorem product_apply {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (TopCat.of (lev F p)) i)
    (y : PoolCap.homology (TopCat.of (lev F q)) j) :
    product hn F hp hq hε i j k h x y =
      (FilteredLoopProductHomology.homology hn F hp hq hε k).hom
        (cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) i j (n + k) h x y) := rfl

theorem product_thom_factor {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (TopCat.of (lev F p)) i)
    (y : PoolCap.homology (TopCat.of (lev F q)) j) :
    product hn F hp hq hε i j k h x y =
      (HomologicalComplex.homologyMap (NearJoinChains.joinChainMap F hp hq hε) k).hom
        (((FilteredLoopProductHomology.thomOperation hn F p hq hε).homology k).hom
          (cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) i j (n + k) h x y)) := by
  exact ConcreteCategory.congr_hom
    (FilteredLoopProductHomology.product_homology_factor hn F hp hq hε k)
    (cross (TopCat.of (lev F p)) (TopCat.of (lev F q)) i j (n + k) h x y)


end
end Finsler.FilteredBilinearLoopProduct
