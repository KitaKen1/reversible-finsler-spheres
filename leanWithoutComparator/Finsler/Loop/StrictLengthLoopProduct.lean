module

public import Finsler.Loop.StrictLengthEnergyBridge
public import Finsler.Topology.FilteredBilinearLoopProduct
public import Finsler.Topology.CrossProjectionZero

/-! A genuine length-filtered product transported through the actual
arclength-normalization equivalence to the existing energy-filtered
product. Nonpositive input bounds give the forced empty-input case. -/

@[expose] public section
namespace Finsler.StrictLengthLoopProduct

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ)

abbrev pairSpace : TopCat.{0} := lengthSpace F p ⊗ lengthSpace F q

def pairMap : pairSpace F p q ⟶ FilteredLoopProduct.loopPairs F p q :=
  toEnergy F p ⊗ₘ toEnergy F q

theorem pair_level_pos (z : pairSpace F p q) : 0 < p ∧ 0 < q :=
  ⟨level_pos F p z.1, level_pos F q z.2⟩

theorem pair_empty (h : ¬ (0 < p ∧ 0 < q)) : IsEmpty (pairSpace F p q) :=
  ⟨fun z => (h (pair_level_pos F p q z)).elim⟩

variable (hn : 1 ≤ n) {p q ε : ℝ} (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε)

def positiveOperation :=
  ((FilteredLoopProductHomology.productOperation hn F hp hq hε).pre (push (pairMap F p q))).post
    (push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))))

theorem positive_component (k : ℕ) :
    (positiveOperation F hn hp hq hε).component k =
    (push (pairMap F p q)).f (n + k) ≫
      (FilteredLoopProductHomology.productOperation hn F hp hq hε).component k ≫
      (push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε)))).f k := rfl

theorem positive_homology (k : ℕ) :
    (positiveOperation F hn hp hq hε).homology k =
    HomologicalComplex.homologyMap (push (pairMap F p q)) (n + k) ≫
      FilteredLoopProductHomology.homology hn F hp hq hε k ≫
      HomologicalComplex.homologyMap (push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε)))) k := by
  rw [positiveOperation, DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.pre_homology]
  rfl

def operation : DegreeLoweringHomology.Map (chains (pairSpace F p q))
    (chains (lengthSpace F (p + (q + ε)))) n :=
  if h : 0 < p ∧ 0 < q then positiveOperation F hn h.1 h.2 hε else
    { component := fun _ => 0
      comm := fun _ => by simp only [zero_comp, comp_zero] }

theorem operation_pos : operation F hn (p := p) (q := q) hε = positiveOperation F hn hp hq hε := by
  rw [operation, dite_eq_left ⟨hp, hq⟩]

theorem operation_nonpos (h : ¬ (0 < p ∧ 0 < q)) (k : ℕ) :
    (operation F hn (p := p) (q := q) hε).component k = 0 := by
  rw [operation, dite_eq_right h]

def positiveProduct (i j k : ℕ) (h : i + j = n + k) :
    PoolCap.homology (lengthSpace F p) i →ₗ[ZMod 2]
      PoolCap.homology (lengthSpace F q) j →ₗ[ZMod 2]
        PoolCap.homology (lengthSpace F (p + (q + ε))) k :=
  (((FilteredBilinearLoopProduct.product hn F hp hq hε i j k h).comp
    (PoolCap.push (toEnergy F p) i).hom).compl₂ (PoolCap.push (toEnergy F q) j).hom).compr₂
    (PoolCap.push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))) k).hom

theorem positive_apply (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    positiveProduct F hn hp hq hε i j k h x y =
    (PoolCap.push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))) k).hom
      (FilteredBilinearLoopProduct.product hn F hp hq hε i j k h
        ((PoolCap.push (toEnergy F p) i).hom x) ((PoolCap.push (toEnergy F q) j).hom y)) := rfl

def product (i j k : ℕ) (h : i + j = n + k) :
    PoolCap.homology (lengthSpace F p) i →ₗ[ZMod 2]
      PoolCap.homology (lengthSpace F q) j →ₗ[ZMod 2]
        PoolCap.homology (lengthSpace F (p + (q + ε))) k :=
  if hpos : 0 < p ∧ 0 < q then positiveProduct F hn hpos.1 hpos.2 hε i j k h else 0

theorem product_pos (i j k : ℕ) (h : i + j = n + k) :
    product F hn (p := p) (q := q) hε i j k h = positiveProduct F hn hp hq hε i j k h := by
  rw [product, dite_eq_left ⟨hp, hq⟩]

theorem product_nonpos (hpos : ¬ (0 < p ∧ 0 < q)) (i j k : ℕ) (h : i + j = n + k) :
    product F hn (p := p) (q := q) hε i j k h = 0 := by
  rw [product, dite_eq_right hpos]

end
end Finsler.StrictLengthLoopProduct
