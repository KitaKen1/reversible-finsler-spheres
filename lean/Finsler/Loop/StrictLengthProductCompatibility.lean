module

public import Finsler.Loop.StrictLengthLoopProduct

/-! The transported product is induced by its genuine closed chain
operation and the actual TauCeti cross. Both directions of comparison
with the existing energy-filtered bilinear product are exact, including
the empty-input case for arbitrary real length bounds. -/

@[expose] public section
namespace Finsler.StrictLengthProductCompatibility

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.StrictLengthEnergyBridge Finsler.StrictLengthLoopProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

theorem energy_inverse_apply {n : ℕ} (F : ReversibleMetric n) (a : ℝ) (ha : 0 < a)
    (k : ℕ) (x : PoolCap.homology (energySpace F a) k) :
    (PoolCap.push (toEnergy F a) k).hom ((PoolCap.push (toLength F a ha) k).hom x) = x := by
  have he := ConcreteCategory.congr_hom (energy_homology_inverse F a ha k) x
  change (PoolCap.push (toEnergy F a) k).hom ((PoolCap.push (toLength F a ha) k).hom x) = x at he
  exact he

variable {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n) {p q ε : ℝ}
  (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε)

theorem positive_energy_output (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    (PoolCap.push (toEnergy F (p + (q + ε))) k).hom (positiveProduct F hn hp hq hε i j k h x y) =
    FilteredBilinearLoopProduct.product hn F hp hq hε i j k h
      ((PoolCap.push (toEnergy F p) i).hom x) ((PoolCap.push (toEnergy F q) j).hom y) := by
  rw [positive_apply]
  exact energy_inverse_apply F _ (add_pos hp (add_pos hq hε)) k _

theorem positive_energy_inputs (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (energySpace F p) i) (y : PoolCap.homology (energySpace F q) j) :
    positiveProduct F hn hp hq hε i j k h
      ((PoolCap.push (toLength F p hp) i).hom x) ((PoolCap.push (toLength F q hq) j).hom y) =
    (PoolCap.push (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))) k).hom
      (FilteredBilinearLoopProduct.product hn F hp hq hε i j k h x y) := by
  rw [positive_apply, energy_inverse_apply, energy_inverse_apply]

theorem positive_chain_apply (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    positiveProduct F hn hp hq hε i j k h x y =
    ((positiveOperation F hn hp hq hε).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F p) (lengthSpace F q) i j (n + k) h x y) := by
  rw [positive_apply, FilteredBilinearLoopProduct.product_apply]
  have hc := CrossProjectionZero.cross_naturality_apply (toEnergy F p) (toEnergy F q)
    i j (n + k) h x y
  rw [hc, positive_homology]
  rfl

theorem nonpos_homology (hpos : ¬ (0 < p ∧ 0 < q)) (k : ℕ) :
    (operation F hn (p := p) (q := q) hε).homology k = 0 := by
  have hc : (operation F hn (p := p) (q := q) hε).cycles k = 0 := by
    apply (cancel_mono ((chains (lengthSpace F (p + (q + ε)))).iCycles k)).mp
    rw [DegreeLoweringHomology.Map.cycles_i, operation_nonpos F hn hε hpos k, comp_zero, zero_comp]
  apply (cancel_epi ((chains (pairSpace F p q)).homologyπ (n + k))).mp
  rw [DegreeLoweringHomology.Map.homologyπ_homology, hc, zero_comp, comp_zero]

theorem chain_apply (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    product F hn hε i j k h x y =
    ((operation F hn hε).homology k).hom
      (FilteredBilinearLoopProduct.cross (lengthSpace F p) (lengthSpace F q) i j (n + k) h x y) := by
  by_cases hpos : 0 < p ∧ 0 < q
  · rw [product_pos F hn hpos.1 hpos.2 hε, operation_pos F hn hpos.1 hpos.2 hε]
    exact positive_chain_apply F hn hpos.1 hpos.2 hε i j k h x y
  · rw [product_nonpos F hn hε hpos, nonpos_homology F hn hε hpos]
    rfl

theorem energy_output (i j k : ℕ) (h : i + j = n + k)
    (x : PoolCap.homology (lengthSpace F p) i) (y : PoolCap.homology (lengthSpace F q) j) :
    (PoolCap.push (toEnergy F (p + (q + ε))) k).hom (product F hn hε i j k h x y) =
    FilteredBilinearLoopProduct.product hn F hp hq hε i j k h
      ((PoolCap.push (toEnergy F p) i).hom x) ((PoolCap.push (toEnergy F q) j).hom y) := by
  rw [product_pos F hn hp hq hε]
  exact positive_energy_output F hn hp hq hε i j k h x y

end
end Finsler.StrictLengthProductCompatibility
