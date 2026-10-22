module

public import Finsler.Topology.SphereDiagonalCap
public import Finsler.Topology.NormalizedDiagonalCocycle

/-! A shortcut for the forthcoming local multiplicity calculation:
the ORIGINAL normalized, radius-dependent diagonal cochain gives
exactly the identity after a sphere-factor graph cap and projection.
This is an ACTUAL cap computation with the real small-chain retraction.
Transporting native matching branches to this sphere-factor input is
still required; this theorem does not assign their multiplicities. -/
@[expose] public section
namespace Finsler.NormalizedSphereGraphCap
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation Finsler.SphereTopClass
open Finsler.SphereUnitCandidate Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def evaluation (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) : sphere n ⊗ Y ⟶ DiagonalCohomology.product n :=
  DiagonalPullbackCut.pairEvaluation (fst (sphere n) Y) (snd (sphere n) Y ≫ g)

def distance (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) (z : sphere n × Y) : ℝ :=
  ‖(g z.2 : Ambient n) - z.1‖

theorem continuous_distance (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) : Continuous (distance n Y g) :=
  (((continuous_subtype_val.comp g.hom.continuous).comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).norm

def exterior (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) (ρ : ℝ) : Set (sphere n × Y) :=
  {z | ρ < distance n Y g z}
def neighborhood (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) (r : ℝ) : Set (sphere n × Y) :=
  {z | distance n Y g z < r}

theorem exterior_open (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) (ρ : ℝ) : IsOpen (exterior n Y g ρ) :=
  isOpen_lt continuous_const (continuous_distance n Y g)
theorem neighborhood_open (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) (r : ℝ) :
    IsOpen (neighborhood n Y g r) := isOpen_lt (continuous_distance n Y g) continuous_const

theorem cover (n : ℕ) (Y : TopCat.{0}) (g : Y ⟶ sphere n) {ρ r : ℝ} (hρr : ρ < r) :
    exterior n Y g ρ ∪ neighborhood n Y g r = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : ρ < distance n Y g z
  · exact Or.inl hz
  · exact Or.inr ((le_of_not_gt hz).trans_lt hρr)

def cocycle (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (sphere n ⊗ Y) n :=
  cochainPullback (evaluation n Y g) n (NormalizedDiagonalCocycle.ambient n hn hρ)

theorem cocycle_closed (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (sphere n ⊗ Y) n (cocycle n hn Y g hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (evaluation n Y g).op) n _
    (NormalizedDiagonalCocycle.ambient_closed n hn hρ)

theorem cocycle_supported (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (sphere n ⊗ Y) (exterior n Y g ρ)) n (cocycle n hn Y g hρ) = 0 := by
  rw [cocycle, ← SupportedCapNaturality.pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ
  intro z
  change ρ ≤ distance n Y g z.val
  exact z.property.le

theorem cocycle_class (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n) {ρ : ℝ} (hρ : 0 < ρ) :
    cocycleClass (sphere n ⊗ Y) n (cocycle n hn Y g hρ) (cocycle_closed n hn Y g hρ) =
      (cohPullback (fst (sphere n) Y) n).hom (topClass n hn) +
        (cohPullback (snd (sphere n) Y) n).hom ((cohPullback g n).hom (topClass n hn)) := by
  have he := CochainClass.classOf_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (evaluation n Y g).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)
    (cocycle_closed n hn Y g hρ)
  rw [NormalizedDiagonalCocycle.ambient_class] at he
  calc
    _ = (cohPullback (evaluation n Y g) n).hom (DiagonalCohomology.ambientClass n hn) := he.symm
    _ = _ := by
      unfold DiagonalCohomology.ambientClass evaluation
      rw [map_add, ← Cup.pullback_comp, ← Cup.pullback_comp,
        DiagonalPullbackClass.pair_first, DiagonalPullbackClass.pair_second, Cup.pullback_comp]

def operation (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :=
  SupportedCapHomology.operation (sphere n ⊗ Y) (exterior n Y g ρ) (neighborhood n Y g r)
    (exterior_open n Y g ρ) (neighborhood_open n Y g r) (cover n Y g hρr) n
    (cocycle n hn Y g hρ) (cocycle_supported n hn Y g hρ) (cocycle_closed n hn Y g hρ)

theorem cut_projection (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (k : ℕ) (y : PoolCap.homology Y k) :
    (PoolCap.push (SupportedCap.subspaceMap (sphere n ⊗ Y) (neighborhood n Y g r) ≫ snd (sphere n) Y) k).hom
      (((operation n hn Y g hρ hρr).homology k).hom
        (FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y)) = y := by
  let j := SupportedCap.subspaceMap (sphere n ⊗ Y) (neighborhood n Y g r)
  let φ := cocycle n hn Y g hρ
  have hφ := cocycle_closed n hn Y g hρ
  let x := FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y
  have he := SupportedCapHomology.ambient_comparison (sphere n ⊗ Y)
    (exterior n Y g ρ) (neighborhood n Y g r) (exterior_open n Y g ρ)
    (neighborhood_open n Y g r) (cover n Y g hρr) n k φ (cocycle_supported n hn Y g hρ) hφ
  calc
    _ = (PoolCap.push (snd (sphere n) Y) k).hom
        ((PoolCap.push j k).hom (((operation n hn Y g hρ hρr).homology k).hom x)) :=
      ConcreteCategory.congr_hom
        (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).map_comp j (snd (sphere n) Y)) _
    _ = (PoolCap.push (snd (sphere n) Y) k).hom
        (PoolCap.cap (sphere n ⊗ Y) n k (n + k) rfl (cocycleClass (sphere n ⊗ Y) n φ hφ) x) :=
      congrArg (PoolCap.push (snd (sphere n) Y) k).hom (ConcreteCategory.congr_hom he x)
    _ = y := by
      rw [cocycle_class]
      exact SphereDiagonalCap.diagonal_projection_cap n hn Y g k y

theorem cut_ne_zero (n : ℕ) (hn : 1 ≤ n) (Y : TopCat.{0}) (g : Y ⟶ sphere n)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (k : ℕ) (y : PoolCap.homology Y k) (hy : y ≠ 0) :
    ((operation n hn Y g hρ hρr).homology k).hom
      (FilteredBilinearLoopProduct.cross (sphere n) Y n k (n + k) rfl (fundamental n hn) y) ≠ 0 := by
  intro hz
  have he := cut_projection n hn Y g hρ hρr k y
  rw [hz, map_zero] at he
  exact hy he.symm

end
end Finsler.NormalizedSphereGraphCap
