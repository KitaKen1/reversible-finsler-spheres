module

public import Finsler.Topology.SelfCutThomCocycle
public import Finsler.Topology.SupportedCapHomology

/-! The actual first Thom stage of self-cutting, with the new cochain
vanishing on both far and diagonal. Its output retains both actual short-arc
cut loops. Crossing with the time interval, the T-cap, normalization and
whole-parent filtered comparisons remain to construct the specified D_T. -/

@[expose] public section
namespace Finsler.SupportedSelfCut

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1FiberBase Finsler.H1SelfCutNeighborhood
open Finsler.SelfCutThomCocycle Finsler.SmallChainCarrier
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def distance (n : ℕ) (z : parameters n) : ℝ :=
  ‖(endpoint z : Ambient n) - (point z.2 : Ambient n)‖

theorem continuous_distance (n : ℕ) : Continuous (distance n) :=
  ((continuous_subtype_val.comp continuous_endpoint).sub
    (continuous_subtype_val.comp (continuous_point.comp continuous_snd))).norm

def exterior (n : ℕ) (ρ : ℝ) : Set (parameters n) := {z | ρ < distance n z}

def neighborhood (n : ℕ) (r : ℝ) : Set (parameters n) := {z | distance n z < r}

theorem exterior_open (n : ℕ) (ρ : ℝ) : IsOpen (exterior n ρ) :=
  isOpen_lt continuous_const (continuous_distance n)

theorem neighborhood_open (n : ℕ) (r : ℝ) : IsOpen (neighborhood n r) :=
  isOpen_lt (continuous_distance n) continuous_const

theorem cover (n : ℕ) {ρ r : ℝ} (hr : ρ < r) :
    exterior n ρ ∪ neighborhood n r = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases h : ρ < distance n z
  · exact Or.inl h
  · exact Or.inr ((le_of_not_gt h).trans_lt hr)

theorem cocycle_supported (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) n
      (SelfCutThomCocycle.cocycle n hn hρ) = 0 := by
  rw [SelfCutThomCocycle.cocycle, ← SupportedCapNaturality.pullback_comp]
  apply pullback_zero_of_far hn hρ
  intro z
  exact z.property.le

def operation (n : ℕ) (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ) (hr : ρ < r) :=
  SupportedCapHomology.operation (parameters n) (exterior n ρ) (neighborhood n r)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hr) n
    (SelfCutThomCocycle.cocycle n hn hρ) (cocycle_supported n hn hρ)
    (SelfCutThomCocycle.cocycle_closed n hn hρ)

def toTube (n : ℕ) {r : ℝ} (hr : r ≤ 1) : C(neighborhood n r, tube n) :=
  ⟨fun z => ⟨z.val, z.property.trans_le hr⟩, continuous_subtype_val.subtype_mk _⟩

def tested (n : ℕ) {r : ℝ} (hr : r ≤ 1) : C(neighborhood n r, SphereLoop n) :=
  ⟨fun z => left (toTube n hr z), continuous_left.comp (toTube n hr).continuous⟩

def retained (n : ℕ) {r : ℝ} (hr : r ≤ 1) : C(neighborhood n r, SphereLoop n) :=
  ⟨fun z => right (toTube n hr z), continuous_right.comp (toTube n hr).continuous⟩

def output (n : ℕ) {r : ℝ} (hr : r ≤ 1) :
    TopCat.of (neighborhood n r) ⟶ TopCat.of (SphereLoop n × SphereLoop n) :=
  TopCat.ofHom ⟨fun z => (tested n hr z, retained n hr z),
    (tested n hr).continuous.prodMk (retained n hr).continuous⟩

def twoLoopOperation (n : ℕ) (hn : 1 ≤ n) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :=
  (operation n hn hρ hρr).post (SupportedCapNaturality.push (output n hr))

theorem tested_basepoint (n : ℕ) {r : ℝ} (hr : r ≤ 1) (z : neighborhood n r) :
    Finsler.CompactH1Alignment.basepoint (tested n hr z) =
      Finsler.CompactH1Alignment.basepoint z.val.2 := basepoint_left _

theorem retained_basepoint (n : ℕ) {r : ℝ} (hr : r ≤ 1) (z : neighborhood n r) :
    Finsler.CompactH1Alignment.basepoint (retained n hr z) =
      Finsler.CompactH1Alignment.basepoint z.val.2 := basepoint_right _

end
end Finsler.SupportedSelfCut
