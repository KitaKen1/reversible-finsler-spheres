module

public import Finsler.Topology.AnnularCutComparison
public import Finsler.Topology.TimeShuffleComparison

/-! Literal annihilation by the actual annular tested cut, also after its
small-chain retraction, for entire chains and time prisms inside a collar.
The compact-family collar is selected before all tested degrees and cochains. -/

@[expose] public section
namespace Finsler.AnnularCollarCut

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem cut_map_zero_of_distance (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (q : ℕ) {Y : TopCat.{0}} (f : Y ⟶ parameters (m + 1))
    (hf : ∀ y, distance (m + 1) (f y) ≤ δ) :
    (push f).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q = 0 := by
  have aux (N : ℕ) (he : N = (m + 1) + (p + q)) :
      (push f).f N ≫ SupportedCap.cut (parameters (m + 1))
        (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr)
        (m + 1) (p + q) N he.symm (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) = 0 := by
    subst N
    exact SelfCutEndpoints.cut_map_zero _ _ {z | distance (m + 1) z ≤ δ}
      (exterior_open _ _) (neighborhood_open _ _) (cover _ hρr) (m + 1) (p + q)
      _ _ (AnnularSelfCut.cocycle_small_zero (m + 1) (by omega) h) f hf
  unfold AnnularCutComparison.cut
  rw [← Category.assoc, aux _ (by omega), zero_comp]

theorem prism_zero_of_distance (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (q : ℕ) {Y : TopCat.{0}} {f g : Y ⟶ parameters (m + 1)}
    (H : TopCat.Homotopy f g) (hH : ∀ z, distance (m + 1) (H.h z) ≤ δ) :
    (H.toSSet.chainComplexMap coeff).hom ((m + p) + q) ((m + p) + q + 1) ≫
      AnnularCutComparison.cut m p h hρr hr T hT q = 0 := by
  rw [← TimeShuffleComparison.rectangle_eq_prism]
  unfold TimeShuffleComparison.rectangle
  rw [Category.assoc, cut_map_zero_of_distance m p h hρr hr T hT q H.h hH, comp_zero]

theorem family_collar_cut_zero {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : ρ < r) (hr : r ≤ 1) (u : C(X, SphereLoop (m + 1))) :
    ∃ a > 0, a < 1 / 2 ∧ ∀ p
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) q,
      (push (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X))
        (AnnularSelfCut.collar a) ≫ AnnularSelfCut.familyMap u)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h hρr hr T hT q = 0 := by
  obtain ⟨a, ha, ha1, hb⟩ := UniformSelfCutCollar.exists_collar u h.1
  refine ⟨a, ha, ha1, ?_⟩
  intro p T hT q
  apply cut_map_zero_of_distance m p h hρr hr T hT q
  intro z
  exact hb z.val.1 z.val.2 z.property

end
end Finsler.AnnularCollarCut
