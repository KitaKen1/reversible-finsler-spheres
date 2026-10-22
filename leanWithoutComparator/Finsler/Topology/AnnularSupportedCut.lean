module

public import Finsler.Topology.AnnularSelfCut
public import Finsler.Topology.SelfCutEndpoints

/-! Actual neighborhood-valued annular Thom capping, followed by the
specified tested cochain and retained-loop map. -/

@[expose] public section
namespace Finsler.AnnularSupportedCut

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem cocycle_supported (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) n
      (AnnularSelfCut.cocycle n hn h) = 0 := by
  rw [AnnularSelfCut.cocycle, ← pullback_comp]
  apply AnnularThomCocycle.pullback_zero_of_range n hn h
  intro z
  refine mem_iUnion.mpr ⟨false, ?_⟩
  change ρ ≤ distance n z.val
  exact z.property.le

theorem time_zero (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (atTime n 0) n (AnnularSelfCut.cocycle n hn h) = 0 := by
  rw [AnnularSelfCut.cocycle, ← pullback_comp, time_factor]
  apply AnnularThomCocycle.pullback_zero_of_range n hn h
  intro u
  refine mem_iUnion.mpr ⟨true, ?_⟩
  change ‖(sphereRepresentative u 0 : Ambient n) - (sphereRepresentative u 0 : Ambient n)‖ ≤ δ
  simpa only [sub_self, norm_zero] using h.1.le

theorem time_one (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (atTime n 1) n (AnnularSelfCut.cocycle n hn h) = 0 := by
  rw [AnnularSelfCut.cocycle, ← pullback_comp, time_factor]
  apply AnnularThomCocycle.pullback_zero_of_range n hn h
  intro u
  refine mem_iUnion.mpr ⟨true, ?_⟩
  change ‖(sphereRepresentative u 1 : Ambient n) - sphereRepresentative u 0‖ ≤ δ
  have hz : ‖(sphereRepresentative u 1 : Ambient n) - sphereRepresentative u 0‖ = 0 :=
    (congrArg (fun z : Sphere n => ‖(z : Ambient n) - sphereRepresentative u 0‖)
      (sphereRepresentative_endpoints u)).trans
        ((congrArg (fun v : Ambient n => ‖v‖)
          (sub_self (sphereRepresentative u 0 : Ambient n))).trans norm_zero)
  exact hz.le.trans h.1.le

def operation (n : ℕ) (hn : 1 ≤ n) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) :=
  SupportedCapHomology.operation (parameters n) (exterior n ρ) (neighborhood n r)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hρr) n
    (AnnularSelfCut.cocycle n hn h) (cocycle_supported n hn h)
    (AnnularSelfCut.cocycle_closed n hn h)

def chainCut (n p : ℕ) (hn : 1 ≤ n) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    (chains (parameters n)).X (n + (p + q)) ⟶ (chains (TopCat.of (SphereLoop n))).X q :=
  (operation n hn h hρr).component (p + q) ≫
    (NormalizedSelfCut.testedOperation n p hr T hT).component q

theorem chainCut_boundary (n p : ℕ) (hn : 1 ≤ n) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    chainCut n p hn h hρr hr T hT (q + 1) ≫
        (chains (TopCat.of (SphereLoop n))).d (q + 1) q =
      (chains (parameters n)).d (n + (p + (q + 1))) (n + (p + q)) ≫
        chainCut n p hn h hρr hr T hT q := by
  have hu : (operation n hn h hρr).component (p + (q + 1)) ≫
      (chains (TopCat.of (neighborhood n r))).d (p + (q + 1)) (p + q) =
    (chains (parameters n)).d (n + (p + (q + 1))) (n + (p + q)) ≫
      (operation n hn h hρr).component (p + q) :=
    (operation n hn h hρr).comm (p + q)
  unfold chainCut
  rw [Category.assoc, (NormalizedSelfCut.testedOperation n p hr T hT).comm,
    ← Category.assoc, hu, Category.assoc]

theorem chainCut_atTime_zero (n p q : ℕ) (hn : 1 ≤ n) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (t : ClosedInterval)
    (ht : cochainPullback (atTime n t) n (AnnularSelfCut.cocycle n hn h) = 0) :
    (push (atTime n t)).f (n + (p + q)) ≫ chainCut n p hn h hρr hr T hT q = 0 := by
  have hs : cochainPullback (SupportedCap.subspaceMap (parameters n)
      (SelfCutEndpoints.timeSlice n t)) n (AnnularSelfCut.cocycle n hn h) = 0 := by
    rw [SelfCutEndpoints.slice_factor, pullback_comp, ht]
    simp only [cochainPullback, map_zero]
  have hz := SelfCutEndpoints.cut_map_zero (exterior n ρ) (neighborhood n r)
    (SelfCutEndpoints.timeSlice n t) (exterior_open n ρ) (neighborhood_open n r)
    (cover n hρr) n (p + q) (AnnularSelfCut.cocycle n hn h)
    (cocycle_supported n hn h) hs (atTime n t) (fun _ => rfl)
  change (push (atTime n t)).f (n + (p + q)) ≫
    (SupportedCap.cut (parameters n) (exterior n ρ) (neighborhood n r)
      (exterior_open n ρ) (neighborhood_open n r) (cover n hρr) n (p + q)
      (n + (p + q)) rfl (AnnularSelfCut.cocycle n hn h) (cocycle_supported n hn h) ≫
      (NormalizedSelfCut.testedOperation n p hr T hT).component q) = 0
  rw [← Category.assoc, hz, zero_comp]

theorem chainCut_time_zero (n p q : ℕ) (hn : 1 ≤ n) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    (push (atTime n 0)).f (n + (p + q)) ≫ chainCut n p hn h hρr hr T hT q = 0 :=
  chainCut_atTime_zero n p q hn h hρr hr T hT 0 (time_zero n hn h)

theorem chainCut_time_one (n p q : ℕ) (hn : 1 ≤ n) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    (push (atTime n 1)).f (n + (p + q)) ≫ chainCut n p hn h hρr hr T hT q = 0 :=
  chainCut_atTime_zero n p q hn h hρr hr T hT 1 (time_one n hn h)

end
end Finsler.AnnularSupportedCut
