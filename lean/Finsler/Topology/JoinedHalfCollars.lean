module

public import Finsler.Topology.HalfConcatRestriction
public import Finsler.Topology.AnnularCollarCut

/-! The actual two half-time evaluation cylinders of a joined H1 loop.
Compact matching input families have one annular-zero collar at all four
half-cylinder ends, including the joined midpoint seam, before every
tested degree and cochain. The time-chain split identity is separate. -/

@[expose] public section
namespace Finsler.JoinedHalfCollars

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SobolevConcat
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {n : ℕ}

def pairJoin (z : composable n) : SphereLoop n :=
  join (1 / 2) (by norm_num) (by norm_num) z.val.1 z.val.2 z.property

theorem continuous_pairJoin : Continuous (pairJoin (n := n)) :=
  continuous_join (1 / 2) (by norm_num) (by norm_num)

def secondTime (t : ClosedInterval) : ClosedInterval :=
  ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

theorem second_evaluate (u v : Space n) (t : ClosedInterval)
    (hm : continuousRepresentative u 1 = continuousRepresentative v 0) :
    continuousRepresentative (concat u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)) (secondTime t) =
      continuousRepresentative v t := by
  have ht : (secondTime t : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    change 1 / 2 ≤ (1 + (t : ℝ)) / 2 ∧ (1 + (t : ℝ)) / 2 ≤ 1
    constructor <;> linarith [t.property.1, t.property.2]
  rw [representative_concat_right u v (by norm_num) (by norm_num) hm ht]
  congr 1
  norm_num [rightMap, secondTime]
  <;> ring

def first (z : ClosedInterval × composable n) : parameters n :=
  (HalfConcatRestriction.half z.1, pairJoin z.2)

def second (z : ClosedInterval × composable n) : parameters n :=
  (secondTime z.1, pairJoin z.2)

theorem continuous_first : Continuous (first (n := n)) := by
  have ht : Continuous (fun z : ClosedInterval × composable n => HalfConcatRestriction.half z.1) :=
    ((continuous_subtype_val.comp continuous_fst).div_const 2).subtype_mk _
  exact ht.prodMk (continuous_pairJoin.comp continuous_snd)

theorem continuous_second : Continuous (second (n := n)) := by
  have ht : Continuous (fun z : ClosedInterval × composable n => secondTime z.1) :=
    ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).div_const 2).subtype_mk _
  exact ht.prodMk (continuous_pairJoin.comp continuous_snd)

theorem first_distance (z : ClosedInterval × composable n) :
    distance n (first z) = distance n (z.1, z.2.val.1) := by
  have he : continuousRepresentative ((pairJoin z.2).data : Space n) (HalfConcatRestriction.half z.1) =
      continuousRepresentative (z.2.val.1.data : Space n) z.1 :=
    HalfConcatRestriction.evaluate _ _ z.1
  have hp : basepoint (pairJoin z.2) = basepoint z.2.val.1 :=
    basepoint_join (1 / 2) (by norm_num) (by norm_num) _ _ z.2.property
  change ‖continuousRepresentative ((pairJoin z.2).data : Space n) (HalfConcatRestriction.half z.1) -
    basepoint (pairJoin z.2)‖ = ‖continuousRepresentative (z.2.val.1.data : Space n) z.1 - basepoint z.2.val.1‖
  rw [he, hp]

theorem second_distance (z : ClosedInterval × composable n) :
    distance n (second z) = distance n (z.1, z.2.val.2) := by
  have he : continuousRepresentative ((pairJoin z.2).data : Space n) (secondTime z.1) =
      continuousRepresentative (z.2.val.2.data : Space n) z.1 :=
    second_evaluate _ _ z.1 (end_match _ _ z.2.property)
  have hp : basepoint (pairJoin z.2) = basepoint z.2.val.2 :=
    (basepoint_join (1 / 2) (by norm_num) (by norm_num) _ _ z.2.property).trans z.2.property
  change ‖continuousRepresentative ((pairJoin z.2).data : Space n) (secondTime z.1) -
    basepoint (pairJoin z.2)‖ = ‖continuousRepresentative (z.2.val.2.data : Space n) z.1 - basepoint z.2.val.2‖
  rw [he, hp]

def leftLoop {X : Type} [TopologicalSpace X] (u : C(X, composable n)) : C(X, SphereLoop n) :=
  ⟨fun x => (u x).val.1, continuous_fst.comp (continuous_subtype_val.comp u.continuous)⟩

def rightLoop {X : Type} [TopologicalSpace X] (u : C(X, composable n)) : C(X, SphereLoop n) :=
  ⟨fun x => (u x).val.2, continuous_snd.comp (continuous_subtype_val.comp u.continuous)⟩

def firstFamily {X : Type} [TopologicalSpace X] (u : C(X, composable n)) :
    TopCat.of (ClosedInterval × X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => first (z.1, u z.2),
    continuous_first.comp (continuous_fst.prodMk (u.continuous.comp continuous_snd))⟩

def secondFamily {X : Type} [TopologicalSpace X] (u : C(X, composable n)) :
    TopCat.of (ClosedInterval × X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => second (z.1, u z.2),
    continuous_second.comp (continuous_fst.prodMk (u.continuous.comp continuous_snd))⟩

theorem exists_collar {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (u : C(X, composable n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a > 0, a < 1 / 2 ∧ ∀ (t : ClosedInterval) (x : X),
      ((t : ℝ) < a ∨ 1 - a < (t : ℝ)) →
      distance n (firstFamily u (t, x)) ≤ δ ∧ distance n (secondFamily u (t, x)) ≤ δ := by
  obtain ⟨a₁, ha₁, ha₁1, hb₁⟩ := UniformSelfCutCollar.exists_collar (leftLoop u) hδ
  obtain ⟨a₂, ha₂, ha₂1, hb₂⟩ := UniformSelfCutCollar.exists_collar (rightLoop u) hδ
  let a := min a₁ a₂
  have ha : 0 < a := lt_min ha₁ ha₂
  have h₁ : a ≤ a₁ := min_le_left _ _
  have h₂ : a ≤ a₂ := min_le_right _ _
  refine ⟨a, ha, h₁.trans_lt ha₁1, ?_⟩
  intro t x ht
  have ht₁ : (t : ℝ) < a₁ ∨ 1 - a₁ < (t : ℝ) := by rcases ht with h | h <;> [left; right] <;> linarith
  have ht₂ : (t : ℝ) < a₂ ∨ 1 - a₂ < (t : ℝ) := by rcases ht with h | h <;> [left; right] <;> linarith
  constructor
  · change distance n (first (t, u x)) ≤ δ
    rw [first_distance]
    exact hb₁ t x ht₁
  · change distance n (second (t, u x)) ≤ δ
    rw [second_distance]
    exact hb₂ t x ht₂

theorem collar_cuts_zero {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (u : C(X, composable (m + 1))) :
    ∃ a > 0, a < 1 / 2 ∧ ∀ p
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) q,
      (push (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (AnnularSelfCut.collar a) ≫
        firstFamily u)).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q = 0 ∧
      (push (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (AnnularSelfCut.collar a) ≫
        secondFamily u)).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q = 0 := by
  obtain ⟨a, ha, ha1, hb⟩ := exists_collar u h.1
  refine ⟨a, ha, ha1, ?_⟩
  intro p T hT q
  constructor
  · apply AnnularCollarCut.cut_map_zero_of_distance m p h hρr hr T hT q
    intro z
    exact (hb z.val.1 z.val.2 z.property).1
  · apply AnnularCollarCut.cut_map_zero_of_distance m p h hρr hr T hT q
    intro z
    exact (hb z.val.1 z.val.2 z.property).2

end
end Finsler.JoinedHalfCollars
