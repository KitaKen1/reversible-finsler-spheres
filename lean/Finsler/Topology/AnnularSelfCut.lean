module

public import Finsler.Topology.AnnularThomComparison
public import Finsler.Topology.UniformSelfCutCollar
public import Finsler.Topology.NormalizedSelfCut

/-! The annular Thom cochain on actual H1 self-evaluation, its positive
endpoint collars on compact loop families, and the comparison primitive
to the existing normalized self-cut. Both primitive time endpoints vanish
literally. Equality of the full supported D_T operators remains separate. -/

@[expose] public section
namespace Finsler.AnnularSelfCut

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def cocycle (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (parameters n) n :=
  cochainPullback (selfEvaluation n) n (AnnularThomCocycle.ambient n hn h)

theorem cocycle_closed (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainCoboundary (ZMod 2) (parameters n) n (cocycle n hn h) = 0 :=
  pullback_closed (selfEvaluation n) n _ (AnnularThomCocycle.ambient_closed n hn h)

theorem cocycle_small_zero (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (parameters n) {z | distance n z ≤ δ}) n (cocycle n hn h) = 0 := by
  rw [cocycle, ← pullback_comp]
  apply AnnularThomCocycle.pullback_zero_of_range n hn h
  intro z
  exact mem_iUnion.mpr ⟨true, z.property⟩

def primitive (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    singularCochainGroup (ZMod 2) (parameters n) (n - 1) :=
  cochainPullback (selfEvaluation n) (n - 1) (AnnularThomComparison.ambientPrimitive n hn h hρ2)

theorem primitive_boundary (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    ((cochainCxZMod2 (parameters n)).d (n - 1) n).hom (primitive n hn h hρ2) =
      cocycle n (by omega) h - NormalizedSelfCut.cocycle n (by omega) (h.1.trans h.2.2) := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (selfEvaluation n).op).comm (n - 1) n)
    (AnnularThomComparison.ambientPrimitive n hn h hρ2)
  change ((cochainCxZMod2 (parameters n)).d (n - 1) n).hom (primitive n hn h hρ2) =
    ((singularCochainComplexZMod2.map (selfEvaluation n).op).f n).hom
      (((cochainCxZMod2 (DiagonalCohomology.product n)).d (n - 1) n).hom
        (AnnularThomComparison.ambientPrimitive n hn h hρ2)) at he
  rw [he, AnnularThomComparison.ambientPrimitive_boundary, map_sub]
  rfl

private theorem primitive_pullback_avoid (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2)
    {X : TopCat.{0}} (f : X ⟶ DiagonalCohomology.product n)
    (hf : ∀ x, f x ∈ DiagonalAvoidanceCocycle.avoid n ρ) :
    cochainPullback f (n - 1) (AnnularThomComparison.ambientPrimitive n hn h hρ2) = 0 := by
  let g : X ⟶ TopCat.of (DiagonalAvoidanceCocycle.avoid n ρ) :=
    TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ DiagonalAvoidanceCocycle.inclusion n ρ := by ext x : 1; rfl
  rw [he, pullback_comp, AnnularThomComparison.ambientPrimitive_supported]
  simp only [cochainPullback, map_zero]

theorem primitive_time_zero (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (atTime n 0) (n - 1) (primitive n hn h hρ2) = 0 := by
  rw [primitive, ← pullback_comp, time_factor]
  apply primitive_pullback_avoid n hn h hρ2
  intro u
  exact mem_iUnion.mpr ⟨true, rfl⟩

theorem primitive_time_one (n : ℕ) (hn : 2 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρ2 : ρ ≤ 2) :
    cochainPullback (atTime n 1) (n - 1) (primitive n hn h hρ2) = 0 := by
  rw [primitive, ← pullback_comp, time_factor]
  apply primitive_pullback_avoid n hn h hρ2
  intro u
  exact mem_iUnion.mpr ⟨true, (sphereRepresentative_endpoints u).symm⟩

def familyMap {X : Type} [TopologicalSpace X] {n : ℕ} (u : C(X, SphereLoop n)) :
    TopCat.of (ClosedInterval × X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, u z.2), continuous_fst.prodMk (u.continuous.comp continuous_snd)⟩

def collar {X : Type} (a : ℝ) : Set (ClosedInterval × X) :=
  {z | (z.1 : ℝ) < a ∨ 1 - a < (z.1 : ℝ)}

def familyCocycle {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 1 ≤ n)
    {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (u : C(X, SphereLoop n)) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) n :=
  cochainPullback (familyMap u) n (cocycle n hn h)

theorem family_collar_zero {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (u : C(X, SphereLoop n)) :
    ∃ a > 0, a < 1 / 2 ∧
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (collar a)) n
        (familyCocycle n hn h u) = 0 := by
  obtain ⟨a, ha, ha1, hb⟩ := UniformSelfCutCollar.exists_collar u h.1
  refine ⟨a, ha, ha1, ?_⟩
  apply pullback_support (familyMap u) (collar a) {z | distance n z ≤ δ} ?_ n
    (cocycle n hn h) (cocycle_small_zero n hn h)
  intro z hz
  exact hb z.1 z.2 hz

end
end Finsler.AnnularSelfCut
