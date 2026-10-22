module

public import Finsler.Topology.TimeCylinderComparison
public import Finsler.Topology.TimePrismNaturality
public import Finsler.Topology.InteriorTimeSlide

/-! Actual time-chain trimming on a compact continuous H1 loop family.
The explicit double prism compares full time with a closed interior interval,
and both side prisms vanish under the actual supported tested cut. -/

@[expose] public section
namespace Finsler.AnnularTimeTrim

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def slice (X : TopCat.{0}) (t : ClosedInterval) : X ⟶ TopCat.of (ClosedInterval × X) :=
  TopCat.ofHom ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩

def cylinder (X : TopCat.{0}) : TopCat.Homotopy (slice X 0) (slice X 1) where
  toFun z := (⟨z.1.val, z.1.property⟩, z.2)
  continuous_toFun := continuous_fst.prodMk continuous_snd
  map_zero_left _ := rfl
  map_one_left _ := rfl

def prism (X : TopCat.{0}) (j : ℕ) : (chains X).X j ⟶
    (chains (TopCat.of (ClosedInterval × X))).X (j + 1) :=
  ((cylinder X).toSSet.chainComplexMap coeff).hom j (j + 1)

def component {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (f : TopCat.of (ClosedInterval × X) ⟶ parameters (m + 1)) (q : ℕ) :
    (chains (TopCat.of X)).X ((m + p) + q) ⟶
      (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  prism (TopCat.of X) ((m + p) + q) ≫ (push f).f ((m + p) + q + 1) ≫
    AnnularCutComparison.cut m p h hρr hr T hT q

def comparison {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (u : C(X, SphereLoop (m + 1))) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (q : ℕ) :
    (chains (TopCat.of X)).X ((m + p) + q) ⟶
      (chains (TopCat.of (SphereLoop (m + 1)))).X (q + 1) :=
  prism (TopCat.of X) ((m + p) + q) ≫
    ((InteriorTimeSlide.homotopy u a ha ha1).toSSet.chainComplexMap coeff).hom
      ((m + p) + q + 1) ((m + p) + q + 2) ≫
        AnnularCutComparison.cut m p h hρr hr T hT (q + 1)

theorem side_zero {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (u : C(X, SphereLoop (m + 1))) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (t : ClosedInterval)
    (ht : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (InteriorTimeSlide.homotopy u a ha ha1 (s, (t, x))) ≤ δ) (q : ℕ) :
    (push (slice (TopCat.of X) t)).f ((m + p) + q) ≫
      (((InteriorTimeSlide.homotopy u a ha ha1).toSSet.chainComplexMap coeff).hom
        ((m + p) + q) ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q) = 0 := by
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  apply AnnularCollarCut.prism_zero_of_distance m p h hρr hr T hT q
  intro z
  exact ht z.2.down z.1

theorem cycle_boundary {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (u : C(X, SphereLoop (m + 1))) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (InteriorTimeSlide.homotopy u a ha ha1 (s, (0, x))) ≤ δ)
    (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (InteriorTimeSlide.homotopy u a ha ha1 (s, (1, x))) ≤ δ) (q : ℕ) :
    (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
      (component m p h hρr hr T hT (AnnularSelfCut.familyMap u) q -
        component m p h hρr hr T hT (InteriorTimeSlide.trimmedMap u a ha ha1) q) =
      ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        comparison m p h hρr hr T hT u a ha ha1 q) ≫
          (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q := by
  have he := TimeCylinderComparison.cycle_boundary
    ((cylinder (TopCat.of X)).toSSet.chainComplexMap coeff)
    ((InteriorTimeSlide.homotopy u a ha ha1).toSSet.chainComplexMap coeff)
    (m + p) (AnnularCutComparison.cut m p h hρr hr T hT)
    (AnnularCutComparison.cut_boundary m p h hρr hr T hT)
    (side_zero m p h hρr hr T hT u a ha ha1 0 h₀)
    (side_zero m p h hρr hr T hT u a ha ha1 1 h₁) q
  simpa only [component, comparison, prism, Category.assoc,
    Preadditive.comp_sub, Preadditive.sub_comp, push, chains] using he

theorem full_component {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (u : C(X, SphereLoop (m + 1))) (q : ℕ) :
    component m p h hρr hr T hT (AnnularSelfCut.familyMap u) q =
      (push (TopCat.ofHom u)).f ((m + p) + q) ≫
        (AnnularCutComparison.operation m p h hρr hr T hT).component q := by
  have hp : prism (TopCat.of X) ((m + p) + q) ≫
      (push (AnnularSelfCut.familyMap u)).f ((m + p) + q + 1) =
      (push (TopCat.ofHom u)).f ((m + p) + q) ≫
        ((SelfCutTimePrism.cylinder (m + 1)).toSSet.chainComplexMap coeff).hom
          ((m + p) + q) ((m + p) + q + 1) := by
    unfold prism
    rw [TimePrismNaturality.prism_post, TimePrismNaturality.prism_pre]
    apply TimePrismNaturality.prism_congr
    ext z : 1
    rfl
  unfold component
  rw [← Category.assoc, hp, Category.assoc]
  rfl

theorem exists_interior_trim {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : ρ < r) (hr : r ≤ 1) (u : C(X, SphereLoop (m + 1))) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      (∀ z, a ≤ ((InteriorTimeSlide.trimmedMap u a ha.le ha1.le) z).1 ∧
        (((InteriorTimeSlide.trimmedMap u a ha.le ha1.le) z).1 : ℝ) ≤ 1 - a) ∧
      ∀ p (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) q,
      (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        (component m p h hρr hr T hT (AnnularSelfCut.familyMap u) q -
          component m p h hρr hr T hT (InteriorTimeSlide.trimmedMap u a ha.le ha1.le) q) =
        ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫
          comparison m p h hρr hr T hT u a ha.le ha1.le q) ≫
            (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q := by
  obtain ⟨a, ha, ha1, h₀, h₁⟩ := InteriorTimeSlide.family_slide_sides_small u h.1
  refine ⟨a, ha, ha1, ?_, ?_⟩
  · intro z
    exact InteriorTimeSlide.trimTime_range a ha.le ha1.le z.1
  · intro p T hT q
    exact cycle_boundary m p h hρr hr T hT u a ha.le ha1.le h₀ h₁ q

end
end Finsler.AnnularTimeTrim
