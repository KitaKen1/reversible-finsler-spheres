module

public import Finsler.Topology.AnnularTimeTrim

/-! Descend the actual interior-time cut to homology and identify it with
the existing annular time-cut pulled back to a compact H1 loop family.
The interior interval is chosen before every tested degree and cochain. -/

@[expose] public section
namespace Finsler.AnnularTrimHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

section
variable {X : Type} [TopologicalSpace X] (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (f : TopCat.of (ClosedInterval × X) ⟶ parameters (m + 1))

def along (q : ℕ) : (chains (TopCat.of (ClosedInterval × X))).X ((m + p) + q + 1) ⟶
    (chains (TopCat.of (SphereLoop (m + 1)))).X q :=
  (push f).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr hr T hT q

theorem along_boundary (q : ℕ) :
    along m p h hρr hr T hT f (q + 1) ≫
        (chains (TopCat.of (SphereLoop (m + 1)))).d (q + 1) q =
      (chains (TopCat.of (ClosedInterval × X))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
        along m p h hρr hr T hT f q := by
  have hc : (push f).f ((m + p) + (q + 1) + 1) ≫
      (chains (parameters (m + 1))).d ((m + p) + q + 2) ((m + p) + q + 1) =
    (chains (TopCat.of (ClosedInterval × X))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
      (push f).f ((m + p) + q + 1) := (push f).comm _ _
  unfold along
  rw [Category.assoc, AnnularCutComparison.cut_boundary, ← Category.assoc,
    hc, Category.assoc]

theorem along_endpoint (t : ClosedInterval)
    (ht : ∀ x, distance (m + 1) (f (t, x)) ≤ δ) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of X) t)).f ((m + p) + q + 1) ≫
      along m p h hρr hr T hT f q = 0 := by
  unfold along
  rw [← Category.assoc, ← HomologicalComplex.comp_f, ← push_comp]
  exact AnnularCollarCut.cut_map_zero_of_distance m p h hρr hr T hT q
    (AnnularTimeTrim.slice (TopCat.of X) t ≫ f) ht

def operation
    (h₀ : ∀ x, distance (m + 1) (f (0, x)) ≤ δ)
    (h₁ : ∀ x, distance (m + 1) (f (1, x)) ≤ δ) :
    DegreeLoweringHomology.Map (chains (TopCat.of X))
      (chains (TopCat.of (SphereLoop (m + 1)))) (m + p) :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder (TopCat.of X)).toSSet.chainComplexMap coeff)
    (m + p) (along m p h hρr hr T hT f) (along_boundary m p h hρr hr T hT f)
    (along_endpoint m p h hρr hr T hT f 0 h₀) (along_endpoint m p h hρr hr T hT f 1 h₁)

theorem homology_eq (u : C(X, SphereLoop (m + 1))) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (ht₀ : ∀ x, distance (m + 1) (InteriorTimeSlide.trimmedMap u a ha ha1 (0, x)) ≤ δ)
    (ht₁ : ∀ x, distance (m + 1) (InteriorTimeSlide.trimmedMap u a ha ha1 (1, x)) ≤ δ)
    (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (InteriorTimeSlide.homotopy u a ha ha1 (s, (0, x))) ≤ δ)
    (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
      (InteriorTimeSlide.homotopy u a ha ha1 (s, (1, x))) ≤ δ) (q : ℕ) :
    ((AnnularCutComparison.operation m p h hρr hr T hT).pre (push (TopCat.ofHom u))).homology q =
      (operation m p h hρr hr T hT (InteriorTimeSlide.trimmedMap u a ha ha1) ht₀ ht₁).homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (AnnularTimeTrim.comparison m p h hρr hr T hT u a ha ha1 q)
  change (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
    ((push (TopCat.ofHom u)).f ((m + p) + q) ≫
      (AnnularCutComparison.operation m p h hρr hr T hT).component q -
      AnnularTimeTrim.component m p h hρr hr T hT (InteriorTimeSlide.trimmedMap u a ha ha1) q) = _
  rw [← AnnularTimeTrim.full_component]
  exact AnnularTimeTrim.cycle_boundary m p h hρr hr T hT u a ha ha1 h₀ h₁ q

end

theorem exists_interior_operation {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (u : C(X, SphereLoop (m + 1))) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
      (ht₀ : ∀ x, distance (m + 1) (InteriorTimeSlide.trimmedMap u a ha.le ha1.le (0, x)) ≤ δ)
      (ht₁ : ∀ x, distance (m + 1) (InteriorTimeSlide.trimmedMap u a ha.le ha1.le (1, x)) ≤ δ),
      ∀ p (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) q,
      ((AnnularCutComparison.operation m p h hρr hr T hT).pre (push (TopCat.ofHom u))).homology q =
        (operation m p h hρr hr T hT (InteriorTimeSlide.trimmedMap u a ha.le ha1.le) ht₀ ht₁).homology q := by
  obtain ⟨a, ha, ha1, h₀, h₁⟩ := InteriorTimeSlide.family_slide_sides_small u h.1
  have ht₀ : ∀ x, distance (m + 1) (InteriorTimeSlide.trimmedMap u a ha.le ha1.le (0, x)) ≤ δ := by
    intro x
    have he := h₀ 1 x
    change distance (m + 1) (InteriorTimeSlide.slide a ha.le ha1.le (1, 0), u x) ≤ δ at he
    rw [InteriorTimeSlide.slide_one] at he
    exact he
  have ht₁ : ∀ x, distance (m + 1) (InteriorTimeSlide.trimmedMap u a ha.le ha1.le (1, x)) ≤ δ := by
    intro x
    have he := h₁ 1 x
    change distance (m + 1) (InteriorTimeSlide.slide a ha.le ha1.le (1, 1), u x) ≤ δ at he
    rw [InteriorTimeSlide.slide_one] at he
    exact he
  refine ⟨a, ha, ha1, ht₀, ht₁, ?_⟩
  intro p T hT q
  exact homology_eq m p h hρr hr T hT u a ha.le ha1.le ht₀ ht₁ h₀ h₁ q

end
end Finsler.AnnularTrimHomology
