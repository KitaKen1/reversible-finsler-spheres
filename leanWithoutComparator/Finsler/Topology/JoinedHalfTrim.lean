module

public import Finsler.Topology.CylinderTimeTrim
public import Finsler.Topology.JoinedHalfOperations

/-! A single positive interior interval is chosen before every tested
cochain and degree for both genuine halves of a joined H1 loop family.
Its trimmed operations still sum to the existing full annular operation. -/

@[expose] public section
namespace Finsler.JoinedHalfTrim

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}

theorem family_slide_sides_small (u : C(X, H1JoinContinuity.composable n))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      (∀ (s : ClosedInterval) (x : X), distance n
        (CylinderTimeTrim.homotopy (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (s, (0, x))) ≤ δ) ∧
      (∀ (s : ClosedInterval) (x : X), distance n
        (CylinderTimeTrim.homotopy (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (s, (1, x))) ≤ δ) ∧
      (∀ (s : ClosedInterval) (x : X), distance n
        (CylinderTimeTrim.homotopy (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (s, (0, x))) ≤ δ) ∧
      (∀ (s : ClosedInterval) (x : X), distance n
        (CylinderTimeTrim.homotopy (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (s, (1, x))) ≤ δ) := by
  obtain ⟨b, hb, hb1, hbound⟩ := JoinedHalfCollars.exists_collar u hδ
  let a := b / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 / 2 := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  refine ⟨a, ha, ha1, ?_, ?_, ?_, ?_⟩
  · intro s x
    exact (hbound (InteriorTimeSlide.slide a ha.le ha1.le (s, 0)) x
      (Or.inl (InteriorTimeSlide.slide_ends_in_collar a b ha.le ha1.le hab s).1)).1
  · intro s x
    exact (hbound (InteriorTimeSlide.slide a ha.le ha1.le (s, 1)) x
      (Or.inr (InteriorTimeSlide.slide_ends_in_collar a b ha.le ha1.le hab s).2)).1
  · intro s x
    exact (hbound (InteriorTimeSlide.slide a ha.le ha1.le (s, 0)) x
      (Or.inl (InteriorTimeSlide.slide_ends_in_collar a b ha.le ha1.le hab s).1)).2
  · intro s x
    exact (hbound (InteriorTimeSlide.slide a ha.le ha1.le (s, 1)) x
      (Or.inr (InteriorTimeSlide.slide_ends_in_collar a b ha.le ha1.le hab s).2)).2

private theorem trimmed_endpoint_small
    (f : TopCat.of (ClosedInterval × X) ⟶ parameters n)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (t : ClosedInterval) {δ : ℝ}
    (ht : ∀ (s : ClosedInterval) (x : X), distance n
      (CylinderTimeTrim.homotopy f a ha ha1 (s, (t, x))) ≤ δ) :
    ∀ x, distance n (CylinderTimeTrim.trimmedMap f a ha ha1 (t, x)) ≤ δ := by
  intro x
  have he := ht 1 x
  change distance n (f (InteriorTimeSlide.slide a ha ha1 (1, t), x)) ≤ δ at he
  rw [InteriorTimeSlide.slide_one] at he
  exact he

theorem exists_interior_operations (m : ℕ) {δ ρ r : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (u : C(X, H1JoinContinuity.composable (m + 1))) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
      (hf₀ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (0, x)) ≤ δ)
      (hf₁ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (1, x)) ≤ δ)
      (hs₀ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (0, x)) ≤ δ)
      (hs₁ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (1, x)) ≤ δ),
      ∀ p (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) q,
      ((AnnularCutComparison.operation m p h hρr hr T hT).pre
        (push (TopCat.ofHom (JoinedTimeSplit.loopFamily u)))).homology q =
        (AnnularTrimHomology.operation m p h hρr hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) hf₀ hf₁).homology q +
        (AnnularTrimHomology.operation m p h hρr hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le) hs₀ hs₁).homology q := by
  obtain ⟨a, ha, ha1, hf0, hf1, hs0, hs1⟩ := family_slide_sides_small u h.1
  have hf₀ := trimmed_endpoint_small (JoinedHalfCollars.firstFamily u) a ha.le ha1.le 0 hf0
  have hf₁ := trimmed_endpoint_small (JoinedHalfCollars.firstFamily u) a ha.le ha1.le 1 hf1
  have hs₀ := trimmed_endpoint_small (JoinedHalfCollars.secondFamily u) a ha.le ha1.le 0 hs0
  have hs₁ := trimmed_endpoint_small (JoinedHalfCollars.secondFamily u) a ha.le ha1.le 1 hs1
  refine ⟨a, ha, ha1, hf₀, hf₁, hs₀, hs₁, ?_⟩
  intro p T hT q
  have heF := CylinderTimeTrim.homology_eq m p h hρr hr T hT (JoinedHalfCollars.firstFamily u)
    a ha.le ha1.le
    (fun x => (JoinedHalfOperations.first_endpoint u 0 (Or.inl rfl) x).trans_le h.1.le)
    (fun x => (JoinedHalfOperations.first_endpoint u 1 (Or.inr rfl) x).trans_le h.1.le)
    hf₀ hf₁ hf0 hf1 q
  have heS := CylinderTimeTrim.homology_eq m p h hρr hr T hT (JoinedHalfCollars.secondFamily u)
    a ha.le ha1.le
    (fun x => (JoinedHalfOperations.second_endpoint u 0 (Or.inl rfl) x).trans_le h.1.le)
    (fun x => (JoinedHalfOperations.second_endpoint u 1 (Or.inr rfl) x).trans_le h.1.le)
    hs₀ hs₁ hs0 hs1 q
  rw [JoinedHalfOperations.homology_split]
  exact congrArg₂ (fun f g => f + g) heF heS

end
end Finsler.JoinedHalfTrim
