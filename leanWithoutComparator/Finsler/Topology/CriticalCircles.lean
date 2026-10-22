module

public import Finsler.Topology.OrientedCritical

/-! The critical circles of a level. For a prime closed geodesic image s and a level c, the
positive critical circle consists of the rotations of the iterate of level c of the chosen closed
geodesic with image s (it is empty if no iterate has level c), and the negative critical circle
of its reversals. The positive critical loops of the level are the union of the positive circles
of the prime images, and likewise the negative ones. The circles are compact, and the circles
of distinct labels (a prime image with an orientation) are disjoint. Finitely many pairwise
disjoint compact sets of a Hausdorff space have pairwise disjoint open neighbourhoods; so with
finitely many prime closed geodesic images the critical circles of a level have pairwise
disjoint open neighbourhoods. -/

@[expose] public section

namespace Finsler.CriticalCircles

open Set Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.SmoothSobolev
open Finsler.SobolevCurveVariation Finsler.SobolevCircleRepresentative Finsler.SobolevReverse
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.SobolevShiftEnergy
open Finsler.CriticalLevels Finsler.EnergyConservation Finsler.BorelLoop Finsler.BorelLocal
open Finsler.OrientedCritical

noncomputable section

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

/-- Finitely many pairwise disjoint compact sets of a Hausdorff space have pairwise disjoint
open neighbourhoods. -/
theorem exists_disjoint_nhds {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*}
    (s : Finset ι) (K : ι → Set X) (hK : ∀ i ∈ s, IsCompact (K i))
    (hdis : (s : Set ι).PairwiseDisjoint K) :
    ∃ U : ι → Set X, (∀ i ∈ s, IsOpen (U i) ∧ K i ⊆ U i) ∧ (s : Set ι).PairwiseDisjoint U := by
  classical
  have hsep : ∀ i j : ι, ∃ V : Set X × Set X, i ∈ s → j ∈ s → i ≠ j →
      IsOpen V.1 ∧ IsOpen V.2 ∧ K i ⊆ V.1 ∧ K j ⊆ V.2 ∧ Disjoint V.1 V.2 := by
    intro i j
    by_cases h : i ∈ s ∧ j ∈ s ∧ i ≠ j
    · obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
        SeparatedNhds.of_isCompact_isCompact (hK i h.1) (hK j h.2.1) (hdis h.1 h.2.1 h.2.2)
      exact ⟨(U, V), fun _ _ _ => ⟨hU, hV, hKU, hKV, hUV⟩⟩
    · exact ⟨(∅, ∅), fun hi hj hne => absurd ⟨hi, hj, hne⟩ h⟩
  choose V hV using hsep
  refine ⟨fun i => ⋂ j ∈ s.erase i, (V i j).1 ∩ (V j i).2, ?_, ?_⟩
  · intro i hi
    constructor
    · refine isOpen_biInter_finset fun j hj => ?_
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      exact (hV i j hi hjs hne.symm).1.inter (hV j i hjs hi hne).2.1
    · refine subset_iInter₂ fun j hj => ?_
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      exact subset_inter (hV i j hi hjs hne.symm).2.2.1 (hV j i hjs hi hne).2.2.2.1
  · intro i hi j hj hne
    have hi' : i ∈ s := hi
    have hj' : j ∈ s := hj
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have h1 : x ∈ (V i j).1 :=
      (mem_iInter₂.mp hxi j (Finset.mem_erase.mpr ⟨hne.symm, hj'⟩)).1
    have h2 : x ∈ (V i j).2 :=
      (mem_iInter₂.mp hxj i (Finset.mem_erase.mpr ⟨hne, hi'⟩)).2
    exact Set.disjoint_left.mp (hV i j hi' hj' hne).2.2.2.2 h1 h2

variable {n : ℕ}

/-- The positive critical circle of level c with prime image s: the rotations of the iterate of
level c of the chosen closed geodesic with image s. -/
def posCircle (F : ReversibleMetric n) (c : ℝ) (s : Set (Sphere n)) : Set (SphereLoop n) :=
  {γ | ∃ (hs : s ∈ primeImages F) (k : ℕ) (θ : Circ), 0 < k ∧
    (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c ∧
    γ = θ +ᵥ ofSmooth (iterate (chosen F s hs).loop k)}

/-- The negative critical circle: the reversals of the positive one. -/
def negCircle (F : ReversibleMetric n) (c : ℝ) (s : Set (Sphere n)) : Set (SphereLoop n) :=
  reverseSphere '' posCircle F c s

variable (F : ReversibleMetric n) (c : ℝ)

theorem posCircle_subset (s : Set (Sphere n)) : posCircle F c s ⊆ posCrit F c := by
  rintro γ ⟨hs, k, θ, hk, hck, h⟩
  exact ⟨s, hs, k, θ, hk, hck, h⟩

theorem negCircle_subset (s : Set (Sphere n)) : negCircle F c s ⊆ negCrit F c :=
  image_mono (posCircle_subset F c s)

/-- The positive critical loops of a level are the union of the positive critical circles. -/
theorem posCrit_eq : posCrit F c = ⋃ s ∈ primeImages F, posCircle F c s := by
  ext γ
  constructor
  · rintro ⟨s, hs, k, θ, hk, hck, rfl⟩
    exact mem_iUnion₂.mpr ⟨s, hs, hs, k, θ, hk, hck, rfl⟩
  · intro hγ
    obtain ⟨s, -, h⟩ := mem_iUnion₂.mp hγ
    exact posCircle_subset F c s h

theorem negCrit_eq : negCrit F c = ⋃ s ∈ primeImages F, negCircle F c s := by
  rw [negCrit, posCrit_eq, image_iUnion₂]
  rfl

theorem isCompact_posCircle (s : Set (Sphere n)) : IsCompact (posCircle F c s) :=
  isCompact_posCrit_image F c s

theorem isCompact_negCircle (s : Set (Sphere n)) : IsCompact (negCircle F c s) :=
  (isCompact_posCircle F c s).image (reverseSphere_continuous n)

/-- Positive critical circles of distinct prime images are disjoint. -/
theorem posCircle_disjoint {s s' : Set (Sphere n)} (hne : s ≠ s') :
    Disjoint (posCircle F c s) (posCircle F c s') := by
  refine Set.disjoint_left.mpr ?_
  rintro γ ⟨hs, k, θ, hk, -, rfl⟩ ⟨hs', k', θ', hk', -, heq⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨a', rfl⟩ := QuotientAddGroup.mk_surjective θ'
  have h1 : ofSmooth (shift (iterate (chosen F s hs).loop k) a) =
      ofSmooth (shift (iterate (chosen F s' hs').loop k') a') := by
    rw [ofSmooth_shift, ofSmooth_shift]
    exact heq
  have e := congrArg Finsler.Loops.image (ofSmooth_injective h1)
  rw [image_shift, image_iterate _ (Nat.ne_of_gt hk), image_shift,
    image_iterate _ (Nat.ne_of_gt hk'), chosen_image, chosen_image] at e
  exact hne e

theorem negCircle_disjoint {s s' : Set (Sphere n)} (hne : s ≠ s') :
    Disjoint (negCircle F c s) (negCircle F c s') := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨γ, hγ, rfl⟩ ⟨γ', hγ', heq⟩
  have h : γ' = γ := by
    rw [← reverseSphere_involutive γ', heq, reverseSphere_involutive]
  exact Set.disjoint_left.mp (posCircle_disjoint F c hne) hγ (h ▸ hγ')

/-- A positive critical circle is disjoint from every negative critical circle. -/
theorem posCircle_negCircle_disjoint (s s' : Set (Sphere n)) :
    Disjoint (posCircle F c s) (negCircle F c s') :=
  Set.disjoint_left.mpr fun γ hp hm =>
    posCrit_inter_negCrit F c γ (posCircle_subset F c s hp) (negCircle_subset F c s' hm)

/-- The oriented critical circle of a label: a prime image with an orientation. -/
def circle (ℓ : Set (Sphere n) × Bool) : Set (SphereLoop n) :=
  cond ℓ.2 (posCircle F c ℓ.1) (negCircle F c ℓ.1)

theorem isCompact_circle (ℓ : Set (Sphere n) × Bool) : IsCompact (circle F c ℓ) := by
  obtain ⟨s, o⟩ := ℓ
  cases o
  · exact isCompact_negCircle F c s
  · exact isCompact_posCircle F c s

/-- The labels of a metric with finitely many prime closed geodesic images. -/
def labels (hfin : (primeImages F).Finite) : Finset (Set (Sphere n) × Bool) :=
  hfin.toFinset ×ˢ Finset.univ

theorem mem_labels (hfin : (primeImages F).Finite) (ℓ : Set (Sphere n) × Bool) :
    ℓ ∈ labels F hfin ↔ ℓ.1 ∈ primeImages F := by
  rw [labels, Finset.mem_product, Set.Finite.mem_toFinset]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ _⟩⟩

/-- The critical circles of distinct labels are disjoint. -/
theorem circle_disjoint {ℓ ℓ' : Set (Sphere n) × Bool} (hne : ℓ ≠ ℓ') :
    Disjoint (circle F c ℓ) (circle F c ℓ') := by
  obtain ⟨s, o⟩ := ℓ
  obtain ⟨s', o'⟩ := ℓ'
  cases o <;> cases o'
  · exact negCircle_disjoint F c fun h => hne (congrArg (fun x => (x, false)) h)
  · exact (posCircle_negCircle_disjoint F c s' s).symm
  · exact posCircle_negCircle_disjoint F c s s'
  · exact posCircle_disjoint F c fun h => hne (congrArg (fun x => (x, true)) h)

/-- The critical loops of a level are the union of the critical circles of the labels. -/
theorem crit_eq (hfin : (primeImages F).Finite) :
    posCrit F c ∪ negCrit F c = ⋃ ℓ ∈ labels F hfin, circle F c ℓ := by
  ext γ
  constructor
  · rintro (h | h)
    · rw [posCrit_eq] at h
      obtain ⟨s, hs, hγ⟩ := mem_iUnion₂.mp h
      exact mem_iUnion₂.mpr ⟨(s, true), (mem_labels F hfin _).mpr hs, hγ⟩
    · rw [negCrit_eq] at h
      obtain ⟨s, hs, hγ⟩ := mem_iUnion₂.mp h
      exact mem_iUnion₂.mpr ⟨(s, false), (mem_labels F hfin _).mpr hs, hγ⟩
  · intro h
    obtain ⟨⟨s, o⟩, -, hγ⟩ := mem_iUnion₂.mp h
    cases o
    · exact Or.inr (negCircle_subset F c s hγ)
    · exact Or.inl (posCircle_subset F c s hγ)

/-- With finitely many prime closed geodesic images the critical circles of a level have
pairwise disjoint open neighbourhoods. -/
theorem exists_circle_nhds (hfin : (primeImages F).Finite) :
    ∃ U : Set (Sphere n) × Bool → Set (SphereLoop n),
      (∀ ℓ ∈ labels F hfin, IsOpen (U ℓ) ∧ circle F c ℓ ⊆ U ℓ) ∧
        ((labels F hfin : Finset (Set (Sphere n) × Bool)) :
          Set (Set (Sphere n) × Bool)).PairwiseDisjoint U :=
  exists_disjoint_nhds (labels F hfin) (circle F c) (fun ℓ _ => isCompact_circle F c ℓ)
    (fun _ _ _ _ hne => circle_disjoint F c hne)

end

end Finsler.CriticalCircles
