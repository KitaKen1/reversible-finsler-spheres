module

public import Finsler.Topology.FixedSampleK
public import Finsler.Topology.OrbitNbhd
public import Finsler.Topology.PolygonOriented

/-! Neighbourhoods of the orbits of critical circles in the polygon models, with halves. For
polygons with 2M vertices the broken geodesic of the polygon rotated by M vertices is the half
rotation of the broken geodesic, and that of the reversed polygon is the reversed loop. So the
polygons near a set of loops invariant under the reversal and the half rotation form a set
invariant under the reversal and the rotation by M, and if the reversal exchanges the loops of
such a set inside and outside a second set, it exchanges the corresponding polygons. With
finitely many prime closed geodesic images there are open neighbourhoods of the positive and of
the negative critical loops of a level which are exchanged by the reversal, kept by the half
rotation and disjoint; intersected with the orbit neighbourhoods (`OrbitNbhd`) they give, for
every prime image, an open set of loops invariant under the reversal and the half rotation with a
half exchanged by the reversal. The polygons near these sets are pairwise disjoint invariant open
sets with halves exchanged by the reversal, and they contain the stationary polygons of a band in
which the level is the only critical level: these are the open sets and halves of the polygon
models of the crossings (`PolyModels`). -/

@[expose] public section

namespace Finsler.PolyOrbits

open Set Topology
open Finsler.Geometry Finsler.SphereGeometry Finsler.SobolevReverse Finsler.BorelLoop
open Finsler.BorelK Finsler.BorelCoverK Finsler.PolygonLoop Finsler.PolygonModel
open Finsler.PolygonDescent Finsler.PolygonDescentK Finsler.PolygonOriented Finsler.SampleK
open Finsler.FixedSampleK Finsler.InvPairs Finsler.OrbitNbhd Finsler.OrientedCritical
open Finsler.CriticalCircles Finsler.AmbientRotation Finsler.PolygonCritical
open Finsler.Geodesics Finsler.IntervalSobolev Finsler.CriticalLevels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {M : ℕ} [NeZero M]
  (P : PolygonModelData F A (2 * M))

/-- The broken geodesic of the polygon rotated by M vertices is the half rotation of the broken
geodesic. -/
theorem broken_rotM (q : {q : ZMod (2 * M) → Sphere n // ShortPolygon P.δ q}) :
    broken P ⟨rotPoly (M : ZMod (2 * M)) q.1, shortPolygon_rotP _ q.2⟩ = half +ᵥ broken P q := by
  have h := broken_rotate_nat P M q
  rw [circle_half] at h
  rw [← h]
  congr 1
  apply Subtype.ext
  have hk : ∀ k (r : {q : ZMod (2 * M) → Sphere n // ShortPolygon P.δ q}),
      ((rotateShort P)^[k] r).1 = rotatePolygon^[k] r.1 := by
    intro k
    induction k with
    | zero => intro r; rfl
    | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  rw [hk, iterate_rotatePolygon]

/-- The polygons near a set of loops invariant under the reversal and the half rotation form a
set invariant under the reversal and the rotation by M. -/
theorem near_inv {W : Set (Loops n)} (hW : KInv W) : Inv (kPoly n M) (near P W) where
  ρ_mem q hq := by
    obtain ⟨hs, hb⟩ := hq
    exact ⟨shortPolygon_reverse hs,
      (congrArg (· ∈ W) (broken_reverse P ⟨q, hs⟩)).mpr (hW.rev_mem _ hb)⟩
  σ_mem q hq := by
    obtain ⟨hs, hb⟩ := hq
    exact ⟨shortPolygon_rotP _ hs,
      (congrArg (· ∈ W) (broken_rotM P ⟨q, hs⟩)).mpr (hW.half_mem _ hb)⟩

/-- If the reversal exchanges the loops of W inside and outside V, it exchanges the polygons
near W inside and outside the polygons near V. -/
theorem near_swap {W V : Set (Loops n)} (hV : ∀ u ∈ W, reverseSphere u ∈ V ↔ u ∉ V) :
    ∀ q ∈ near P W, (kPoly n M).ρ q ∈ near P V ↔ q ∉ near P V := by
  rintro q ⟨hs, hb⟩
  have e := congrArg (· ∈ V) (broken_reverse P ⟨q, hs⟩)
  constructor
  · rintro ⟨_, hb'⟩ ⟨_, hb''⟩
    exact (hV _ hb).mp (e.mp hb') hb''
  · intro hn
    exact ⟨shortPolygon_reverse hs, e.mpr ((hV _ hb).mpr fun h => hn ⟨hs, h⟩)⟩

theorem vadd_mem_posCrit (φ : SobolevCircleRepresentative.Circle) {c : ℝ} {γ : SphereLoop n}
    (hγ : γ ∈ posCrit F c) : φ +ᵥ γ ∈ posCrit F c := by
  obtain ⟨s, hs, k, θ, hk, hck, rfl⟩ := hγ
  exact ⟨s, hs, k, φ + θ, hk, hck, vadd_vadd φ θ _⟩

/-- The part of a set of loops kept by the half rotation. -/
def halfSym (U : Set (Loops n)) : Set (Loops n) := U ∩ (fun u : SphereLoop n => half +ᵥ u) ⁻¹' U

theorem halfSym_isOpen {U : Set (Loops n)} (hU : IsOpen U) : IsOpen (halfSym U) :=
  hU.inter (hU.preimage half_continuous)

theorem mem_halfSym {U : Set (Loops n)} {u : SphereLoop n} :
    u ∈ halfSym U ↔ u ∈ U ∧ half +ᵥ u ∈ U :=
  (Set.mem_inter_iff _ _ _).trans (and_congr Iff.rfl Set.mem_preimage)

theorem half_mem_halfSym {U : Set (Loops n)} (u : SphereLoop n) :
    half +ᵥ u ∈ halfSym U ↔ u ∈ halfSym U := by
  rw [mem_halfSym, mem_halfSym, half_half]
  exact and_comm

theorem posCrit_subset_halfSym {c : ℝ} {U : Set (Loops n)} (h : posCrit F c ⊆ U) :
    posCrit F c ⊆ halfSym U :=
  fun _ hγ => mem_halfSym.mpr ⟨h hγ, h (vadd_mem_posCrit half hγ)⟩

/-- **Halves.** With finitely many prime closed geodesic images, there is an open set of loops
containing the positive critical loops of a level, kept by the half rotation and disjoint from
its image under the reversal (which contains the negative critical loops). -/
theorem exists_half (hfin : (primeImages F).Finite) (c : ℝ) :
    ∃ Up : Set (Loops n), IsOpen Up ∧ posCrit F c ⊆ Up ∧ (∀ u, half +ᵥ u ∈ Up ↔ u ∈ Up) ∧
      Disjoint Up (reverseSphere ⁻¹' Up) := by
  have hdis : Disjoint (posCrit F c) (negCrit F c) :=
    Set.disjoint_left.mpr fun γ hp hm => posCrit_inter_negCrit F c γ hp hm
  obtain ⟨U₁, U₂, hU₁, hU₂, hpU, hmU, hUU⟩ :=
    SeparatedNhds.of_isCompact_isCompact (isCompact_posCrit F hfin c)
      (isCompact_negCrit F hfin c) hdis
  refine ⟨halfSym (U₁ ∩ reverseSphere ⁻¹' U₂),
    halfSym_isOpen (hU₁.inter (hU₂.preimage (reverseSphere_continuous n))),
    posCrit_subset_halfSym fun γ hγ =>
      (Set.mem_inter_iff _ _ _).mpr ⟨hpU hγ, Set.mem_preimage.mpr (hmU ⟨γ, hγ, rfl⟩)⟩,
    half_mem_halfSym, Set.disjoint_left.mpr fun u hu hu' => ?_⟩
  have h1 := ((Set.mem_inter_iff _ _ _).mp (mem_halfSym.mp hu).1).2
  have h2 := ((Set.mem_inter_iff _ _ _).mp (mem_halfSym.mp (Set.mem_preimage.mp hu')).1).1
  exact Set.disjoint_left.mp hUU h2 (Set.mem_preimage.mp h1)

variable {c : ℝ} {Up : Set (Loops n)}

/-- The orbit neighbourhood of a prime image cut down to the halves. -/
def orbitSet (r : ℝ) (Up : Set (Loops n)) (s : Set (Sphere n)) : Set (Loops n) :=
  nbhd F c r s ∩ (Up ∪ reverseSphere ⁻¹' Up)

/-- Its positive half. -/
def orbitHalf (r : ℝ) (Up : Set (Loops n)) (s : Set (Sphere n)) : Set (Loops n) :=
  nbhd F c r s ∩ Up

theorem orbitSet_isOpen {r : ℝ} (hUp : IsOpen Up) (s : Set (Sphere n)) :
    IsOpen (orbitSet (F := F) (c := c) r Up s) :=
  (nbhd_isOpen F c r s).inter (hUp.union (hUp.preimage (reverseSphere_continuous n)))

theorem orbitHalf_isOpen {r : ℝ} (hUp : IsOpen Up) (s : Set (Sphere n)) :
    IsOpen (orbitHalf (F := F) (c := c) r Up s) :=
  (nbhd_isOpen F c r s).inter hUp

theorem mem_orbitSet {r : ℝ} {s : Set (Sphere n)} {u : SphereLoop n} :
    u ∈ orbitSet (F := F) (c := c) r Up s ↔
      u ∈ nbhd F c r s ∧ (u ∈ Up ∨ reverseSphere u ∈ Up) :=
  (Set.mem_inter_iff _ _ _).trans (and_congr Iff.rfl
    ((Set.mem_union _ _ _).trans (or_congr Iff.rfl Set.mem_preimage)))

theorem mem_orbitHalf {r : ℝ} {s : Set (Sphere n)} {u : SphereLoop n} :
    u ∈ orbitHalf (F := F) (c := c) r Up s ↔ u ∈ nbhd F c r s ∧ u ∈ Up :=
  Set.mem_inter_iff _ _ _

theorem kInv_orbitSet {r : ℝ} (hhalf : ∀ u, half +ᵥ u ∈ Up ↔ u ∈ Up) (s : Set (Sphere n)) :
    KInv (orbitSet (F := F) (c := c) r Up s) where
  rev_mem u hu := by
    obtain ⟨h1, h2⟩ := mem_orbitSet.mp hu
    refine mem_orbitSet.mpr ⟨(kInv_nbhd F c r s).rev_mem u h1, ?_⟩
    rw [reverseSphere_involutive]
    exact h2.symm
  half_mem u hu := by
    obtain ⟨h1, h2⟩ := mem_orbitSet.mp hu
    refine mem_orbitSet.mpr ⟨(kInv_nbhd F c r s).half_mem u h1, ?_⟩
    rw [reverse_half, hhalf, hhalf]
    exact h2

/-- The reversal exchanges the loops of the orbit set inside and outside its positive half. -/
theorem orbitHalf_swap {r : ℝ} (hUU : Disjoint Up (reverseSphere ⁻¹' Up)) (s : Set (Sphere n)) :
    ∀ u ∈ orbitSet (F := F) (c := c) r Up s,
      reverseSphere u ∈ orbitHalf (F := F) (c := c) r Up s ↔
        u ∉ orbitHalf (F := F) (c := c) r Up s := by
  intro u hu
  obtain ⟨h1, h2⟩ := mem_orbitSet.mp hu
  rw [mem_orbitHalf, mem_orbitHalf]
  constructor
  · rintro ⟨_, h⟩ ⟨_, h'⟩
    exact Set.disjoint_left.mp hUU h' (Set.mem_preimage.mpr h)
  · intro hn
    refine ⟨(kInv_nbhd F c r s).rev_mem u h1, ?_⟩
    rcases h2 with h | h
    · exact absurd ⟨h1, h⟩ hn
    · exact h

theorem orbitSet_disjoint {r : ℝ} {s s' : Set (Sphere n)}
    (h : Disjoint (nbhd F c r s) (nbhd F c r s')) :
    Disjoint (orbitSet (F := F) (c := c) r Up s) (orbitSet (F := F) (c := c) r Up s') :=
  h.mono inter_subset_left inter_subset_left

/-- The critical loops of the level lie in the orbit sets. -/
theorem crit_subset_orbitSet {r : ℝ} (hpU : posCrit F c ⊆ Up)
    (hmem : ∀ s, ∀ γ ∈ orbitCrit F c s, (γ : Loops n) ∈ nbhd F c r s) :
    posCrit F c ∪ negCrit F c ⊆ ⋃ s, orbitSet (F := F) (c := c) r Up s := by
  rintro γ (h | h)
  · have h' := h
    rw [posCrit_eq] at h'
    obtain ⟨s, -, hs⟩ := mem_iUnion₂.mp h'
    exact mem_iUnion.mpr ⟨s, mem_orbitSet.mpr ⟨hmem s γ (Or.inl hs), Or.inl (hpU h)⟩⟩
  · have h' := h
    rw [negCrit_eq] at h'
    obtain ⟨s, -, hs⟩ := mem_iUnion₂.mp h'
    refine mem_iUnion.mpr ⟨s, mem_orbitSet.mpr ⟨hmem s γ (Or.inr hs), Or.inr ?_⟩⟩
    obtain ⟨γ', hγ', rfl⟩ := h
    rw [reverseSphere_involutive]
    exact hpU hγ'

/-- **Polygon orbit sets.** The polygons near the orbit sets are open, invariant under the
reversal and the rotation by M, pairwise disjoint, with halves exchanged by the reversal, and
they contain the stationary polygons of a band in which c is the only critical level. -/
theorem polyOrbits (hfin : (primeImages F).Finite) (hc : 0 < c) :
    ∃ (r : ℝ) (Up : Set (Loops n)), 0 < r ∧
      (∀ s, IsOpen (near P (orbitSet (F := F) (c := c) r Up s))) ∧
      (∀ s, Inv (kPoly n M) (near P (orbitSet (F := F) (c := c) r Up s))) ∧
      (Pairwise fun s s' => Disjoint (near P (orbitSet (F := F) (c := c) r Up s))
        (near P (orbitSet (F := F) (c := c) r Up s'))) ∧
      (∀ s, IsOpen (near P (orbitHalf (F := F) (c := c) r Up s))) ∧
      (∀ s, ∀ q ∈ near P (orbitSet (F := F) (c := c) r Up s),
        (kPoly n M).ρ q ∈ near P (orbitHalf (F := F) (c := c) r Up s) ↔
          q ∉ near P (orbitHalf (F := F) (c := c) r Up s)) ∧
      ∀ {a₀ b₀ : ℝ}, 0 < a₀ → a₀ ≤ b₀ → (∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) →
        ∀ q : ZMod (2 * M) → Sphere n, ShortPolygon P.δ q → PolyCritical F (2 * M) q →
          a₀ ^ 2 ≤ energy F (2 * M) q → energy F (2 * M) q ≤ b₀ ^ 2 →
          ∃ s, q ∈ near P (orbitSet (F := F) (c := c) r Up s) := by
  obtain ⟨r, hr, -, -, hdis, hmem, -⟩ := exists_orbit_nhds F hfin hc
  obtain ⟨Up, hUp, hpU, hhalf, hUU⟩ := exists_half (F := F) hfin c
  refine ⟨r, Up, hr, fun s => near_isOpen P (orbitSet_isOpen hUp s),
    fun s => near_inv P (kInv_orbitSet hhalf s),
    fun s s' hne => near_disjoint P (orbitSet_disjoint (hdis hne)),
    fun s => near_isOpen P (orbitHalf_isOpen hUp s),
    fun s => near_swap P (orbitHalf_swap hUU s), ?_⟩
  intro a₀ b₀ ha₀ hab₀ hone q hq hcq ha hb
  have h := crit_subset_orbitSet (F := F) (c := c) hpU hmem
    (broken_mem_crit P ha₀ hab₀ hone hq hcq ha hb)
  obtain ⟨s, hs⟩ := mem_iUnion.mp h
  exact ⟨s, hq, hs⟩

end

end Finsler.PolyOrbits
