module

public import Finsler.Topology.PolyFrames

/-! Windows of the orbit frames from windows of the lens pairs of the halves. The part in an open
set 𝒲 of the excised lens pair is an excision of the lens pair of 𝒲 (`LensLabels`), also inside
a set Z (relative excision, `LensFixed`); so windows of the lens pairs give windows of the parts.
If an involution preserving the function and commuting with the descent maps the complement of
an open half U inside 𝒲 = U ∪ ρ⁻¹U onto U, the lens pair of ρ⁻¹U is homeomorphic to that of U
and the lens pair of 𝒲 is the sum of the two (`LensParts`): windows of the lens pair of the half
U suffice. For the orbit frames the orbit set of a prime image is the union of its positive half
and the reversal preimage of that half. Hence the windows of the orbit frames reduce to windows of
the lens pairs of the positive halves (the polygons near the positive critical circle of the
level, a single critical circle of one oriented iterate) and of their parts in the fixed
polygons (additivity over the two halves and the same homeomorphism, the fixed polygons being
kept by the reversal): the local critical groups of one oriented critical circle. It suffices
to have, for every single crossing, one orbit frame (with a descent of one's choice, for instance
one agreeing with label descents near the orbits) with such windows (`HalfTight`); windows for all
orbit frames (`PolyFrames.FrameWindows`) are not needed, and are not to be expected for descents
which are stationary inside the orbit sets. -/

@[expose] public section

namespace Finsler.HalfLens

open CategoryTheory Set Topology
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.SobolevReverse
open Finsler.IntervalSobolev Finsler.BorelLoop Finsler.BorelK Finsler.BorelCoverK
open Finsler.BorelCochain Finsler.BorelComparison Finsler.BorelPair Finsler.PairTriple
open Finsler.PolygonLoop Finsler.PolygonModel Finsler.PolygonDescent Finsler.PolygonDescentK
open Finsler.PolygonOriented Finsler.SampleK Finsler.FixedSampleK Finsler.InvPairs
open Finsler.OrbitNbhd Finsler.OrientedCritical Finsler.CriticalLevels Finsler.FlowLens
open Finsler.LensContinuation Finsler.LensLabels Finsler.LensFamily Finsler.LensParts
open Finsler.PairAdditive Finsler.PolyOrbits Finsler.PolyModels Finsler.PolyFrames
open Finsler.LensFixed Finsler.EventSum Finsler.EventFar Finsler.CrossingSlopes
open Finsler.CriticalCircles

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Generic

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g)

/-- Vanishing of the ordinary cohomology of a pair is vanishing of its actual relative
cohomology. -/
theorem native_eq_zero {P : TopPair.{0}} {k : ℕ} (h : ∀ x : H (triv P) k, x = 0)
    (z : native P k) : z = 0 :=
  (ordinaryEquiv P (𝟙 P) (Category.comp_id _) k).symm.map_eq_zero_iff.mp (h _)

/-- **Parts from lens pairs.** If the lens pair of an open set has no cohomology in degree k,
neither has the part in it of the excised lens pair. -/
theorem part_eq_zero (hg : Continuous g) {a' a b T : ℝ} (ha : a' < a) (𝒲 : Set W) {k : ℕ}
    (h : ∀ x : lensH D 𝒲 a b T k, x = 0) :
    ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN D a' T)
      (lensY_subset D a b T)) 𝒲)) k, z = 0 := by
  refine native_eq_zero fun x => ?_
  obtain ⟨y, rfl⟩ := (piece_bijective D hg ha 𝒲 k).2 x
  rw [h y, map_zero]

/-- The lens pair of 𝒲 inside Z. -/
theorem fixLens_sub (𝒲 Z : Set W) (a b T : ℝ) :
    partY g D 𝒲 a b T ∩ Z ⊆ partU g 𝒲 b ∩ Z :=
  inter_subset_inter_left Z (partY_sub_partU g D 𝒲 a b T)

/-- **Fixed parts from the lens pairs inside Z.** If the lens pair of an open set inside Z has no
cohomology in degree k, neither has the part inside Z of the excised lens pair. -/
theorem fixPart_eq_zero (hg : Continuous g) {a' a b T : ℝ} (ha : a' < a) (𝒲 Z : Set W)
    {k : ℕ} (h : ∀ x : H (triv (pairOf (fixLens_sub D 𝒲 Z a b T))) k, x = 0) :
    ∀ z : native (pairOf (part_sub (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))) 𝒲)) k, z = 0 := by
  have hA : IsOpen (Subtype.val ⁻¹' (partY g D 𝒲 a b T ∩ Z) : Set ↥(partU g 𝒲 b ∩ Z)) := by
    have e : (Subtype.val ⁻¹' (partY g D 𝒲 a b T ∩ Z) : Set ↥(partU g 𝒲 b ∩ Z)) =
        Subtype.val ⁻¹' {w : W | g (D.flow T w) < a} := by
      ext w
      constructor
      · intro hw
        exact Set.mem_ofPred_eq ▸ (Set.mem_preimage.mp hw).1.2.1
      · intro hw
        exact Set.mem_preimage.mpr
          ⟨⟨w.2.1.1, Set.mem_preimage.mp hw, w.2.1.2⟩, w.2.2⟩
    rw [e]
    exact (isOpen_lt (hg.comp (flow_continuous D T)) continuous_const).preimage
      continuous_subtype_val
  have hN : IsOpen (Subtype.val ⁻¹' lensN D a' T : Set ↥(partU g 𝒲 b ∩ Z)) :=
    (lensN_isOpen D hg a' T).preimage continuous_subtype_val
  have hcov : partU g 𝒲 b ∩ Z ⊆ (partY g D 𝒲 a b T ∩ Z) ∪ lensN D a' T := by
    intro w hw
    by_cases h' : g (D.flow T w) < a
    · exact Or.inl ⟨⟨hw.1.1, h', hw.1.2⟩, hw.2⟩
    · exact Or.inr (lt_of_lt_of_le ha (not_lt.mp h'))
  have hexc := bijective_nativePull_excision_rel (lensN D a' T) (fixLens_sub D 𝒲 Z a b T) hA hN
    hcov k
  have hz : ∀ z : native (pairOf (inter_subset_inter_right (lensN D a' T)
      (fixLens_sub D 𝒲 Z a b T))) k, z = 0 := by
    intro z
    obtain ⟨y, rfl⟩ := hexc.2 z
    rw [native_eq_zero h y, map_zero]
  have heq := Finsler.BorelLens.bijective_nativePull_of_eq
    (part_sub (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))) 𝒲)
    (inter_subset_inter_right (lensN D a' T) (fixLens_sub D 𝒲 Z a b T))
    (fun _ hw => ⟨hw.1.1, ⟨hw.1.2.1.1, hw.1.2.1.2, hw.2⟩, hw.1.2.2⟩)
    (fun _ hw => ⟨hw.1.1, ⟨hw.1.2.1, hw.2⟩, hw.1.2.2⟩)
    (fun _ hw => ⟨⟨hw.1, ⟨hw.2.1.1, hw.2.1.2.1⟩, hw.2.2⟩, hw.2.1.2.2⟩)
    (fun _ hw => ⟨⟨hw.1, hw.2.1.1, hw.2.2⟩, hw.2.1.2⟩) k
  intro z
  obtain ⟨y, rfl⟩ := heq.2 z
  rw [hz y, map_zero]

variable (k : KAct W) (hgρ : ∀ w, g (k.ρ w) = g w)
  (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w))

/-- The involution as a homeomorphism. -/
def rhoHomeo : W ≃ₜ W where
  toFun := k.ρ
  invFun := k.ρ
  left_inv := k.ρρ
  right_inv := k.ρρ
  continuous_toFun := k.ρ.continuous
  continuous_invFun := k.ρ.continuous

include hgρ hDρ in
/-- **Halves.** If the lens pair of an open set U has no cohomology in degree n, neither has the
lens pair of U ∪ ρ⁻¹U when U and ρ⁻¹U are disjoint. -/
theorem lens_half_eq_zero {U : Set W} (hU : IsOpen U) (hdis : Disjoint U (k.ρ ⁻¹' U))
    {a b T : ℝ} {n : ℕ} (h : ∀ x : lensH D U a b T n, x = 0) :
    ∀ x : lensH D (U ∪ k.ρ ⁻¹' U) a b T n, x = 0 := by
  have hρ : ∀ x : lensH D (k.ρ ⁻¹' U) a b T n, x = 0 := by
    have hb := bijective_Hmap_of_homeomorph (partY_sub_partU g D (k.ρ ⁻¹' U) a b T)
      (partY_sub_partU g D U a b T) (rhoHomeo k)
      (fun x => by
        change g x < b ∧ x ∈ k.ρ ⁻¹' U ↔ g (k.ρ x) < b ∧ k.ρ x ∈ U
        rw [hgρ, Set.mem_preimage])
      (fun x => by
        change g x < b ∧ g (D.flow T x) < a ∧ x ∈ k.ρ ⁻¹' U ↔
          g (k.ρ x) < b ∧ g (D.flow T (k.ρ x)) < a ∧ k.ρ x ∈ U
        rw [hgρ, hDρ, hgρ, Set.mem_preimage]) n
    intro x
    obtain ⟨y, rfl⟩ := hb.2 x
    rw [h y, map_zero]
  exact union_eq_zero D hU (hU.preimage k.ρ.continuous) hdis n h hρ

/-- Vanishing transfers between pairs of equal sets. -/
theorem triv_eq_zero_of_eq {s t s' t' : Set W} (hst : s ⊆ t) (hst' : s' ⊆ t') (hs : s = s')
    (ht : t = t') {n : ℕ} (h : ∀ x : H (triv (pairOf hst')) n, x = 0) :
    ∀ x : H (triv (pairOf hst)) n, x = 0 := by
  subst hs
  subst ht
  exact h

include hgρ hDρ in
/-- **Fixed halves.** For a set Z kept by the involution, if the lens pair of an open set U
inside Z has no cohomology in degree n, neither has the lens pair of U ∪ ρ⁻¹U inside Z when U
and ρ⁻¹U are disjoint. -/
theorem fixLens_half_eq_zero {Z : Set W} (hZ : ∀ x ∈ Z, k.ρ x ∈ Z) {U : Set W} (hU : IsOpen U)
    (hdis : Disjoint U (k.ρ ⁻¹' U)) {a b T : ℝ} {n : ℕ}
    (h : ∀ x : H (triv (pairOf (fixLens_sub D U Z a b T))) n, x = 0) :
    ∀ x : H (triv (pairOf (fixLens_sub D (U ∪ k.ρ ⁻¹' U) Z a b T))) n, x = 0 := by
  have hZ' : ∀ x, x ∈ Z ↔ k.ρ x ∈ Z := fun x =>
    ⟨hZ x, fun hx => by have := hZ _ hx; rwa [k.ρρ] at this⟩
  have hρ : ∀ x : H (triv (pairOf (fixLens_sub D (k.ρ ⁻¹' U) Z a b T))) n, x = 0 := by
    have hb := bijective_Hmap_of_homeomorph (fixLens_sub D (k.ρ ⁻¹' U) Z a b T)
      (fixLens_sub D U Z a b T) (rhoHomeo k)
      (fun x => by
        change (g x < b ∧ x ∈ k.ρ ⁻¹' U) ∧ x ∈ Z ↔ (g (k.ρ x) < b ∧ k.ρ x ∈ U) ∧ k.ρ x ∈ Z
        rw [hgρ, Set.mem_preimage, ← hZ'])
      (fun x => by
        change (g x < b ∧ g (D.flow T x) < a ∧ x ∈ k.ρ ⁻¹' U) ∧ x ∈ Z ↔
          (g (k.ρ x) < b ∧ g (D.flow T (k.ρ x)) < a ∧ k.ρ x ∈ U) ∧ k.ρ x ∈ Z
        rw [hgρ, hDρ, hgρ, Set.mem_preimage, ← hZ']) n
    intro x
    obtain ⟨y, rfl⟩ := hb.2 x
    rw [h y, map_zero]
  refine eq_zero_of_parts (fixLens_sub D (U ∪ k.ρ ⁻¹' U) Z a b T) hU
    (hU.preimage k.ρ.continuous) hdis (fun _ hw => hw.1.2) n ?_ ?_
  · refine triv_eq_zero_of_eq _ (fixLens_sub D U Z a b T) ?_ ?_ h
    · ext w
      exact ⟨fun hw => ⟨⟨hw.1.1.1, hw.1.1.2.1, hw.2⟩, hw.1.2⟩,
        fun hw => ⟨⟨⟨hw.1.1, hw.1.2.1, Or.inl hw.1.2.2⟩, hw.2⟩, hw.1.2.2⟩⟩
    · ext w
      exact ⟨fun hw => ⟨⟨hw.1.1.1, hw.2⟩, hw.1.2⟩,
        fun hw => ⟨⟨⟨hw.1.1, Or.inl hw.1.2⟩, hw.2⟩, hw.1.2⟩⟩
  · refine triv_eq_zero_of_eq _ (fixLens_sub D (k.ρ ⁻¹' U) Z a b T) ?_ ?_ hρ
    · ext w
      exact ⟨fun hw => ⟨⟨hw.1.1.1, hw.1.1.2.1, hw.2⟩, hw.1.2⟩,
        fun hw => ⟨⟨⟨hw.1.1, hw.1.2.1, Or.inr hw.1.2.2⟩, hw.2⟩, hw.1.2.2⟩⟩
    · ext w
      exact ⟨fun hw => ⟨⟨hw.1.1.1, hw.2⟩, hw.1.2⟩,
        fun hw => ⟨⟨⟨hw.1.1, Or.inr hw.1.2⟩, hw.2⟩, hw.1.2⟩⟩

end Generic

section Frames

variable {n : ℕ} {F : ReversibleMetric n} {M : ℕ} [NeZero M] {L : ℝ}
  (P : PolygonModelData F L (2 * M)) {c : ℝ} {r : ℝ} {Up : Set (Loops n)}

/-- The polygons near the orbit set are the polygons near the positive half and their reversal
preimage. -/
theorem near_orbitSet_eq (hhalf : ∀ u, half +ᵥ u ∈ Up ↔ u ∈ Up)
    (hUU : Disjoint Up (reverseSphere ⁻¹' Up)) (s : Set (Sphere n)) :
    near P (orbitSet (F := F) (c := c) r Up s) =
      near P (orbitHalf (F := F) (c := c) r Up s) ∪
        (kPoly n M).ρ ⁻¹' near P (orbitHalf (F := F) (c := c) r Up s) := by
  have hsub : near P (orbitHalf (F := F) (c := c) r Up s) ⊆
      near P (orbitSet (F := F) (c := c) r Up s) := by
    rintro q ⟨hq, hb⟩
    obtain ⟨h1, h2⟩ := mem_orbitHalf.mp hb
    exact ⟨hq, mem_orbitSet.mpr ⟨h1, Or.inl h2⟩⟩
  ext q
  constructor
  · intro hq
    by_cases h : q ∈ near P (orbitHalf (F := F) (c := c) r Up s)
    · exact Or.inl h
    · exact Or.inr (Set.mem_preimage.mpr ((near_swap P (orbitHalf_swap hUU s) q hq).mpr h))
  · rintro (h | h)
    · exact hsub h
    · have h' := (near_inv P (kInv_orbitSet hhalf s)).ρ_mem _ (hsub (Set.mem_preimage.mp h))
      rwa [(kPoly n M).ρρ] at h'

theorem near_orbitHalf_disjoint (hhalf : ∀ u, half +ᵥ u ∈ Up ↔ u ∈ Up)
    (hUU : Disjoint Up (reverseSphere ⁻¹' Up)) (s : Set (Sphere n)) :
    Disjoint (near P (orbitHalf (F := F) (c := c) r Up s))
      ((kPoly n M).ρ ⁻¹' near P (orbitHalf (F := F) (c := c) r Up s)) := by
  refine Set.disjoint_left.mpr fun q hq hq' => ?_
  have hs : q ∈ near P (orbitSet (F := F) (c := c) r Up s) := by
    rw [near_orbitSet_eq P hhalf hUU s]
    exact Or.inl hq
  exact ((near_swap P (orbitHalf_swap hUU s) q hs).mp (Set.mem_preimage.mp hq')) hq

end Frames

variable {n : ℕ} (F : ReversibleMetric n)

/-- **Windows of an orbit frame from windows of its halves.** Windows of the lens pairs of the
positive halves and of their parts in the fixed polygons give windows of the parts and fixed
parts of the orbit frame, hence a polygon model of the crossing. -/
def halfModel (hn : 1 ≤ n) {a b : ℝ} {hab : a ≤ b} {ha : 0 < a} {c₀ : ℝ}
    (Fr : OrbitFrame F hab ha c₀) {A : ℝ} {S : Finset ℝ} (slope : Set (Sphere n) → ℝ)
    (hslope : ∀ s, slope s ∈ S)
    (hwin : ∀ s (i : ℕ), A < |(i : ℝ) - slope s * c₀| →
      ∀ x : lensH Fr.D (near Fr.P (orbitHalf (F := F) (c := c₀) Fr.r Fr.Up s)) (a ^ 2) (b ^ 2)
        Fr.T i, x = 0)
    (hwinh : ∀ s (l : ℕ), 2 * A < |2 * (l : ℝ) - slope s * c₀| →
      ∀ x : H (triv (pairOf (fixLens_sub Fr.D (near Fr.P (orbitHalf (F := F) (c := c₀) Fr.r
        Fr.Up s)) (fixP n Fr.M) (a ^ 2) (b ^ 2) Fr.T))) l, x = 0) :
    PolyModel F hab ha c₀ A S :=
  Fr.model slope hslope
    (fun s i hi => by
      refine part_eq_zero Fr.D (energy_continuous F hn (2 * Fr.M)) Fr.ha'' _ ?_
      rw [near_orbitSet_eq Fr.P Fr.hhalf Fr.hUU s]
      exact lens_half_eq_zero Fr.D (kPoly n Fr.M) (energy_reversePolygon F) Fr.hDρ
        (near_isOpen Fr.P (orbitHalf_isOpen Fr.hUp s))
        (near_orbitHalf_disjoint Fr.P Fr.hhalf Fr.hUU s) (hwin s i hi))
    (fun s l hl => by
      refine fixPart_eq_zero Fr.D (energy_continuous F hn (2 * Fr.M)) Fr.ha'' _ _ ?_
      rw [near_orbitSet_eq Fr.P Fr.hhalf Fr.hUU s]
      exact fixLens_half_eq_zero Fr.D (kPoly n Fr.M) (energy_reversePolygon F) Fr.hDρ
        inv_fixP.ρ_mem (near_isOpen Fr.P (orbitHalf_isOpen Fr.hUp s))
        (near_orbitHalf_disjoint Fr.P Fr.hhalf Fr.hUU s) (hwinh s l hl))

/-- For every single crossing of regular cuts, tight cuts around the critical level with an orbit
frame (with a descent of one's choice) and windows of the lens pairs of its positive halves and
of their parts in the fixed polygons: the local critical groups of one oriented critical circle,
for one good equivariant descent per crossing. -/
def HalfTight (S : Finset ℝ) (A : ℝ) : Prop :=
  ∀ (a b : ℝ), 2 * a ≤ 2 * b → ∀ ha : 0 < a, 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
    ∃ (a' b' : ℝ) (haa : a ≤ a') (hab' : a' ≤ b') (_ : b' ≤ b),
      (∀ x ∈ Icc (2 * a) (2 * a'), x ∉ crit F) ∧ (∀ x ∈ Icc (2 * b') (2 * b), x ∉ crit F) ∧
      ∃ (Fr : OrbitFrame F (by linarith : 2 * a' ≤ 2 * b') (by linarith : 0 < 2 * a') c₀)
        (slope : Set (Sphere n) → ℝ), (∀ s, slope s ∈ S) ∧
        (∀ s (i : ℕ), A < |(i : ℝ) - slope s * c₀| →
          ∀ x : lensH Fr.D (near Fr.P (orbitHalf (F := F) (c := c₀) Fr.r Fr.Up s))
            ((2 * a') ^ 2) ((2 * b') ^ 2) Fr.T i, x = 0) ∧
        (∀ s (l : ℕ), 2 * A < |2 * (l : ℝ) - slope s * c₀| →
          ∀ x : H (triv (pairOf (fixLens_sub Fr.D (near Fr.P (orbitHalf (F := F) (c := c₀)
            Fr.r Fr.Up s)) (fixP n Fr.M) ((2 * a') ^ 2) ((2 * b') ^ 2) Fr.T))) l, x = 0)

/-- Windows of the halves of one orbit frame per single crossing give polygon models of the
single crossings. -/
def polyTight (hn : 1 ≤ n) {S : Finset ℝ} {A : ℝ} (hA : 0 ≤ A) (H : HalfTight F S A) :
    PolyTight F where
  S := S
  A := A
  A_nonneg := hA
  model a b hab ha h2a h2b hsub c₀ hc₀ := by
    obtain ⟨a', b', haa, hab', hbb, h1, h2, Fr, slope, hslope, hwin, hwinh⟩ :=
      H a b hab ha h2a h2b hsub c₀ hc₀
    exact ⟨a', b', haa, hab', hbb, h1, h2, ⟨halfModel F hn Fr slope hslope hwin hwinh⟩⟩

/-- **The local bounds of the events from windows of the halves.** -/
theorem nonempty_eventBounds_of_halfTight (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {S : Finset ℝ} {A : ℝ} (hA : 0 ≤ A) (H : HalfTight F S A) :
    Nonempty (EventBounds F) :=
  nonempty_eventBounds_of_polyTight F hn hfin (polyTight F hn hA H)

/-- With the slopes among the slopes of the labels and zero, windows of the halves give the
windowed localization below the lines. -/
theorem gapLoc_of_halfTight (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {S : Finset ℝ}
    {A : ℝ} (hA : 0 ≤ A) (H : HalfTight F S A)
    (hS : S ⊆ insert (0 : ℝ) ((labels F hfin).image (slope F))) :
    Nonempty (GapLoc F hfin) :=
  gapLoc_of_polyTight F hn hfin (polyTight F hn hA H) hS

end

end Finsler.HalfLens
