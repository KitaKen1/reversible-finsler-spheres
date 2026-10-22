module

public import Finsler.Topology.EquivariantK
public import Finsler.Topology.EvalFunctionals
public import Finsler.Topology.HalfRetract
public import Finsler.Topology.HalfDeform

/-! A power of U = v(v + w) vanishes on the K-Borel cohomology of a sublevel relative to its
loops fixed by the half rotation. Let r be a deformation of the sublevel X = t_b into a compact
part P of it which commutes with the reversal and the half rotation. For a functional ψ which is
odd under the half rotation and even or odd under the reversal, the loops u of X with
ψ(r u) ≠ 0 form an open invariant set split by the half rotation. A loop not fixed by the half
rotation has a nonvanishing evaluation functional; so, by compactness, finitely many
functionals suffice for the loops of P outside a given open set O containing the fixed loops of
P. With O the neighbourhood of the fixed loops T of X which deforms onto them, X is covered by
N = r⁻¹(O) and finitely many split sets; hence a power of U vanishes on the K-Borel cohomology
of (X, N). Restriction from (X, T) to (N, T) vanishes, because r maps (N, T) into (O, T), whose
K-Borel cohomology vanishes, and r is bijective on that of (X, T). By exactness, the K-Borel
cohomology of (X, N) maps onto that of (X, T), where the same power of U therefore vanishes. -/

@[expose] public section

namespace Finsler.LocalCoverK

open Set Topology
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelCochain Finsler.BorelLoop Finsler.BorelIterate Finsler.BorelK
open Finsler.BorelLens Finsler.BorelLocalK Finsler.BorelFixed Finsler.BorelCoverK
open Finsler.FunctionalCover Finsler.EvalFunctionals Finsler.EquivariantK
open Finsler.MilnorHomotopy Finsler.MilnorEquivariance

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Invariant sets -/

section Sets

variable (F : ReversibleMetric n) (b : ℝ)

theorem kInv_lev : KInv (lev F b) :=
  ⟨fun _ hu => reverse_mem_lev F hu, fun _ hu => half_mem_lev F hu⟩

theorem kInv_consts : KInv (consts n) :=
  ⟨fun _ hu => reverse_mem_consts hu, fun _ hu => half_mem_consts hu⟩

theorem mem_fixLev_iff (u : SphereLoop n) : u ∈ fixLev F b ↔ u ∈ lev F b ∧ half +ᵥ u = u := by
  constructor
  · intro hu
    refine ⟨?_, fixLev_subset_halfFixed F b hu⟩
    rcases hu with ⟨h1, -⟩ | h
    · exact Or.inl h1
    · exact Or.inr h
  · rintro ⟨hu | hu, hfix⟩
    · exact Or.inl ⟨hu, hfix⟩
    · exact Or.inr hu

theorem fixLev_subset_lev : fixLev F b ⊆ lev F b := fun u hu => ((mem_fixLev_iff F b u).mp hu).1

theorem kInv_fixLev : KInv (fixLev F b) :=
  ⟨fun _ hu => reverse_mem_fixLev F hu, fun u hu => by
    rw [((mem_fixLev_iff F b u).mp hu).2]
    exact hu⟩

end Sets

/-! ### Functionals not vanishing on a loop -/

/-- A loop not fixed by the half rotation has a nonvanishing evaluation functional. -/
theorem exists_functional_ne {u : SphereLoop n} (hu : half +ᵥ u ≠ u) :
    ∃ f : OddFunctional n, f.ψ u ≠ 0 := by
  have ht : ∃ t : ℝ, pt u (t + 1 / 2) ≠ pt u t := by
    by_contra hall
    apply hu
    apply Finsler.HalfRetract.eq_of_pt
    intro t _
    have h1 : pt (half +ᵥ u) t = pt u (t + 1 / 2) := pt_vadd u (1 / 2) t
    rw [h1]
    by_contra hne
    exact hall ⟨t, hne⟩
  obtain ⟨t, ht⟩ := ht
  obtain ⟨e, he_def⟩ : ∃ e : Ambient n,
      e = (pt u t : Ambient n) - (pt u (t + 1 / 2) : Ambient n) := ⟨_, rfl⟩
  have he : e ≠ 0 := by
    rw [he_def]
    exact sub_ne_zero.mpr fun h => ht (Subtype.ext h).symm
  have hd : diff t e u ≠ 0 := by
    have h : diff t e u = ‖e‖ ^ 2 := by
      unfold diff
      rw [← he_def, real_inner_self_eq_norm_sq]
    rw [h]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  by_contra hno
  have h1 : diff t e u + diff (-t) e u = 0 := by
    by_contra h
    exact hno ⟨evenFunctional t e, h⟩
  have h2 : diff t e u - diff (-t) e u = 0 := by
    by_contra h
    exact hno ⟨oddFunctional t e, h⟩
  apply hd
  linarith

/-- For a compact set of loops and an open set containing its loops fixed by the half rotation,
finitely many functionals do not vanish simultaneously on a loop of the compact set outside the
open set. -/
theorem exists_functional_cover {P O : Set (Loops n)} (hP : IsCompact P) (hO : IsOpen O)
    (hfix : ∀ u : SphereLoop n, u ∈ P → half +ᵥ u = u → u ∈ O) :
    ∃ l : List (OddFunctional n), ∀ u : SphereLoop n, u ∈ P → u ∈ O ∨ ∃ f ∈ l, f.ψ u ≠ 0 := by
  have hK : IsCompact (P \ O) := hP.diff hO
  have hcov : P \ O ⊆ ⋃ f : OddFunctional n, {v : Loops n | f.ψ v ≠ 0} := by
    intro u hu
    obtain ⟨f, hf⟩ := exists_functional_ne (fun h => hu.2 (hfix u hu.1 h))
    exact mem_iUnion.mpr ⟨f, hf⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun f : OddFunctional n => {v : Loops n | f.ψ v ≠ 0})
    (fun f => isOpen_ne_fun f.continuous continuous_const) hcov
  refine ⟨s.toList, fun u hu => ?_⟩
  by_cases huO : u ∈ O
  · exact Or.inl huO
  · obtain ⟨f, hf⟩ := mem_iUnion.mp (hs ⟨hu, huO⟩)
    obtain ⟨hfs, hne⟩ := mem_iUnion.mp hf
    exact Or.inr ⟨f, Finset.mem_toList.mpr hfs, hne⟩

/-! ### Sets split by a functional along a deformation -/

section Split

variable {F : ReversibleMetric n} {b : ℝ} (d : Finsler.HalfDeform.Data F b) (f : OddFunctional n)

/-- The loops of t_b whose image under the deformation has positive functional. -/
def posSet : Set (Loops n) :=
  Subtype.val '' {x : lev F b | 0 < f.ψ (d.r x : SphereLoop n)}

/-- The loops of t_b whose image under the deformation has negative functional. -/
def negSet : Set (Loops n) :=
  Subtype.val '' {x : lev F b | f.ψ (d.r x : SphereLoop n) < 0}

theorem psi_cont : Continuous fun x : lev F b => f.ψ (d.r x : SphereLoop n) :=
  f.continuous.comp (continuous_subtype_val.comp d.r.continuous)

theorem posSet_isOpen (hb : 0 < b) : IsOpen (posSet d f) :=
  (lev_isOpen F hb).isOpenMap_subtype_val _ (isOpen_lt continuous_const (psi_cont d f))

theorem negSet_isOpen (hb : 0 < b) : IsOpen (negSet d f) :=
  (lev_isOpen F hb).isOpenMap_subtype_val _ (isOpen_lt (psi_cont d f) continuous_const)

theorem psi_half (x : lev F b) :
    f.ψ (d.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : SphereLoop n) =
      -f.ψ (d.r x : SphereLoop n) := by
  have h : ((d.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : lev F b) : SphereLoop n) =
      half +ᵥ (d.r x : SphereLoop n) := Finsler.HalfDeform.data_half d x
  rw [h, f.half_odd]

theorem psi_rev (x : lev F b) :
    f.ψ (d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : SphereLoop n) =
      f.ψ (reverseSphere (d.r x : SphereLoop n)) := by
  have h : ((d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : lev F b) :
      SphereLoop n) = reverseSphere (d.r x : SphereLoop n) := d.rev x
  rw [h]

theorem half_posSet {u : SphereLoop n} (hu : u ∈ posSet d f) : half +ᵥ u ∈ negSet d f := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : 0 < f.ψ (d.r x : SphereLoop n) := hx
  refine ⟨⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩, ?_, rfl⟩
  change f.ψ (d.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : SphereLoop n) < 0
  rw [psi_half]
  linarith

theorem half_negSet {u : SphereLoop n} (hu : u ∈ negSet d f) : half +ᵥ u ∈ posSet d f := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : f.ψ (d.r x : SphereLoop n) < 0 := hx
  refine ⟨⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩, ?_, rfl⟩
  change 0 < f.ψ (d.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : SphereLoop n)
  rw [psi_half]
  linarith

theorem rev_pos_of_even (h : ∀ u, f.ψ (reverseSphere u) = f.ψ u) {u : SphereLoop n}
    (hu : u ∈ posSet d f) : reverseSphere u ∈ posSet d f := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : 0 < f.ψ (d.r x : SphereLoop n) := hx
  refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
  change 0 < f.ψ (d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : SphereLoop n)
  rw [psi_rev, h]
  exact hx'

theorem rev_neg_of_even (h : ∀ u, f.ψ (reverseSphere u) = f.ψ u) {u : SphereLoop n}
    (hu : u ∈ negSet d f) : reverseSphere u ∈ negSet d f := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : f.ψ (d.r x : SphereLoop n) < 0 := hx
  refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
  change f.ψ (d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : SphereLoop n) < 0
  rw [psi_rev, h]
  exact hx'

theorem rev_pos_of_odd (h : ∀ u, f.ψ (reverseSphere u) = -f.ψ u) {u : SphereLoop n}
    (hu : u ∈ posSet d f) : reverseSphere u ∈ negSet d f := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : 0 < f.ψ (d.r x : SphereLoop n) := hx
  refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
  change f.ψ (d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : SphereLoop n) < 0
  rw [psi_rev, h]
  linarith

theorem rev_neg_of_odd (h : ∀ u, f.ψ (reverseSphere u) = -f.ψ u) {u : SphereLoop n}
    (hu : u ∈ negSet d f) : reverseSphere u ∈ posSet d f := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : f.ψ (d.r x : SphereLoop n) < 0 := hx
  refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
  change 0 < f.ψ (d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : SphereLoop n)
  rw [psi_rev, h]
  linarith

/-- The loops of t_b on whose image under the deformation the functional does not vanish, as an
open invariant set split by the half rotation. -/
def typedAlong (hb : 0 < b) : Typed n where
  V := posSet d f ∪ negSet d f
  isOpen := (posSet_isOpen d f hb).union (negSet_isOpen d f hb)
  inv :=
    ⟨fun u hu => by
        rcases f.rev_parity with h | h
        · rcases hu with hu | hu
          · exact Or.inl (rev_pos_of_even d f h hu)
          · exact Or.inr (rev_neg_of_even d f h hu)
        · rcases hu with hu | hu
          · exact Or.inr (rev_pos_of_odd d f h hu)
          · exact Or.inl (rev_neg_of_odd d f h hu),
      fun u hu => by
        rcases hu with hu | hu
        · exact Or.inr (half_posSet d f hu)
        · exact Or.inl (half_negSet d f hu)⟩
  split :=
    { pos := posSet d f
      neg := negSet d f
      pos_open := posSet_isOpen d f hb
      neg_open := negSet_isOpen d f hb
      cover := subset_rfl
      disjoint := by
        rintro u - ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
        have hyx : y = x := Subtype.ext hxy
        subst hyx
        have hx' : 0 < f.ψ (d.r y : SphereLoop n) := hx
        have hy' : f.ψ (d.r y : SphereLoop n) < 0 := hy
        linarith
      half_pos := fun _ hu => half_posSet d f hu
      half_neg := fun _ hu => half_negSet d f hu }
  type := by
    rcases f.rev_parity with h | h
    · exact Or.inl ⟨fun _ hu => rev_pos_of_even d f h hu, fun _ hu => rev_neg_of_even d f h hu⟩
    · exact Or.inr ⟨fun _ hu => rev_pos_of_odd d f h hu, fun _ hu => rev_neg_of_odd d f h hu⟩

theorem typedAlong_subset (hb : 0 < b) : (typedAlong d f hb).V ⊆ lev F b := by
  rintro u (⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) <;> exact x.2

theorem mem_typedAlong (hb : 0 < b) (x : lev F b) (hx : f.ψ (d.r x : SphereLoop n) ≠ 0) :
    (x : Loops n) ∈ (typedAlong d f hb).V := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact Or.inr ⟨x, h, rfl⟩
  · exact Or.inl ⟨x, h, rfl⟩

end Split

/-! ### The preimage of the neighbourhood of the fixed loops -/

section PreTube

variable {F : ReversibleMetric n} {b : ℝ} (d : Finsler.HalfDeform.Data F b)

/-- The loops of t_b which the deformation maps into the neighbourhood of the fixed loops. -/
def preTube : Set (Loops n) :=
  Subtype.val '' {x : lev F b | (d.r x : Loops n) ∈ Finsler.HalfRetract.tube (lev F b)}

theorem preTube_subset : preTube d ⊆ lev F b := by
  rintro u ⟨x, -, rfl⟩
  exact x.2

theorem preTube_isOpen (hb : 0 < b) : IsOpen (preTube d) :=
  (lev_isOpen F hb).isOpenMap_subtype_val _
    ((Finsler.HalfRetract.tube_isOpen (lev_isOpen F hb)).preimage
      (continuous_subtype_val.comp d.r.continuous))

theorem kInv_tube : KInv (Finsler.HalfRetract.tube (lev F b)) :=
  ⟨fun _ hu => Finsler.HalfRetract.rev_mem_tube (fun _ h => reverse_mem_lev F h) hu,
    fun _ hu => Finsler.HalfRetract.half_mem_tube (fun _ h => half_mem_lev F h) hu⟩

theorem kInv_preTube : KInv (preTube d) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hu
    have hx' : (d.r x : Loops n) ∈ Finsler.HalfRetract.tube (lev F b) := hx
    refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
    change (d.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : Loops n) ∈
      Finsler.HalfRetract.tube (lev F b)
    rw [d.rev x]
    exact (kInv_tube (F := F) (b := b)).rev_mem _ hx'
  · obtain ⟨x, hx, rfl⟩ := hu
    have hx' : (d.r x : Loops n) ∈ Finsler.HalfRetract.tube (lev F b) := hx
    refine ⟨⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩, ?_, rfl⟩
    change (d.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : Loops n) ∈
      Finsler.HalfRetract.tube (lev F b)
    rw [Finsler.HalfDeform.data_half d x]
    exact (kInv_tube (F := F) (b := b)).half_mem _ hx'

/-- The deformation maps the fixed loops of t_b to fixed loops. -/
theorem r_mem_fixLev (x : lev F b) (hx : (x : Loops n) ∈ fixLev F b) :
    (d.r x : Loops n) ∈ fixLev F b := by
  have hfix : half +ᵥ (x : SphereLoop n) = x := ((mem_fixLev_iff F b _).mp hx).2
  have e : (⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : lev F b) = x := Subtype.ext hfix
  have h := Finsler.HalfDeform.data_half d x
  rw [e] at h
  exact (mem_fixLev_iff F b _).mpr ⟨(d.r x).2, h.symm⟩

/-- The homotopy of the deformation keeps the fixed loops of t_b. -/
theorem H_mem_fixLev (τ : _root_.unitInterval) (x : lev F b) (hx : (x : Loops n) ∈ fixLev F b) :
    (d.H (τ, x) : Loops n) ∈ fixLev F b := by
  have hfix : half +ᵥ (x : SphereLoop n) = x := ((mem_fixLev_iff F b _).mp hx).2
  have e : (⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : lev F b) = x := Subtype.ext hfix
  have h := d.half_H τ x
  rw [e] at h
  exact (mem_fixLev_iff F b _).mpr ⟨(d.H (τ, x)).2, h.symm⟩

theorem fixLev_subset_tube : fixLev F b ⊆ Finsler.HalfRetract.tube (lev F b) :=
  Finsler.HalfRetract.fixed_subset_tube (mem_fixLev_iff F b)

theorem fixLev_subset_preTube : fixLev F b ⊆ preTube d := fun u hu =>
  ⟨⟨u, fixLev_subset_lev F b hu⟩,
    fixLev_subset_tube (r_mem_fixLev d ⟨u, fixLev_subset_lev F b hu⟩ hu), rfl⟩

theorem r_mem_tube (x : lev F b) (hx : (x : Loops n) ∈ preTube d) :
    (d.r x : Loops n) ∈ Finsler.HalfRetract.tube (lev F b) := by
  obtain ⟨y, hy, hyx⟩ := hx
  have e : y = x := Subtype.ext hyx
  subst e
  exact hy

end PreTube

/-! ### The power of U on the cohomology relative to the fixed loops -/

section Main

variable {F : ReversibleMetric n} {b : ℝ}

/-- The K-Borel cohomology of the neighbourhood of the fixed loops relative to them vanishes. -/
theorem HR_tube_eq_zero (q : ℕ)
    (z : HR (borelInv (kCommuting (fixLev_subset_tube (F := F) (b := b)) (kInv_fixLev F b)
      (kInv_tube (F := F) (b := b)))) q) : z = 0 := by
  have hbij := bijective_subCommHom (subset_rfl : fixLev F b ⊆ fixLev F b)
    (kInv_fixLev F b).rev_mem (kInv_fixLev F b).rev_mem (kInv_fixLev F b).half_mem
    (kInv_fixLev F b).half_mem (fixLev_subset_tube (F := F) (b := b))
    (kInv_fixLev F b).rev_mem (kInv_tube (F := F) (b := b)).rev_mem
    (kInv_fixLev F b).half_mem (kInv_tube (F := F) (b := b)).half_mem subset_rfl
    (fixLev_subset_tube (F := F) (b := b))
    (fun j => Finsler.HalfRetract.bijective_nativePull_tube (mem_fixLev_iff F b) j)
  apply (hbij q).1
  rw [map_zero]
  exact HR_eq_zero_of_subset (subset_rfl : fixLev F b ⊆ fixLev F b) subset_rfl
    (kInv_fixLev F b) (kInv_fixLev F b) q _

/-- If the sublevel t_b has a deformation into a compact part of it commuting with the half
rotation, a power of U = v(v + w) vanishes on the K-Borel cohomology of t_b relative to its
loops fixed by the half rotation. -/
theorem exists_ann_fixed (hb : 0 < b) (d : Finsler.HalfDeform.Data F b) :
    ∃ k : ℕ, ∀ (q : ℕ)
      (x : HR (borelInv (kCommuting (fixLev_subset_lev F b) (kInv_fixLev F b) (kInv_lev F b))) q),
      Ann (kCommuting (fixLev_subset_lev F b) (kInv_fixLev F b) (kInv_lev F b)) k q x := by
  have hXo : IsOpen (lev F b) := lev_isOpen F hb
  obtain ⟨l, hl⟩ := exists_functional_cover d.compact (Finsler.HalfRetract.tube_isOpen hXo)
    (fun u hu h => Finsler.HalfRetract.fixed_mem_tube (d.subset hu) h)
  have h1 : lev F b ⊆ unionOf (preTube d) (l.map fun f => typedAlong d f hb) := by
    intro u hu
    rcases hl (d.r ⟨u, hu⟩ : SphereLoop n) (d.r_mem ⟨u, hu⟩) with hO | ⟨f, hf, hne⟩
    · exact subset_unionOf _ _ ⟨⟨u, hu⟩, hO, rfl⟩
    · exact mem_unionOf_of_mem (List.mem_map.mpr ⟨f, hf, rfl⟩)
        (mem_typedAlong d f hb ⟨u, hu⟩ hne)
  have h2 : unionOf (preTube d) (l.map fun f => typedAlong d f hb) ⊆ lev F b :=
    unionOf_subset (preTube_subset d) fun T hT => by
      obtain ⟨f, -, rfl⟩ := List.mem_map.mp hT
      exact typedAlong_subset d f hb
  have hann := ann_of_cover (preTube_subset d) (kInv_preTube d) (kInv_lev F b)
    (preTube_isOpen d hb) (l.map fun f => typedAlong d f hb) h1 h2
  refine ⟨l.length, fun q x => ?_⟩
  have hres := restriction_eq_zero (fixLev_subset_preTube d) (preTube_subset d)
    (fixLev_subset_tube (F := F) (b := b)) Finsler.HalfRetract.tube_subset (kInv_fixLev F b)
    (kInv_preTube d) (kInv_tube (F := F) (b := b)) (kInv_lev F b) d.r (r_mem_fixLev d)
    (r_mem_tube d) d.rev (Finsler.HalfDeform.data_half d) d.H (H_mem_fixLev d) HR_tube_eq_zero q x
  obtain ⟨z, rfl⟩ := exact_triple (fixLev_subset_preTube d) (preTube_subset d) (kInv_fixLev F b)
    (kInv_preTube d) (kInv_lev F b) q x hres
  have hz := hann q z
  rw [List.length_map] at hz
  exact ann_map (kHom ((fixLev_subset_preTube d).trans (preTube_subset d)) (kInv_fixLev F b)
    (kInv_lev F b) (preTube_subset d) (kInv_preTube d) (kInv_lev F b) (fixLev_subset_preTube d)
    subset_rfl) l.length q z hz

end Main

end

end Finsler.LocalCoverK
