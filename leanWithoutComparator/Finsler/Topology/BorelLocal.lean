module

public import Finsler.Topology.Shortening
public import Finsler.Topology.BorelFree

/-! Local lenses and the vanishing of w on crossing groups. The vanishing of w is transported
along maps of involutive complexes: backwards along a map injective in the next degree, and
forwards along a surjective map; where w acts as zero, forgetting the action is injective in the
next degree and the transfer is surjective. An orientation of a set V of loops consists of two open sets
covering V, disjoint on V and exchanged by reversal; on every pair of reversal-invariant sets
of loops inside an oriented set, w acts as zero (the involution exchanges the closed and open
set of positive loops with its complement). A local lens for levels a ≤ b and a set V is a lens
whose N-part below b lies in V instead of avoiding a point. For a local lens, restriction from
(t_b, Y) to (t_b, t_a) is surjective and restriction from (t_b, Y) to (N ∩ t_b, N ∩ Y) is an
excision, so if w acts as zero on the pairs of reversal-invariant sets inside V, it acts as
zero on the crossing group of (t_b, t_a). The passage from tight to wide cuts and the
construction of local lenses from shortenings are as for e. The existence of oriented
neighbourhoods of the critical set and the corresponding localization of the curve shortening
map are separate geometric statements and are not proved here. -/

@[expose] public section

namespace Finsler.BorelLocal

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevReverse Finsler.SobolevReflectionAction
open Finsler.BorelDeformation Finsler.AvoidPoint Finsler.BorelLens Finsler.RegularInterval

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Transport

variable {K L : InvComplex} (φ : InvHom K L)

/-- If w acts as zero on the target and the map is injective in the next degree, w acts as
zero on the source. -/
theorem w_zero_of_injective (q : ℕ) (hinj : Function.Injective (HRmap φ (q + 1)))
    (h : ∀ y : HR L q, w L q y = 0) (x : HR K q) : w K q x = 0 := by
  apply hinj
  rw [HRmap_w, h, map_zero]

/-- If w acts as zero on the source and the map is surjective, w acts as zero on the target. -/
theorem w_zero_of_surjective (q : ℕ) (hsurj : Function.Surjective (HRmap φ q))
    (h : ∀ x : HR K q, w K q x = 0) (y : HR L q) : w L q y = 0 := by
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← HRmap_w, h, map_zero]

/-- If w acts as zero in degree q, forgetting the action is injective in degree q + 1. -/
theorem forget_injective_of_w_zero (K : InvComplex) (q : ℕ) (h : ∀ y : HR K q, w K q y = 0) :
    Function.Injective (forget K (q + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_forget K q x).mp hx
  exact h y

/-- If w acts as zero in degree q, the transfer is surjective in degree q. -/
theorem transfer_surjective_of_w_zero (K : InvComplex) (q : ℕ) (h : ∀ y : HR K q, w K q y = 0) :
    Function.Surjective (transfer K q) := fun y => (exact_w K q y).mp (h y)

end Transport

variable {n : ℕ}

/-- An orientation of a set V of loops: two open sets covering V, disjoint on V and exchanged
by reversal. -/
structure Orientation (V : Set (Loops n)) where
  pos : Set (Loops n)
  neg : Set (Loops n)
  pos_open : IsOpen pos
  neg_open : IsOpen neg
  cover : V ⊆ pos ∪ neg
  disjoint : ∀ u : Loops n, u ∈ V → u ∈ pos → u ∈ neg → False
  rev_pos : ∀ u : SphereLoop n, u ∈ pos → reverseSphere u ∈ neg
  rev_neg : ∀ u : SphereLoop n, u ∈ neg → reverseSphere u ∈ pos

/-- On a pair of reversal-invariant sets of loops inside an oriented set, w acts as zero. -/
theorem subW_zero {V : Set (Loops n)} (O : Orientation V) {s t : Set (Loops n)} (hst : s ⊆ t)
    (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
    (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t) (htV : t ⊆ V) (q : ℕ)
    (y : HR (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) q) :
    w (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) q y = 0 := by
  have hcompl : ({x : t | (x : Loops n) ∈ O.pos} : Set t)ᶜ = {x : t | (x : Loops n) ∈ O.neg} := by
    ext x
    constructor
    · intro hx
      rcases O.cover (htV x.2) with h | h
      · exact absurd h hx
      · exact h
    · intro hx hpos
      exact O.disjoint _ (htV x.2) hpos hx
  have hclosed : IsClosed ({x : t | (x : Loops n) ∈ O.pos} : Set t) := by
    rw [← isOpen_compl_iff, hcompl]
    exact O.neg_open.preimage continuous_subtype_val
  have hopen : IsOpen ({x : t | (x : Loops n) ∈ O.pos} : Set t) :=
    O.pos_open.preimage continuous_subtype_val
  refine BorelFree.w_eq_zero_of_isClopen (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)
    {x : t | (x : Loops n) ∈ O.pos} ⟨hclosed, hopen⟩ (fun x => ⟨fun hrx hx => ?_, fun hx => ?_⟩)
    q y
  · exact O.disjoint _ (htV (ht _ x.2)) hrx (O.rev_pos _ hx)
  · rcases O.cover (htV x.2) with h | h
    · exact absurd h hx
    · exact O.rev_neg _ h

variable (F : ReversibleMetric n) {a b : ℝ}

/-- A local lens for the levels a ≤ b and a set V of loops: open reversal-invariant sets Y and
N of loops with t_a ⊆ Y ⊆ t_b ⊆ Y ∪ N, such that the loops of N below b lie in V, and a map of
t_b commuting with reversal which takes Y into t_a and is homotopic to the identity through
maps keeping t_a. -/
structure LocalLens (F : ReversibleMetric n) (a b : ℝ) (V : Set (Loops n)) where
  Y : Set (Loops n)
  N : Set (Loops n)
  Y_open : IsOpen Y
  N_open : IsOpen N
  Y_rev : ∀ u : SphereLoop n, u ∈ Y → reverseSphere u ∈ Y
  N_rev : ∀ u : SphereLoop n, u ∈ N → reverseSphere u ∈ N
  lev_subset : lev F a ⊆ Y
  subset_lev : Y ⊆ lev F b
  cover : lev F b ⊆ Y ∪ N
  inside : N ∩ lev F b ⊆ V
  retraction : Retraction (lev F a) Y (lev F b)
  rev_comm : ∀ x : lev F b,
    (retraction.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : Loops n) =
      reverseSphere (retraction.r x : SphereLoop n)

/-- A lens for a point is a local lens for the set of loops avoiding the point. -/
def ofLens {p : Sphere n} (L : Lens F a b p) : LocalLens F a b (avoid p) where
  Y := L.Y
  N := L.N
  Y_open := L.Y_open
  N_open := L.N_open
  Y_rev := L.Y_rev
  N_rev := L.N_rev
  lev_subset := L.lev_subset
  subset_lev := L.subset_lev
  cover := L.cover
  inside := L.avoids
  retraction := L.retraction
  rev_comm := L.rev_comm

variable {V : Set (Loops n)}

/-- For a local lens, restriction from (t_b, Y) to (t_b, t_a) is surjective on reflection
Borel cohomology. -/
theorem localLens_surjective (L : LocalLens F a b V) (q : ℕ) :
    Function.Surjective (HRmap (subHom (L.lev_subset.trans L.subset_lev) L.subset_lev
      (fun _ hu => reverse_mem_lev F hu) (fun _ hu => reverse_mem_lev F hu) L.Y_rev
      (fun _ hu => reverse_mem_lev F hu) L.lev_subset subset_rfl) q) := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hcomm : (revSet hrb).comp L.retraction.r = L.retraction.r.comp (revSet hrb) :=
    ContinuousMap.ext fun x => Subtype.ext (L.rev_comm x).symm
  have hR : retractPair L.lev_subset L.subset_lev L.retraction ≫ revSub hA hra hrb =
      revSub L.subset_lev L.Y_rev hrb ≫ retractPair L.lev_subset L.subset_lev L.retraction :=
    (pairMap_comp L.subset_lev hA hA L.retraction.r (revSet hrb)
      (fun x hx => L.retraction.r_mem x hx) (fun _ hx => hra _ hx)).symm.trans
      ((pairMap_congr _ _ hcomm _ _).trans
        (pairMap_comp L.subset_lev L.subset_lev hA (revSet hrb) L.retraction.r
          (fun _ hx => L.Y_rev _ hx) (fun x hx => L.retraction.r_mem x hx)))
  have hj := inclPair_equivariant hA L.subset_lev hra hrb L.Y_rev hrb L.lev_subset subset_rfl
  have hjR : (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) ≫ revSub hA hra hrb =
      revSub hA hra hrb ≫ (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) := by
    rw [Category.assoc, hR, ← Category.assoc, hj, Category.assoc]
  have hB := BorelInvariance.bijective_HRmap (revSub_sq hA hra hrb) (revSub_sq hA hra hrb)
    (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
      retractPair L.lev_subset L.subset_lev L.retraction) hjR
    (fun k => bijective_nativePull_retract L.lev_subset L.subset_lev L.retraction k) q
  intro y
  obtain ⟨x, hx⟩ := hB.2 y
  refine ⟨HRmap (pullHom (revSub_sq L.subset_lev L.Y_rev hrb) (revSub_sq hA hra hrb)
    (retractPair L.lev_subset L.subset_lev L.retraction) hR) q x, ?_⟩
  rw [← hx, ← HRmap_comp]
  exact (HRmap_congr (pullHom_comp (revSub_sq hA hra hrb)
    (revSub_sq L.subset_lev L.Y_rev hrb) (revSub_sq hA hra hrb)
    (inclPair hA L.subset_lev L.lev_subset subset_rfl)
    (retractPair L.lev_subset L.subset_lev L.retraction) hj hR hjR) q x).symm

/-- For a local lens: if w acts as zero on the pairs of reversal-invariant sets of loops inside
V, it acts as zero on the crossing group of (t_b, t_a). -/
theorem crossW_zero_of_localLens (hab : a ≤ b) (L : LocalLens F a b V)
    (hV : ∀ (s t : Set (Loops n)) (hst : s ⊆ t)
      (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
      (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t), t ⊆ V → ∀ (q : ℕ)
      (y : HR (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) q),
      w (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) q y = 0)
    (q : ℕ) (z : HR (crossComplex F hab) q) : w (crossComplex F hab) q z = 0 := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hC : L.N ∩ L.Y ⊆ L.N ∩ lev F b := inter_subset_inter_right L.N L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hCs : ∀ u : SphereLoop n, u ∈ L.N ∩ L.Y → reverseSphere u ∈ L.N ∩ L.Y :=
    fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩
  have hCt : ∀ u : SphereLoop n, u ∈ L.N ∩ lev F b → reverseSphere u ∈ L.N ∩ lev F b :=
    fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩
  have h1 := hV _ _ hC hCs hCt L.inside q
  have h2 := w_zero_of_injective
    (subHom hC L.subset_lev hCs hCt L.Y_rev hrb inter_subset_right inter_subset_right) q
    (bijective_subHom hC L.subset_lev hCs hCt L.Y_rev hrb inter_subset_right
      inter_subset_right
      (fun k => bijective_nativePull_excision L.N L.subset_lev L.Y_open L.N_open L.cover k)
      (q + 1)).1 h1
  have h3 := w_zero_of_surjective
    (subHom hA L.subset_lev hra hrb L.Y_rev hrb L.lev_subset subset_rfl) q
    (localLens_surjective F L q) h2
  have hbij := BorelInvariance.bijective_HRmap
    (revSub_sq (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu))
    (revCross_sq F hab) (toCross (lev_mono F hab) F hab subset_rfl subset_rfl)
    (toCross_equivariant (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu) F hab subset_rfl subset_rfl)
    (fun k => bijective_nativePull_of_eq (lev_mono F hab) (lev_mono F hab) subset_rfl
      subset_rfl subset_rfl subset_rfl k) (q + 1)
  exact w_zero_of_injective _ q hbij.1 h3 z

/-- From tight cuts to wide cuts for w. Let a ≤ a' ≤ b' ≤ b. If [a, a'] carries a level
deformation of t_{b'}, [b', b] carries a level deformation, and w acts as zero on the crossing
group of (t_{b'}, t_{a'}), then w acts as zero on the crossing group of (t_b, t_a). -/
theorem crossW_zero_of_tight {a a' b' b : ℝ} (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b)
    (D₁ : LevelDeformation F a a' b') (D₂ : LevelDeformation F b' b b) (q : ℕ)
    (htight : ∀ z' : HR (crossComplex F hab') q, w (crossComplex F hab') q z' = 0)
    (z : HR (crossComplex F (haa.trans (hab'.trans hbb))) q) :
    w (crossComplex F (haa.trans (hab'.trans hbb))) q z = 0 := by
  have hst : lev F a ⊆ lev F b' := lev_mono F (haa.trans hab')
  have hs : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have ht : ∀ u : SphereLoop n, u ∈ lev F b' → reverseSphere u ∈ lev F b' :=
    fun _ hu => reverse_mem_lev F hu
  have h1 := BorelInvariance.bijective_HRmap (revSub_sq hst hs ht)
    (revCross_sq F (haa.trans (hab'.trans hbb)))
    (toCross hst F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb))
    (toCross_equivariant hst hs ht F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb))
    (fun k => bijective_nativePull hst (lev_mono F hbb) (toDeformation D₂ a) k)
  have h2 := BorelInvariance.bijective_HRmap (revSub_sq hst hs ht) (revCross_sq F hab')
    (toCross hst F hab' (lev_mono F haa) subset_rfl)
    (toCross_equivariant hst hs ht F hab' (lev_mono F haa) subset_rfl)
    (fun k => bijective_nativePull_inclPair hst (lev_mono F hab') (lev_mono F haa) subset_rfl
      (toPairDeformation D₁) k)
  have hmid := w_zero_of_surjective _ q (h2 q).2 htight
  exact w_zero_of_injective _ q (h1 (q + 1)).1 hmid z

/-- The vanishing of w on single crossings from level deformations and oriented local lenses.
Let crit be a set of levels such that every interval [a, a'] without points of crit carries
level deformations of every t_b with a' ≤ b, and such that tight cuts around each point c of
crit carry local lenses for an oriented set of loops. Then for regular cuts 0 < a ≤ b with at
most one point of crit between them, w acts as zero on the reflection Borel cohomology of the
crossing pair (t_b, t_a). -/
theorem crossW_zero_of_flow (crit : Set ℝ)
    (hreg : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      Nonempty (LevelDeformation F a a' b))
    (hlens : ∀ c ∈ crit, ∃ (V : Set (Loops n)) (_ : Orientation V) (ε : ℝ), 0 < ε ∧
      ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε → Nonempty (LocalLens F a b V))
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit) (hbc : b ∉ crit)
    (hsub : (crit ∩ Icc a b).Subsingleton) (q : ℕ) (z : HR (crossComplex F hab) q) :
    w (crossComplex F hab) q z = 0 := by
  by_cases hne : (crit ∩ Icc a b).Nonempty
  · obtain ⟨c, hc, hcab⟩ := hne
    have hac' : a < c := lt_of_le_of_ne hcab.1 (fun h => hac (h ▸ hc))
    have hcb' : c < b := lt_of_le_of_ne hcab.2 (fun h => hbc (h ▸ hc))
    obtain ⟨V, O, ε, hε, hL⟩ := hlens c hc
    obtain ⟨a', ha'1, ha'2⟩ := exists_between (max_lt hac' (sub_lt_self c hε))
    obtain ⟨b', hb'1, hb'2⟩ := exists_between (lt_min hcb' (lt_add_of_pos_right c hε))
    have haa : a ≤ a' := (le_max_left _ _).trans ha'1.le
    have hbb : b' ≤ b := hb'2.le.trans (min_le_left _ _)
    have hab' : a' ≤ b' := (ha'2.trans hb'1).le
    have hreg₁ : ∀ x ∈ Icc a a', x ∉ crit := by
      intro x hx hxc
      have hxe : x = c := hsub ⟨hxc, hx.1, hx.2.trans (ha'2.le.trans hcb'.le)⟩ ⟨hc, hcab⟩
      rw [hxe] at hx
      exact absurd hx.2 (not_le.mpr ha'2)
    have hreg₂ : ∀ x ∈ Icc b' b, x ∉ crit := by
      intro x hx hxc
      have hxe : x = c := hsub ⟨hxc, (hac'.le.trans hb'1.le).trans hx.1, hx.2⟩ ⟨hc, hcab⟩
      rw [hxe] at hx
      exact absurd hx.1 (not_le.mpr hb'1)
    obtain ⟨D₁⟩ := hreg a a' b' ha haa hab' hreg₁
    obtain ⟨D₂⟩ := hreg b' b b (ha.trans_le (haa.trans hab')) hbb le_rfl hreg₂
    obtain ⟨L⟩ := hL a' b' ((le_max_right _ _).trans_lt ha'1) ha'2 hb'1
      (hb'2.trans_le (min_le_right _ _))
    exact crossW_zero_of_tight F haa hab' hbb D₁ D₂ q
      (fun z' => crossW_zero_of_localLens F hab' L
        (fun s t hst hs ht htV q' y => subW_zero O hst hs ht htV q' y) q z') z
  · have hreg₀ : ∀ x ∈ Icc a b, x ∉ crit := fun x hx hxc => hne ⟨x, hxc, hx⟩
    obtain ⟨D⟩ := hreg a b b ha hab le_rfl hreg₀
    rw [crossing_eq_zero F hab D q z, map_zero]

section Shortening

variable {F} {b : ℝ} (S : Shortening.Data F b)

/-- The local lens of a shortening D of t_b for cuts a' < a ≤ b and a set V containing the
loops x of t_b with √E(D x) > a'. -/
def localLens {a a' : ℝ} (V : Set (Loops n)) (ha : 0 < a) (ha' : a' < a) (hab : a ≤ b)
    (hloc : ∀ x : lev F b, a' < Real.sqrt (energy F (S.D x : SphereLoop n)) →
      (x : Loops n) ∈ V) : LocalLens F a b V where
  Y := Subtype.val '' {x : lev F b | Real.sqrt (energy F (S.D x : SphereLoop n)) < a}
  N := Subtype.val '' {x : lev F b | a' < Real.sqrt (energy F (S.D x : SphereLoop n))}
  Y_open := (lev_isOpen F (ha.trans_le hab)).isOpenMap_subtype_val _
    (isOpen_lt (Shortening.continuous_sqrt_energy_D S) continuous_const)
  N_open := (lev_isOpen F (ha.trans_le hab)).isOpenMap_subtype_val _
    (isOpen_lt continuous_const (Shortening.continuous_sqrt_energy_D S))
  Y_rev := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
    change Real.sqrt (energy F (S.D ⟨reverseSphere (x : SphereLoop n),
      reverse_mem_lev F x.2⟩ : SphereLoop n)) < a
    rw [S.rev x, energy_reverseSphere]
    exact hx
  N_rev := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
    change a' < Real.sqrt (energy F (S.D ⟨reverseSphere (x : SphereLoop n),
      reverse_mem_lev F x.2⟩ : SphereLoop n))
    rw [S.rev x, energy_reverseSphere]
    exact hx
  lev_subset := by
    intro u hu
    refine ⟨⟨u, lev_mono F hab hu⟩, ?_, rfl⟩
    have hle : Real.sqrt (energy F (S.D ⟨u, lev_mono F hab hu⟩ : SphereLoop n)) ≤
        Real.sqrt (energy F u) :=
      Real.sqrt_le_sqrt (Shortening.energy_D_le S ⟨u, lev_mono F hab hu⟩)
    rcases hu with hu | ⟨y, rfl⟩
    · exact lt_of_le_of_lt hle hu
    · rw [energy_constantSphereLoop, Real.sqrt_zero] at hle
      exact lt_of_le_of_lt hle ha
  subset_lev := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  cover := by
    intro u hu
    rcases lt_or_ge (Real.sqrt (energy F (S.D ⟨u, hu⟩ : SphereLoop n))) a with h | h
    · exact Or.inl ⟨⟨u, hu⟩, h, rfl⟩
    · exact Or.inr ⟨⟨u, hu⟩, lt_of_lt_of_le ha' h, rfl⟩
  inside := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    exact hloc x hx
  retraction :=
    { r := S.D
      r_mem := by
        rintro x ⟨x', hx', hxx⟩
        have he : x' = x := Subtype.ext hxx
        rw [he] at hx'
        exact Or.inl hx'
      H := S.G
      keep := fun τ x hx => mem_lev_of_energy_le F (S.energy_le τ x) hx }
  rev_comm := S.rev

end Shortening

/-- Local lenses from shortenings: if for tight cuts a' < c < b around a positive level c some
shortening D of t_b is such that the loops x of t_b with √E(D x) > a' lie in V, then tight cuts
around c carry local lenses for V. -/
theorem localLens_of_shortening {c : ℝ} (hc0 : 0 < c) (V : Set (Loops n))
    (hloc : ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Shortening.Data F b, ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) → (x : Loops n) ∈ V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
      Nonempty (LocalLens F a b V) := by
  obtain ⟨ε, hε, h⟩ := hloc
  refine ⟨min ε c, lt_min hε hc0, ?_⟩
  intro a b ha1 ha2 hb1 hb2
  have ha0 : 0 < a := by
    have : c - min ε c ≥ 0 := sub_nonneg.mpr (min_le_right _ _)
    linarith
  have haε : c - ε < a := by
    have := min_le_left ε c
    linarith
  obtain ⟨a', ha'1, ha'2⟩ := exists_between haε
  have hbε : b < c + ε := by
    have := min_le_left ε c
    linarith
  obtain ⟨S, hS⟩ := h a' b ha'1 (ha'2.trans ha2) hb1 hbε
  exact ⟨localLens S V ha0 ha'2 (ha2.trans hb1).le hS⟩

end

end Finsler.BorelLocal
