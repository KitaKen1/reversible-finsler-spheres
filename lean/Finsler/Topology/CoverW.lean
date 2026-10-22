module

public import Finsler.Topology.NilpotentW
public import Finsler.Topology.SmallLevel

/-! Powers of w from covers by oriented sets.

For reversal-invariant sets of loops s ⊆ t ⊆ u the relative cochains of (u, t), (u, s), (t, s)
form a short exact sequence of involutive complexes. If V is an open reversal-invariant set with
an orientation (two open sets covering V, disjoint on V, exchanged by the reversal) and t is
open, then the restriction from (t ∪ V, t) to (V ∩ (t ∪ V), V ∩ t) is an excision and w acts as
zero on the latter pair. Hence, if the k-th power of w vanishes on the reflection Borel
cohomology of (t, s), the (k+1)-st power vanishes on that of (t ∪ V, s). By induction, if X is
the union of an open invariant set N and k oriented open invariant sets, w^k vanishes on the
reflection Borel cohomology of (X, N).

For a local lens of a crossing (cuts a ≤ b, set V), the crossing group of (t_b, t_a) receives a
surjection from the reflection Borel cohomology of (t_b, Y), which is isomorphic to that of the
lens pair (N ∩ t_b, N ∩ Y) inside V; so a power of w vanishing on the lens pair vanishes on the
crossing group. The passage from tight to wide cuts holds for powers of w as for w. This is the
form of W-ZERO needed for critical manifolds which are not split by the reversal (for the round
sphere: the m-fold great circles), with one oriented set for each coordinate of a reversal-odd
vector-valued functional. -/

@[expose] public section

namespace Finsler.CoverW

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelDeformation Finsler.BorelLens Finsler.AvoidPoint Finsler.BorelLocal
open Finsler.NilpotentW Finsler.Geometry Finsler.RegularInterval

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- A reversal-invariant set of loops. -/
def RInv (A : Set (Loops n)) : Prop := ∀ u : SphereLoop n, u ∈ A → reverseSphere u ∈ A

theorem rInv_union {A B : Set (Loops n)} (hA : RInv A) (hB : RInv B) : RInv (A ∪ B) :=
  fun u hu => hu.elim (fun h => Or.inl (hA u h)) (fun h => Or.inr (hB u h))

theorem rInv_inter {A B : Set (Loops n)} (hA : RInv A) (hB : RInv B) : RInv (A ∩ B) :=
  fun u hu => ⟨hA u hu.1, hB u hu.2⟩

/-- The involutive complex of relative cochains of a pair of reversal-invariant sets. -/
abbrev rC {s t : Set (Loops n)} (hst : s ⊆ t) (hs : RInv s) (ht : RInv t) : InvComplex :=
  ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)

/-! ### Transport of powers of w -/

section Transport

variable {K L : InvComplex} (φ : InvHom K L)

theorem wPow_zero_of_injective (k q : ℕ) (hinj : Function.Injective (HRmap φ (q + k)))
    (h : ∀ y : HR L q, wPow L q k y = 0) (x : HR K q) : wPow K q k x = 0 :=
  hinj (by rw [HRmap_wPow, h, map_zero])

theorem wPow_zero_of_surjective (k q : ℕ) (hsurj : Function.Surjective (HRmap φ q))
    (h : ∀ x : HR K q, wPow K q k x = 0) (y : HR L q) : wPow L q k y = 0 := by
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← HRmap_wPow, h, map_zero]

end Transport

/-! ### Triples -/

section Triple

variable {s t u : Set (Loops n)} (hst : s ⊆ t) (htu : t ⊆ u) (hs : RInv s) (ht : RInv t)
  (hu : RInv u)

/-- The relative cochains of (u, t), (u, s), (t, s) form a short exact sequence. -/
theorem shortExact_incl :
    BorelExact.ShortExact (subHom (hst.trans htu) htu hs hu ht hu hst subset_rfl)
      (subHom hst (hst.trans htu) hs ht hs hu subset_rfl htu) := by
  have e1 : inclPair (hst.trans htu) htu hst subset_rfl = relPair hst htu := by
    ext : 2 <;> rfl
  have e2 : inclPair hst (hst.trans htu) subset_rfl htu = incPair hst htu := by
    ext : 2 <;> rfl
  refine ⟨fun j => ?_, fun j => ?_, fun j z => ?_, fun j x hx => ?_⟩
  · change Function.Injective
      (RelativeCupCochain.pullback (inclPair (hst.trans htu) htu hst subset_rfl) j)
    rw [e1]
    exact rel_injective hst htu j
  · change Function.Surjective
      (RelativeCupCochain.pullback (inclPair hst (hst.trans htu) subset_rfl htu) j)
    rw [e2]
    exact inc_surjective hst htu j
  · change RelativeCupCochain.pullback (inclPair hst (hst.trans htu) subset_rfl htu) j
      (RelativeCupCochain.pullback (inclPair (hst.trans htu) htu hst subset_rfl) j z) = 0
    rw [e1, e2]
    exact rel_inc_zero hst htu j z
  · change RelativeCupCochain.pullback (inclPair hst (hst.trans htu) subset_rfl htu) j x = 0
      at hx
    rw [e2] at hx
    obtain ⟨ψ, hψ⟩ := inc_exact hst htu j x hx
    refine ⟨ψ, ?_⟩
    change RelativeCupCochain.pullback (inclPair (hst.trans htu) htu hst subset_rfl) j ψ = x
    rw [e1]
    exact hψ

end Triple

/-! ### Covers -/

/-- Adding an oriented open invariant set: if w^k vanishes on the reflection Borel cohomology
of (t, s), then w^{k+1} vanishes on that of (t ∪ V, s). -/
theorem wPow_union {s t V : Set (Loops n)} (hst : s ⊆ t) (hs : RInv s) (ht : RInv t)
    (hV : RInv V) (hto : IsOpen t) (hVo : IsOpen V) (O : Orientation V) (k : ℕ)
    (h : ∀ (q : ℕ) (x : HR (rC hst hs ht) q), wPow (rC hst hs ht) q k x = 0) (q : ℕ)
    (x : HR (rC (hst.trans subset_union_left) hs (rInv_union ht hV)) q) :
    wPow (rC (hst.trans subset_union_left) hs (rInv_union ht hV)) q (k + 1) x = 0 := by
  have htu : t ⊆ t ∪ V := subset_union_left
  have hu := rInv_union ht hV
  have hex := shortExact_incl hst htu hs ht hu
  have h1 : HRmap (subHom hst (hst.trans htu) hs ht hs hu subset_rfl htu) (q + k)
      (wPow _ q k x) = 0 := by
    rw [HRmap_wPow, h]
  obtain ⟨z, hz⟩ := BorelExact.exact_mid hex (q + k) _ h1
  have hE : V ∩ t ⊆ V ∩ (t ∪ V) := inter_subset_inter_right V htu
  have hbij := bijective_subHom hE htu (rInv_inter hV ht) (rInv_inter hV hu) ht hu
    inter_subset_right inter_subset_right
    (fun j => bijective_nativePull_excision V htu hto hVo subset_rfl j)
  have hwz : w _ (q + k) z = 0 := by
    apply (hbij (q + k + 1)).1
    rw [map_zero, HRmap_w]
    exact subW_zero O hE (rInv_inter hV ht) (rInv_inter hV hu) inter_subset_left (q + k) _
  rw [wPow_succ, ← hz, ← HRmap_w, hwz, map_zero]

/-- An open reversal-invariant set of loops with an orientation. -/
structure Oriented (n : ℕ) where
  V : Set (Loops n)
  isOpen : IsOpen V
  inv : RInv V
  orient : Orientation V

/-- The union of a set and a list of oriented sets. -/
def unionOf (N : Set (Loops n)) : List (Oriented n) → Set (Loops n)
  | [] => N
  | T :: l => unionOf N l ∪ T.V

theorem subset_unionOf (N : Set (Loops n)) (l : List (Oriented n)) : N ⊆ unionOf N l := by
  induction l with
  | nil => exact subset_rfl
  | cons T l ih => exact ih.trans subset_union_left

theorem unionOf_isOpen {N : Set (Loops n)} (hN : IsOpen N) (l : List (Oriented n)) :
    IsOpen (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact ih.union T.isOpen

theorem unionOf_inv {N : Set (Loops n)} (hN : RInv N) (l : List (Oriented n)) :
    RInv (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact rInv_union ih T.inv

/-- The reflection Borel cohomology of a pair of equal sets vanishes. -/
theorem HR_eq_zero_of_subset {s t : Set (Loops n)} (hst : s ⊆ t) (hts : t ⊆ s) (hs : RInv s)
    (ht : RInv t) (q : ℕ) (x : HR (rC hst hs ht) q) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_zero_iff_bcoboundary]
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero]
  funext j
  exact (Finsler.SmallLevel.relative_eq_zero hst hts j _).symm

/-- For an open invariant set N and a list of oriented sets, the power of w given by the length
of the list vanishes on the reflection Borel cohomology of the pair of the union and N. -/
theorem wPow_unionOf {N : Set (Loops n)} (hN : RInv N) (hNo : IsOpen N) (l : List (Oriented n)) :
    ∀ (q : ℕ) (x : HR (rC (subset_unionOf N l) hN (unionOf_inv hN l)) q),
      wPow (rC (subset_unionOf N l) hN (unionOf_inv hN l)) q l.length x = 0 := by
  induction l with
  | nil =>
    intro q x
    exact HR_eq_zero_of_subset (subset_unionOf N []) subset_rfl hN (unionOf_inv hN []) q x
  | cons T l ih =>
    intro q x
    exact wPow_union (subset_unionOf N l) hN (unionOf_inv hN l) T.inv (unionOf_isOpen hNo l)
      T.isOpen T.orient l.length ih q x

/-- If an invariant set X is the union of an open invariant set N and a list of oriented sets,
the power of w given by the length of the list vanishes on the reflection Borel cohomology of
(X, N). -/
theorem wPow_of_cover {N X : Set (Loops n)} (hNX : N ⊆ X) (hN : RInv N) (hX : RInv X)
    (hNo : IsOpen N) (l : List (Oriented n)) (h1 : X ⊆ unionOf N l) (h2 : unionOf N l ⊆ X)
    (q : ℕ) (x : HR (rC hNX hN hX) q) : wPow (rC hNX hN hX) q l.length x = 0 := by
  have hbij := bijective_subHom hNX (subset_unionOf N l) hN hX hN (unionOf_inv hN l) subset_rfl
    h1 (fun j => bijective_nativePull_of_eq hNX (subset_unionOf N l) subset_rfl h1 subset_rfl
      h2 j)
  obtain ⟨y, rfl⟩ := (hbij q).2 x
  rw [← HRmap_wPow, wPow_unionOf hN hNo l q y, map_zero]

/-! ### Crossings -/

variable (F : ReversibleMetric n) {a b : ℝ} {V : Set (Loops n)}

/-- For a local lens: a power of w vanishing on the lens pair vanishes on the crossing group of
(t_b, t_a). -/
theorem crossW_pow_zero_of_localLens (hab : a ≤ b) (L : LocalLens F a b V) (k : ℕ)
    (hV : ∀ (q : ℕ) (y : HR (rC (inter_subset_inter_right L.N L.subset_lev)
        (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
        (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)) q),
      wPow (rC (inter_subset_inter_right L.N L.subset_lev)
        (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
        (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)) q k y = 0)
    (q : ℕ) (z : HR (crossComplex F hab) q) : wPow (crossComplex F hab) q k z = 0 := by
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
  have h2 := wPow_zero_of_injective
    (subHom hC L.subset_lev hCs hCt L.Y_rev hrb inter_subset_right inter_subset_right) k q
    (bijective_subHom hC L.subset_lev hCs hCt L.Y_rev hrb inter_subset_right
      inter_subset_right
      (fun j => bijective_nativePull_excision L.N L.subset_lev L.Y_open L.N_open L.cover j)
      (q + k)).1 (hV q)
  have h3 := wPow_zero_of_surjective
    (subHom hA L.subset_lev hra hrb L.Y_rev hrb L.lev_subset subset_rfl) k q
    (localLens_surjective F L q) h2
  have hbij := BorelInvariance.bijective_HRmap
    (revSub_sq (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu))
    (revCross_sq F hab) (toCross (lev_mono F hab) F hab subset_rfl subset_rfl)
    (toCross_equivariant (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu) F hab subset_rfl subset_rfl)
    (fun j => bijective_nativePull_of_eq (lev_mono F hab) (lev_mono F hab) subset_rfl
      subset_rfl subset_rfl subset_rfl j) (q + k)
  exact wPow_zero_of_injective _ k q hbij.1 h3 z

/-- From tight cuts to wide cuts for powers of w. -/
theorem crossW_pow_zero_of_tight {a a' b' b : ℝ} (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b)
    (D₁ : LevelDeformation F a a' b') (D₂ : LevelDeformation F b' b b) (k q : ℕ)
    (htight : ∀ z' : HR (crossComplex F hab') q, wPow (crossComplex F hab') q k z' = 0)
    (z : HR (crossComplex F (haa.trans (hab'.trans hbb))) q) :
    wPow (crossComplex F (haa.trans (hab'.trans hbb))) q k z = 0 := by
  have hst : lev F a ⊆ lev F b' := lev_mono F (haa.trans hab')
  have hs : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have ht : ∀ u : SphereLoop n, u ∈ lev F b' → reverseSphere u ∈ lev F b' :=
    fun _ hu => reverse_mem_lev F hu
  have h1 := BorelInvariance.bijective_HRmap (revSub_sq hst hs ht)
    (revCross_sq F (haa.trans (hab'.trans hbb)))
    (toCross hst F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb))
    (toCross_equivariant hst hs ht F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb))
    (fun j => bijective_nativePull hst (lev_mono F hbb) (toDeformation D₂ a) j)
  have h2 := BorelInvariance.bijective_HRmap (revSub_sq hst hs ht) (revCross_sq F hab')
    (toCross hst F hab' (lev_mono F haa) subset_rfl)
    (toCross_equivariant hst hs ht F hab' (lev_mono F haa) subset_rfl)
    (fun j => bijective_nativePull_inclPair hst (lev_mono F hab') (lev_mono F haa) subset_rfl
      (toPairDeformation D₁) j)
  have hmid := wPow_zero_of_surjective _ k q (h2 q).2 htight
  exact wPow_zero_of_injective _ k q (h1 (q + k)).1 hmid z

theorem wPow_zero_vec (K : InvComplex) (q : ℕ) : ∀ k, wPow K q k (0 : HR K q) = 0
  | 0 => rfl
  | k + 1 => by rw [wPow_succ, wPow_zero_vec K q k, map_zero]

/-- Powers of w on single crossings from level deformations and local lenses on whose lens
pairs the power vanishes. -/
theorem crossW_pow_zero_of_flow (crit : Set ℝ) (k : ℕ)
    (hreg : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      Nonempty (LevelDeformation F a a' b))
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit) (hbc : b ∉ crit)
    (hsub : (crit ∩ Icc a b).Subsingleton)
    (hlens : ∀ c ∈ crit ∩ Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∀ a' b' : ℝ, c - ε < a' → a' < c →
      c < b' → b' < c + ε → ∃ (W : Set (Loops n)) (L : LocalLens F a' b' W),
        ∀ (q : ℕ) (y : HR (rC (inter_subset_inter_right L.N L.subset_lev)
          (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
          (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)) q),
          wPow (rC (inter_subset_inter_right L.N L.subset_lev)
            (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
            (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)) q k y = 0)
    (q : ℕ) (z : HR (crossComplex F hab) q) : wPow (crossComplex F hab) q k z = 0 := by
  by_cases hne : (crit ∩ Icc a b).Nonempty
  · obtain ⟨c, hc, hcab⟩ := hne
    have hac' : a < c := lt_of_le_of_ne hcab.1 (fun h => hac (h ▸ hc))
    have hcb' : c < b := lt_of_le_of_ne hcab.2 (fun h => hbc (h ▸ hc))
    obtain ⟨ε, hε, hL⟩ := hlens c ⟨hc, hcab⟩
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
    obtain ⟨W, L, hLv⟩ := hL a' b' ((le_max_right _ _).trans_lt ha'1) ha'2 hb'1
      (hb'2.trans_le (min_le_right _ _))
    exact crossW_pow_zero_of_tight F haa hab' hbb D₁ D₂ k q
      (fun z' => crossW_pow_zero_of_localLens F hab' L k hLv q z') z
  · have hreg₀ : ∀ x ∈ Icc a b, x ∉ crit := fun x hx hxc => hne ⟨x, hxc, hx⟩
    obtain ⟨D⟩ := hreg a b b ha hab le_rfl hreg₀
    rw [crossing_eq_zero F hab D q z, wPow_zero_vec]

end

end Finsler.CoverW
