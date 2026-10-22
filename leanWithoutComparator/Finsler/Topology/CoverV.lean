module

public import Finsler.Topology.BorelCoverK
public import Finsler.Topology.CrossingWK
public import Finsler.Topology.NilpotentW

/-! Powers of the class v of the half rotation from covers.

On the K-Borel cohomology of a pair of invariant sets of loops inside a set split by the half
rotation into two pieces kept by the reversal, the class v of the half rotation acts as zero
(`BorelCoverK.subV_zero`). As for w and U: if the k-th power of v vanishes on the K-Borel
cohomology of (t, s) and V is such an open invariant set, the (k+1)-st power vanishes on that of
(t ∪ V, s) (exactness of the triple and excision); if X is the union of an open invariant set N
and k such sets, v^k vanishes on the K-Borel cohomology of (X, N). For a local lens compatible
with the half rotation, a power of v vanishing on the lens pair vanishes on the K-Borel
cohomology of the crossing pair, and the passage from tight to wide cuts holds.

For the round sphere at the critical manifold of the m-fold great circles with m odd, the
coordinates of the cosine Fourier coefficient of order m are odd under the half rotation and even
under the reversal, and they do not all vanish near the critical manifold: n + 1 sets of this
kind cover it, so v^{n+1} vanishes on its K-crossing group. -/

@[expose] public section

namespace Finsler.CoverV

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelDeformation Finsler.BorelLens Finsler.AvoidPoint Finsler.BorelLocal
open Finsler.BorelIterate Finsler.BorelLocalK Finsler.BorelCoverK Finsler.NilpotentW Finsler.BorelFreeK
open Finsler.Geometry Finsler.RegularInterval Finsler.BorelK Finsler.SobolevCircleRepresentative
open Finsler.SobolevShift Finsler.SobolevCircleAction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Transport -/

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

/-! ### Covers -/

/-- Adding an open invariant set split by the half rotation into pieces kept by the reversal:
if v^k vanishes on the K-Borel cohomology of (t, s), then v^{k+1} vanishes on that of
(t ∪ V, s). -/
theorem vPow_union {s t V : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    (hV : KInv V) (hto : IsOpen t) (hVo : IsOpen V) (O : HalfSplit V) (hO : RevKeeps O)
    (k : ℕ)
    (h : ∀ (q : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q),
      wPow (borelInv (kCommuting hst hs ht)) q k x = 0) (q : ℕ)
    (x : HR (borelInv (kCommuting (hst.trans subset_union_left) hs (kInv_union ht hV))) q) :
    wPow (borelInv (kCommuting (hst.trans subset_union_left) hs (kInv_union ht hV))) q (k + 1)
      x = 0 := by
  have htu : t ⊆ t ∪ V := subset_union_left
  have hu := kInv_union ht hV
  have h1 : HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) (q + k)
      (wPow _ q k x) = 0 := by
    rw [HRmap_wPow, h]
  obtain ⟨z, hz⟩ := exact_triple hst htu hs ht hu (q + k) _ h1
  have hE : V ∩ t ⊆ V ∩ (t ∪ V) := inter_subset_inter_right V htu
  have hbij := bijective_subCommHom hE (kInv_inter hV ht).rev_mem (kInv_inter hV hu).rev_mem
    (kInv_inter hV ht).half_mem (kInv_inter hV hu).half_mem htu ht.rev_mem hu.rev_mem
    ht.half_mem hu.half_mem inter_subset_right inter_subset_right
    (fun j => bijective_nativePull_excision V htu hto hVo subset_rfl j)
  have hwz : w _ (q + k) z = 0 := by
    apply (hbij (q + k + 1)).1
    rw [map_zero, HRmap_w]
    exact subV_zero hE (kInv_inter hV ht) (kInv_inter hV hu) O inter_subset_left hO (q + k) _
  rw [wPow_succ, ← hz, ← HRmap_w, hwz, map_zero]

/-- An open invariant set of loops split by the half rotation into pieces kept by the
reversal. -/
structure Kept (n : ℕ) where
  V : Set (Loops n)
  isOpen : IsOpen V
  inv : KInv V
  split : HalfSplit V
  keeps : RevKeeps split

/-- The union of a set and a list of kept sets. -/
def unionOf (N : Set (Loops n)) : List (Kept n) → Set (Loops n)
  | [] => N
  | T :: l => unionOf N l ∪ T.V

theorem subset_unionOf (N : Set (Loops n)) (l : List (Kept n)) : N ⊆ unionOf N l := by
  induction l with
  | nil => exact subset_rfl
  | cons T l ih => exact ih.trans subset_union_left

theorem unionOf_isOpen {N : Set (Loops n)} (hN : IsOpen N) (l : List (Kept n)) :
    IsOpen (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact ih.union T.isOpen

theorem unionOf_inv {N : Set (Loops n)} (hN : KInv N) (l : List (Kept n)) :
    KInv (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact kInv_union ih T.inv

/-- For an open invariant set N and a list of kept sets, the power of v given by the length of
the list vanishes on the K-Borel cohomology of the pair of the union and N. -/
theorem vPow_unionOf {N : Set (Loops n)} (hN : KInv N) (hNo : IsOpen N) (l : List (Kept n)) :
    ∀ (q : ℕ) (x : HR (borelInv (kCommuting (subset_unionOf N l) hN (unionOf_inv hN l))) q),
      wPow (borelInv (kCommuting (subset_unionOf N l) hN (unionOf_inv hN l))) q l.length x =
        0 := by
  induction l with
  | nil =>
    intro q x
    exact HR_eq_zero_of_subset (subset_unionOf N []) subset_rfl hN (unionOf_inv hN []) q x
  | cons T l ih =>
    intro q x
    exact vPow_union (subset_unionOf N l) hN (unionOf_inv hN l) T.inv (unionOf_isOpen hNo l)
      T.isOpen T.split T.keeps l.length ih q x

/-- If an invariant set X is the union of an open invariant set N and a list of kept sets, the
power of v given by the length of the list vanishes on the K-Borel cohomology of (X, N). -/
theorem vPow_of_cover {N X : Set (Loops n)} (hNX : N ⊆ X) (hN : KInv N) (hX : KInv X)
    (hNo : IsOpen N) (l : List (Kept n)) (h1 : X ⊆ unionOf N l) (h2 : unionOf N l ⊆ X)
    (q : ℕ) (x : HR (borelInv (kCommuting hNX hN hX)) q) :
    wPow (borelInv (kCommuting hNX hN hX)) q l.length x = 0 := by
  have hbij := bijective_subCommHom hNX hN.rev_mem hX.rev_mem hN.half_mem hX.half_mem
    (subset_unionOf N l) hN.rev_mem (unionOf_inv hN l).rev_mem hN.half_mem
    (unionOf_inv hN l).half_mem subset_rfl h1
    (fun j => bijective_nativePull_of_eq hNX (subset_unionOf N l) subset_rfl h1 subset_rfl h2 j)
  obtain ⟨y, rfl⟩ := (hbij q).2 x
  rw [← HRmap_wPow, vPow_unionOf hN hNo l q y, map_zero]

/-! ### Crossings -/

variable (F : ReversibleMetric n) {a b : ℝ} {V : Set (Loops n)}

/-- For a local lens compatible with the half rotation: a power of v vanishing on the K-Borel
cohomology of the lens pair vanishes on the K-Borel cohomology of the crossing pair. -/
theorem crossV_pow_zero_of_localLens (hab : a ≤ b) (L : LocalLens F a b V) (hL : HalfLens F L)
    (k : ℕ)
    (hV : ∀ (q : ℕ) (y : HR (borelInv (subCommuting (inter_subset_inter_right L.N L.subset_lev)
        (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
        (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)
        (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
        (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev F hu.2⟩))) q),
      wPow (borelInv (subCommuting (inter_subset_inter_right L.N L.subset_lev)
        (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
        (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)
        (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
        (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev F hu.2⟩))) q k y = 0)
    (q : ℕ) (z : HR (borelInv (crossCommuting F hab)) q) :
    wPow (borelInv (crossCommuting F hab)) q k z = 0 := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hC : L.N ∩ L.Y ⊆ L.N ∩ lev F b := inter_subset_inter_right L.N L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hha : ∀ u : SphereLoop n, u ∈ lev F a → half +ᵥ u ∈ lev F a :=
    fun _ hu => half_mem_lev F hu
  have hhb : ∀ u : SphereLoop n, u ∈ lev F b → half +ᵥ u ∈ lev F b :=
    fun _ hu => half_mem_lev F hu
  have hCs : ∀ u : SphereLoop n, u ∈ L.N ∩ L.Y → reverseSphere u ∈ L.N ∩ L.Y :=
    fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩
  have hCt : ∀ u : SphereLoop n, u ∈ L.N ∩ lev F b → reverseSphere u ∈ L.N ∩ lev F b :=
    fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩
  have hhCs : ∀ u : SphereLoop n, u ∈ L.N ∩ L.Y → half +ᵥ u ∈ L.N ∩ L.Y :=
    fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩
  have hhCt : ∀ u : SphereLoop n, u ∈ L.N ∩ lev F b → half +ᵥ u ∈ L.N ∩ lev F b :=
    fun u hu => ⟨hL.N_half u hu.1, half_mem_lev F hu.2⟩
  have h2 := wPow_zero_of_injective
    (borelHom (subCommHom hC hCs hCt hhCs hhCt L.subset_lev L.Y_rev hrb hL.Y_half hhb
      inter_subset_right inter_subset_right)) k q
    (bijective_subCommHom hC hCs hCt hhCs hhCt L.subset_lev L.Y_rev hrb hL.Y_half hhb
      inter_subset_right inter_subset_right
      (fun j => bijective_nativePull_excision L.N L.subset_lev L.Y_open L.N_open L.cover j)
      (q + k)).1 (hV q)
  have h3 := wPow_zero_of_surjective
    (borelHom (subCommHom hA hra hrb hha hhb L.subset_lev L.Y_rev hrb hL.Y_half hhb
      L.lev_subset subset_rfl)) k q (halfLens_surjective F L hL q) h2
  have hbij := bijective_toCrossCommHom (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
    (fun _ hu => reverse_mem_lev F hu) (fun _ hu => half_mem_lev F hu)
    (fun _ hu => half_mem_lev F hu) F hab subset_rfl subset_rfl
    (fun j => bijective_nativePull_of_eq (lev_mono F hab) (lev_mono F hab) subset_rfl
      subset_rfl subset_rfl subset_rfl j) (q + k)
  exact wPow_zero_of_injective _ k q hbij.1 h3 z

/-- From tight cuts to wide cuts for powers of v. -/
theorem crossV_pow_zero_of_tight {a a' b' b : ℝ} (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b)
    (D₁ : LevelDeformation F a a' b') (D₂ : LevelDeformation F b' b b) (k q : ℕ)
    (htight : ∀ z' : HR (borelInv (crossCommuting F hab')) q,
      wPow (borelInv (crossCommuting F hab')) q k z' = 0)
    (z : HR (borelInv (crossCommuting F (haa.trans (hab'.trans hbb)))) q) :
    wPow (borelInv (crossCommuting F (haa.trans (hab'.trans hbb)))) q k z = 0 := by
  have hst : lev F a ⊆ lev F b' := lev_mono F (haa.trans hab')
  have hs : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have ht : ∀ u : SphereLoop n, u ∈ lev F b' → reverseSphere u ∈ lev F b' :=
    fun _ hu => reverse_mem_lev F hu
  have hhs : ∀ u : SphereLoop n, u ∈ lev F a → half +ᵥ u ∈ lev F a :=
    fun _ hu => half_mem_lev F hu
  have hht : ∀ u : SphereLoop n, u ∈ lev F b' → half +ᵥ u ∈ lev F b' :=
    fun _ hu => half_mem_lev F hu
  have h1 := bijective_toCrossCommHom hst hs ht hhs hht F (haa.trans (hab'.trans hbb))
    subset_rfl (lev_mono F hbb)
    (fun j => bijective_nativePull hst (lev_mono F hbb) (toDeformation D₂ a) j)
  have h2 := bijective_toCrossCommHom hst hs ht hhs hht F hab' (lev_mono F haa) subset_rfl
    (fun j => bijective_nativePull_inclPair hst (lev_mono F hab') (lev_mono F haa) subset_rfl
      (toPairDeformation D₁) j)
  have hmid := wPow_zero_of_surjective _ k q (h2 q).2 htight
  exact wPow_zero_of_injective _ k q (h1 (q + k)).1 hmid z

theorem wPow_zero_vec (K : InvComplex) (q : ℕ) : ∀ k, wPow K q k (0 : HR K q) = 0
  | 0 => rfl
  | k + 1 => by rw [wPow_succ, wPow_zero_vec K q k, map_zero]

/-- Powers of v on the K-Borel cohomology of single crossings from level deformations and local
lenses compatible with the half rotation on whose lens pairs the power vanishes. -/
theorem crossV_pow_zero_of_flow (crit : Set ℝ) (k : ℕ)
    (hreg : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      Nonempty (LevelDeformation F a a' b))
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit) (hbc : b ∉ crit)
    (hsub : (crit ∩ Icc a b).Subsingleton)
    (hlens : ∀ c ∈ crit ∩ Icc a b, ∃ ε : ℝ, 0 < ε ∧ ∀ a' b' : ℝ, c - ε < a' → a' < c →
      c < b' → b' < c + ε → ∃ (W : Set (Loops n)) (L : LocalLens F a' b' W) (hL : HalfLens F L),
        ∀ (q : ℕ) (y : HR (borelInv (subCommuting (inter_subset_inter_right L.N L.subset_lev)
          (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
          (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)
          (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
          (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev F hu.2⟩))) q),
          wPow (borelInv (subCommuting (inter_subset_inter_right L.N L.subset_lev)
            (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
            (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩)
            (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
            (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev F hu.2⟩))) q k y = 0)
    (q : ℕ) (z : HR (borelInv (crossCommuting F hab)) q) :
    wPow (borelInv (crossCommuting F hab)) q k z = 0 := by
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
    obtain ⟨W, L, hLh, hLv⟩ := hL a' b' ((le_max_right _ _).trans_lt ha'1) ha'2 hb'1
      (hb'2.trans_le (min_le_right _ _))
    exact crossV_pow_zero_of_tight F haa hab' hbb D₁ D₂ k q
      (fun z' => crossV_pow_zero_of_localLens F hab' L hLh k hLv q z') z
  · have hreg₀ : ∀ x ∈ Icc a b, x ∉ crit := fun x hx hxc => hne ⟨x, hxc, hx⟩
    obtain ⟨D⟩ := hreg a b b ha hab le_rfl hreg₀
    rw [HR_borelInv_eq_zero (crossCommuting F hab) (fun k y => crossing_eq_zero F hab D k y) q z,
      wPow_zero_vec]

end

end Finsler.CoverV
