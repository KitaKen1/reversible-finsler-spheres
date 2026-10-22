module

public import Finsler.Topology.EventFar

/-! The windowed localization of single crossings from a splitting into pieces. Suppose that for a
single crossing of regular cuts 2a ≤ 2b with critical level c₀ the K-Borel cochains of the
crossing pair and of the fixed crossing pair map to pieces (indexed by any type, for instance the
K-orbits of the critical circles of the level) by maps commuting with the restrictions to the
fixed parts, such that the induced maps to the products are bijective on K-Borel cohomology and
on the reflection Borel cohomology of the fixed parts, the half rotation acts trivially on the
fixed pieces, and every piece has a slope s with its reflection Borel groups within A of s·c₀
and those of its fixed piece in root degrees l with 2l within 2A of s·c₀ (`Pieces`). The
restriction of each piece to its fixed piece is bijective in high degrees, because the
restriction of the crossing is (`CrossLocalize`) and the splittings are bijective; it descends to
every degree above the reflection Borel groups of the piece (Gysin), and below them the K-Borel
groups of the piece vanish. In a degree q away from all lines s·c₀ every piece is either below
q, where its restriction is bijective and its fixed groups live in root degrees below q/2, or
above q, where its K-Borel groups vanish and its fixed groups live above q/2. Hence the total
normalized restriction of the crossing is injective with image the families of root degrees at
most q/2: the windowed localization follows from splittings of all single crossings
(`OrbitSplit`), and so do the local bounds of the events. The splittings themselves (K-invariant
neighbourhoods of the K-orbits of critical circles, a K-equivariant deformation, excision and
additivity, and the windows of the pieces from the labels) are not proved here. -/

@[expose] public section

namespace Finsler.OrbitAssembly

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelFixed Finsler.FixedLadder Finsler.CutPotential Finsler.AvoidPoint
open Finsler.BorelIterate Finsler.BorelCrossingK Finsler.GradedLadder Finsler.BorelExact
open Finsler.CriticalLevels Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelK Finsler.TotalExact Finsler.BorelCoverK Finsler.LocalCoverK
open Finsler.TrivialK Finsler.FixedGlobal Finsler.CrossLocalize Finsler.EventFar Finsler.EventSum
open Finsler.CriticalCircles Finsler.CrossingSlopes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- If the ordinary cohomology of a complex vanishes in all degrees at most q, so does its Borel
cohomology. -/
theorem HR_eq_zero_of_low (L : InvComplex) :
    ∀ q : ℕ, (∀ i, i ≤ q → ∀ z : H L i, z = 0) → ∀ x : HR L q, x = 0 := by
  intro q
  induction q with
  | zero =>
    intro h x
    apply Finsler.BorelQuasiIso.forget_zero_injective L
    rw [h 0 le_rfl (forget L 0 x), map_zero]
  | succ q ih =>
    intro h x
    obtain ⟨y, rfl⟩ := (exact_forget L q x).mp (h (q + 1) le_rfl _)
    rw [ih (fun i hi => h i (by omega)) y, map_zero]

/-! ### Joint bijectivity -/

section Joint

variable {K : InvComplex} {J : Type} {L : J → InvComplex} (φ : ∀ j, InvHom K (L j))
  (hbij : ∀ i, Function.Bijective (LinearMap.pi fun j => (φ j).f i))

/-- Gluing a family of total cochains of the targets to a total cochain of the source. -/
def glue (y : ∀ j, Seq (L j)) : Seq K :=
  fun i => (LinearEquiv.ofBijective _ (hbij i)).symm (fun j => y j i)

theorem seqMap_glue (y : ∀ j, Seq (L j)) (j : J) : seqMap (φ j) (glue φ hbij y) = y j := by
  funext i
  exact congrFun ((LinearEquiv.ofBijective _ (hbij i)).apply_symm_apply (fun j => y j i)) j

include hbij in
theorem seq_ext {c c' : Seq K} (h : ∀ j, seqMap (φ j) c = seqMap (φ j) c') : c = c' := by
  funext i
  apply (hbij i).1
  funext j
  exact congrFun (h j) i

include hbij in
theorem glue_mem_low {k : ℕ} (y : ∀ j, Seq (L j)) (hy : ∀ j, y j ∈ low (L j) k) :
    glue φ hbij y ∈ low K k := by
  intro i hi
  apply (hbij i).1
  funext j
  change (φ j).f i (glue φ hbij y i) = (φ j).f i 0
  rw [map_zero]
  exact (congrFun (seqMap_glue φ hbij y j) i).trans (hy j i hi)

include hbij in
/-- If maps of complexes are jointly bijective on cochains, they are jointly bijective on Borel
cohomology. -/
theorem HR_pi_bijective (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap (φ j) q) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hj : ∀ j, ∃ b ∈ low (L j) q, D (L j) b = seqMap (φ j) (c : Seq K) := by
      intro j
      have h : (Submodule.Quotient.mk (bcocycleMap (φ j) q c) : HR (L j) q) = 0 := congrFun hx j
      obtain ⟨b, hb, hbc⟩ := (mk_eq_zero_iff_bcoboundary (L j) q _).mp h
      exact ⟨b, hb, hbc⟩
    choose b hb hbc using hj
    rw [mk_eq_zero_iff_bcoboundary]
    refine ⟨glue φ hbij b, glue_mem_low φ hbij b hb, ?_⟩
    apply seq_ext φ hbij
    intro j
    rw [seqMap_D, seqMap_glue, hbc j]
  · intro y
    have hj : ∀ j, ∃ c : bcocycles (L j) q, Submodule.Quotient.mk c = y j :=
      fun j => Submodule.Quotient.mk_surjective _ (y j)
    choose c hc using hj
    have hg : glue φ hbij (fun j => (c j : Seq (L j))) ∈ bcocycles K q := by
      refine ⟨glue_mem_low φ hbij _ fun j => ((mem_bcocycles (L j)).mp (c j).2).1, ?_⟩
      change D K (glue φ hbij (fun j => (c j : Seq (L j)))) = 0
      apply seq_ext φ hbij
      intro j
      rw [seqMap_D, seqMap_glue, ((mem_bcocycles (L j)).mp (c j).2).2, map_zero]
    refine ⟨Submodule.Quotient.mk ⟨_, hg⟩, ?_⟩
    funext j
    rw [← hc j]
    change Submodule.Quotient.mk (bcocycleMap (φ j) q ⟨_, hg⟩) = _
    congr 1
    exact Subtype.ext (seqMap_glue φ hbij _ j)

end Joint

/-- If maps of commuting complexes are jointly bijective on cochains, so are the induced maps of
the iterated Borel complexes. -/
theorem borelHom_pi_bijective {K : InvComplex} {SK : Commuting K} {J : Type}
    {L : J → InvComplex} {SL : ∀ j, Commuting (L j)} (Φ : ∀ j, CommHom SK (SL j))
    (hbij : ∀ i, Function.Bijective (LinearMap.pi fun j => (Φ j).φ.f i)) (m : ℕ) :
    Function.Bijective (LinearMap.pi fun j => (borelHom (Φ j)).f m) := by
  constructor
  · intro x x' hxx
    apply Subtype.ext
    apply seq_ext (fun j => (Φ j).φ) hbij
    intro j
    exact congrArg Subtype.val (congrFun hxx j)
  · intro y
    refine ⟨⟨glue (fun j => (Φ j).φ) hbij (fun j => ((toLow (SL j) m (y j) : low (L j) (m + 1)) :
      Seq (L j))), glue_mem_low _ hbij _ fun j => (toLow (SL j) m (y j)).2⟩, ?_⟩
    funext j
    exact Subtype.ext (seqMap_glue (fun j => (Φ j).φ) hbij _ j)

/-- If maps of commuting complexes are jointly bijective on cochains, they are jointly bijective
on the Borel cohomology of the iterated complexes. -/
theorem HK_pi_bijective {K : InvComplex} {SK : Commuting K} {J : Type} {L : J → InvComplex}
    {SL : ∀ j, Commuting (L j)} (Φ : ∀ j, CommHom SK (SL j))
    (hbij : ∀ i, Function.Bijective (LinearMap.pi fun j => (Φ j).φ.f i)) (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap (borelHom (Φ j)) q) :=
  HR_pi_bijective (fun j => borelHom (Φ j)) (borelHom_pi_bijective Φ hbij) q

/-! ### Splittings of a crossing-like pair of complexes -/

section Abstract

variable {X Xh : InvComplex} {SX : Commuting X} {SXh : Commuting Xh} (R : CommHom SX SXh)

/-- A splitting of commuting complexes X, Xh with a restriction R into pieces with slopes in S and
windows of width A around the lines through c₀: maps to the pieces and fixed pieces commuting
with the restrictions, jointly bijective on the K-Borel cohomology of X and Xh and on the
reflection Borel cohomology of Xh; the half rotation acts trivially on the fixed pieces. -/
structure Split (c₀ A : ℝ) (S : Finset ℝ) where
  /-- the pieces -/
  J : Type
  slope : J → ℝ
  slope_mem : ∀ j, slope j ∈ S
  K : J → InvComplex
  SK : ∀ j, Commuting (K j)
  Kh : J → InvComplex
  SKh : ∀ j, Commuting (Kh j)
  triv : ∀ j i x, (SKh j).s i x = x
  /-- restriction of a piece to its fixed piece -/
  ρ : ∀ j, CommHom (SK j) (SKh j)
  /-- the maps to the pieces and to the fixed pieces -/
  r : ∀ j, CommHom SX (SK j)
  rh : ∀ j, CommHom SXh (SKh j)
  comm : ∀ j i x, (ρ j).φ.f i ((r j).φ.f i x) = (rh j).φ.f i (R.φ.f i x)
  bijK : ∀ q, Function.Bijective (LinearMap.pi fun j => HRmap (borelHom (r j)) q)
  bijKh : ∀ q, Function.Bijective (LinearMap.pi fun j => HRmap (borelHom (rh j)) q)
  bijR : ∀ l, Function.Bijective (LinearMap.pi fun j => HRmap (rh j).φ l)
  /-- the windows of the pieces -/
  win : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| → ∀ z : HR (K j) i, z = 0
  winh : ∀ j (l : ℕ), 2 * A < |2 * (l : ℝ) - slope j * c₀| → ∀ z : HR (Kh j) l, z = 0

variable {R} {c₀ A : ℝ} {S : Finset ℝ} (P : Split R c₀ A S)

/-- Restriction commutes with the maps to the pieces on K-Borel cohomology. -/
theorem res_piece (j : P.J) (q : ℕ) (x : HR (borelInv SX) q) :
    HRmap (borelHom (P.ρ j)) q (HRmap (borelHom (P.r j)) q x) =
      HRmap (borelHom (P.rh j)) q (HRmap (borelHom R) q x) :=
  HRmap_square _ _ _ _ (fun i z => borelHom_square _ _ _ _ (fun m y => P.comm j m y) i z) q x

/-- A family of classes of the pieces comes from a class of X. -/
theorem exists_of_pieces (q : ℕ) (y : ∀ j, HR (borelInv (P.SK j)) q) :
    ∃ x : HR (borelInv SX) q, ∀ j, HRmap (borelHom (P.r j)) q x = y j := by
  obtain ⟨x, hx⟩ := (P.bijK q).2 y
  exact ⟨x, fun j => congrFun hx j⟩

/-- A class of X vanishing on all pieces vanishes. -/
theorem eq_zero_of_pieces (q : ℕ) (x : HR (borelInv SX) q)
    (hx : ∀ j, HRmap (borelHom (P.r j)) q x = 0) : x = 0 :=
  (P.bijK q).1 ((funext hx).trans
    (map_zero (LinearMap.pi fun j => HRmap (borelHom (P.r j)) q)).symm)

/-- A class of Xh vanishing on all fixed pieces vanishes. -/
theorem eq_zero_of_fixPieces (q : ℕ) (x : HR (borelInv SXh) q)
    (hx : ∀ j, HRmap (borelHom (P.rh j)) q x = 0) : x = 0 :=
  (P.bijKh q).1 ((funext hx).trans
    (map_zero (LinearMap.pi fun j => HRmap (borelHom (P.rh j)) q)).symm)

/-- A reflection Borel class of Xh vanishing on all fixed pieces vanishes. -/
theorem eq_zero_of_fixR (l : ℕ) (y : HR Xh l) (hy : ∀ j, HRmap (P.rh j).φ l y = 0) : y = 0 :=
  (P.bijR l).1 ((funext hy).trans (map_zero (LinearMap.pi fun j => HRmap (P.rh j).φ l)).symm)

/-- If the restriction R is bijective in degree q, so is the restriction of every piece. -/
theorem piece_bijective (q : ℕ) (h : Function.Bijective (HRmap (borelHom R) q)) (j : P.J) :
    Function.Bijective (HRmap (borelHom (P.ρ j)) q) := by
  classical
  constructor
  · intro u v huv
    obtain ⟨x, hx⟩ := exists_of_pieces P q (Pi.single j (u - v))
    have h0 : HRmap (borelHom R) q x = 0 := by
      apply eq_zero_of_fixPieces P q
      intro k
      rw [← res_piece, hx k]
      by_cases hk : k = j
      · subst hk
        rw [Pi.single_eq_same, map_sub, huv, sub_self]
      · rw [Pi.single_eq_of_ne hk, map_zero]
    have hx0 : x = 0 := h.1 (h0.trans (map_zero _).symm)
    have := hx j
    rw [hx0, map_zero, Pi.single_eq_same] at this
    exact sub_eq_zero.mp this.symm
  · intro w
    obtain ⟨y, hy⟩ := (P.bijKh q).2 (Pi.single j w)
    obtain ⟨x, rfl⟩ := h.2 y
    refine ⟨HRmap (borelHom (P.r j)) q x, ?_⟩
    rw [res_piece]
    have := congrFun hy j
    simpa using this

include P in
/-- **Localization from a splitting.** If the restriction R is bijective in high degrees and the
half rotation acts trivially on Xh, then in every degree q farther than 2A + 1 from all lines
s·c₀ (s ∈ S) the family of components of the restriction to Xh is injective with image the
families of root degrees at most q/2. -/
theorem split_loc (hXh : ∀ i x, SXh.s i x = x) (hA : 0 ≤ A)
    (hQ : ∃ Q : ℕ, ∀ q, Q ≤ q → Function.Bijective (HRmap (borelHom R) q)) (q : ℕ)
    (hq : ∀ s ∈ S, 2 * A + 1 < |(q : ℝ) - s * c₀|) :
    Function.Injective (totMap (X := HR (borelInv SXh) q) (G := fun l => HR Xh l)
        (fun l => theta SXh hXh q l) ∘ₗ HRmap (borelHom R) q) ∧
      LinearMap.range (totMap (X := HR (borelInv SXh) q) (G := fun l => HR Xh l)
          (fun l => theta SXh hXh q l) ∘ₗ HRmap (borelHom R) q) =
        LinearMap.range (cut (fun l => HR Xh l) (q / 2)) := by
  classical
  obtain ⟨Q, hQ⟩ := hQ
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  -- every piece is below or above q
  have hside : ∀ j, P.slope j * c₀ + (2 * A + 1) < q ∨
      (q : ℝ) < P.slope j * c₀ - (2 * A + 1) := by
    intro j
    have h := hq (P.slope j) (P.slope_mem j)
    rcases le_or_gt (P.slope j * c₀) q with hle | hlt
    · left
      rw [abs_of_nonneg (by linarith)] at h
      linarith
    · right
      rw [abs_of_neg (by linarith)] at h
      linarith
  -- a piece above q has no K-Borel classes of degree q
  have F1 : ∀ j, (q : ℝ) < P.slope j * c₀ - (2 * A + 1) →
      ∀ x : HR (borelInv (P.SK j)) q, x = 0 := by
    intro j hj
    refine HR_eq_zero_of_low (borelInv (P.SK j)) q fun i hi z => ?_
    refine (LinearEquiv.map_eq_zero_iff (cohomologyEquiv (P.SK j) i)).mp (P.win j i ?_ _)
    have hi' : (i : ℝ) ≤ q := by exact_mod_cast hi
    rw [abs_of_neg (by linarith)]
    linarith
  -- a piece above q has no fixed classes of root degree at most q/2
  have F2 : ∀ j, (q : ℝ) < P.slope j * c₀ - (2 * A + 1) →
      ∀ l : ℕ, 2 * l ≤ q → ∀ z : HR (P.Kh j) l, z = 0 := by
    intro j hj l hl
    refine P.winh j l ?_
    have hl' : 2 * (l : ℝ) ≤ q := by exact_mod_cast hl
    rw [abs_of_neg (by linarith)]
    linarith
  -- a piece below q restricts bijectively in degree q
  have F3 : ∀ j, P.slope j * c₀ + (2 * A + 1) < q →
      Function.Bijective (HRmap (borelHom (P.ρ j)) q) := by
    intro j hj
    refine bijective_down (borelHom (P.ρ j)) (Q := Q)
      (fun p hp => piece_bijective P p (hQ p hp) j) (fun i hi z => ?_) (fun i hi z => ?_) q le_rfl
    · refine (LinearEquiv.map_eq_zero_iff (cohomologyEquiv (P.SK j) i)).mp (P.win j i ?_ _)
      have hi' : (q : ℝ) ≤ i := by exact_mod_cast hi
      rw [abs_of_nonneg (by linarith)]
      linarith
    · refine (LinearEquiv.map_eq_zero_iff (cohomologyEquiv (P.SKh j) i)).mp (P.winh j i ?_ _)
      have hi' : (q : ℝ) ≤ i := by exact_mod_cast hi
      rw [abs_of_nonneg (by linarith)]
      linarith
  -- a piece below q has no fixed classes of root degree above q/2
  have F4 : ∀ j, P.slope j * c₀ + (2 * A + 1) < q →
      ∀ l : ℕ, q < 2 * l → ∀ z : HR (P.Kh j) l, z = 0 := by
    intro j hj l hl
    refine P.winh j l ?_
    have hl' : (q : ℝ) < 2 * (l : ℝ) := by exact_mod_cast hl
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : HRmap (borelHom R) q x = 0 :=
      totTheta_injective _ hXh q (hx.trans (map_zero _).symm)
    apply eq_zero_of_pieces P q x
    intro j
    have h2 : HRmap (borelHom (P.ρ j)) q (HRmap (borelHom (P.r j)) q x) = 0 := by
      rw [res_piece]
      exact (congrArg (HRmap (borelHom (P.rh j)) q) h1).trans (map_zero _)
    rcases hside j with hb | ha
    · exact (F3 j hb).1 (h2.trans (map_zero _).symm)
    · exact F1 j ha _
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_range_cut]
      intro l hl
      apply eq_zero_of_fixR P l
      intro j
      change HRmap (P.rh j).φ l (theta SXh hXh q l (HRmap (borelHom R) q x)) = 0
      rw [← theta_natural hXh (P.triv j) (P.rh j) q l, ← res_piece]
      rcases hside j with hb | ha
      · exact F4 j hb l (by omega) _
      · rw [F1 j ha (HRmap (borelHom (P.r j)) q x), map_zero, map_zero]
    · intro hy
      rw [mem_range_cut] at hy
      have hpick : ∀ j, ∃ xj : HR (borelInv (P.SK j)) q, ∀ l,
          theta (P.SKh j) (P.triv j) q l (HRmap (borelHom (P.ρ j)) q xj) =
            HRmap (P.rh j).φ l (y l) := by
        intro j
        rcases hside j with hb | ha
        · have hz : (fun l => HRmap (P.rh j).φ l (y l)) ∈
              LinearMap.range (cut (fun l => HR (P.Kh j) l) q) := by
            rw [mem_range_cut]
            intro l hl
            change HRmap (P.rh j).φ l (y l) = 0
            rw [hy l (by omega), map_zero]
          rw [← range_totTheta (P.SKh j) (P.triv j) q] at hz
          obtain ⟨w, hw⟩ := hz
          obtain ⟨xj, rfl⟩ := (F3 j hb).2 w
          exact ⟨xj, fun l => congrFun hw l⟩
        · refine ⟨0, fun l => ?_⟩
          rw [map_zero, map_zero]
          by_cases hl : 2 * l ≤ q
          · exact (F2 j ha l hl _).symm
          · rw [hy l (by omega), map_zero]
      choose xs hxs using hpick
      obtain ⟨x, hx⟩ := exists_of_pieces P q xs
      refine ⟨x, ?_⟩
      funext l
      apply (P.bijR l).1
      funext j
      change HRmap (P.rh j).φ l (theta SXh hXh q l (HRmap (borelHom R) q x)) =
        HRmap (P.rh j).φ l (y l)
      rw [← theta_natural hXh (P.triv j) (P.rh j) q l, ← res_piece, hx j]
      exact hxs j l

end Abstract

/-! ### Single crossings -/

variable (F : ReversibleMetric n)

/-- The two commuting involutions on the cochains of the crossing pair (t_b, t_a). -/
abbrev crossS {a b : ℝ} (hab : a ≤ b) := kCommuting (lev_mono F hab) (kInv_lev F a) (kInv_lev F b)

/-- The two commuting involutions on the cochains of the fixed crossing pair. -/
abbrev fixS {a b : ℝ} (hab : a ≤ b) :=
  kCommuting (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b)

/-- Restriction from the crossing pair to the fixed crossing pair. -/
abbrev crossHom {a b : ℝ} (hab : a ≤ b) : CommHom (crossS F hab) (fixS F hab) :=
  kHom (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b) (lev_mono F hab)
    (kInv_lev F a) (kInv_lev F b) (fixLev_subset_lev F a) (fixLev_subset_lev F b)

/-- A splitting of a single crossing: commuting complexes M, Mh with a restriction, mapping to the
crossing pair and to the fixed crossing pair by maps commuting with the restrictions and bijective
on K-Borel cohomology and on the reflection Borel cohomology of the fixed parts (for instance the
cochains of (t_b, Y) for a lens), together with a splitting of M, Mh into pieces with slopes in S
and windows of width A around the lines through c₀. -/
structure Pieces {a b : ℝ} (hab : a ≤ b) (c₀ A : ℝ) (S : Finset ℝ) where
  M : InvComplex
  SM : Commuting M
  Mh : InvComplex
  SMh : Commuting Mh
  trivh : ∀ i x, SMh.s i x = x
  ρM : CommHom SM SMh
  ι : CommHom SM (crossS F hab)
  ιh : CommHom SMh (fixS F hab)
  commι : ∀ i x, (crossHom F hab).φ.f i (ι.φ.f i x) = ιh.φ.f i (ρM.φ.f i x)
  bijι : ∀ q, Function.Bijective (HRmap (borelHom ι) q)
  bijιh : ∀ q, Function.Bijective (HRmap (borelHom ιh) q)
  bijιR : ∀ l, Function.Bijective (HRmap ιh.φ l)
  split : Split ρM c₀ A S

/-- Splittings of all single crossings into pieces with slopes in S and windows of width A. -/
structure OrbitSplit where
  S : Finset ℝ
  A : ℝ
  A_nonneg : 0 ≤ A
  split : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
    Nonempty (Pieces F hab c₀ A S)

section Transport

variable {F} {a b : ℝ} {hab : a ≤ b} {c₀ A : ℝ} {S : Finset ℝ} (P : Pieces F hab c₀ A S)

/-- The maps to the crossing commute with the restrictions on K-Borel cohomology. -/
theorem res_ι (q : ℕ) (x : HR (borelInv P.SM) q) :
    crossRes F hab q (HRmap (borelHom P.ι) q x) =
      HRmap (borelHom P.ιh) q (HRmap (borelHom P.ρM) q x) :=
  HRmap_square _ _ _ _ (fun i z => borelHom_square _ _ _ _ (fun m y => P.commι m y) i z) q x

/-- Bijectivity of restriction passes from the crossing to M. -/
theorem anchor_M (q : ℕ) (h : Function.Bijective (crossRes F hab q)) :
    Function.Bijective (HRmap (borelHom P.ρM) q) := by
  constructor
  · intro x y hxy
    apply (P.bijι q).1
    apply h.1
    rw [res_ι, res_ι, hxy]
  · intro z
    obtain ⟨w, hw⟩ := h.2 (HRmap (borelHom P.ιh) q z)
    obtain ⟨x, rfl⟩ := (P.bijι q).2 w
    refine ⟨x, (P.bijιh q).1 ?_⟩
    rw [← res_ι, hw]

/-- The total normalized restriction of the crossing on classes coming from M. -/
theorem crossEps_ι (q : ℕ) (x : HR (borelInv P.SM) q) (l : ℕ) :
    crossEps F hab q (HRmap (borelHom P.ι) q x) l =
      HRmap P.ιh.φ l (theta P.SMh P.trivh q l (HRmap (borelHom P.ρM) q x)) := by
  rw [crossEps_eq]
  change theta (fixS F hab) (kCommuting_trivial (fixLev_mono F hab) (kInv_fixLev F a)
      (kInv_fixLev F b) (half_fixLev F b)) q l (crossRes F hab q (HRmap (borelHom P.ι) q x)) = _
  rw [res_ι, theta_natural P.trivh]

include P in
/-- **Localization of a single crossing from a splitting.** If restriction from the crossing to
the fixed crossing is bijective in high degrees, then in every degree q farther than 2A + 1 from
all lines s·c₀ (s ∈ S) the total normalized restriction of the K-Borel crossing group is
injective with image the families of root degrees at most q/2. -/
theorem loc_of_pieces (hA : 0 ≤ A)
    (hQ : ∃ Q : ℕ, ∀ q, Q ≤ q → Function.Bijective (crossRes F hab q)) (q : ℕ)
    (hq : ∀ s ∈ S, 2 * A + 1 < |(q : ℝ) - s * c₀|) :
    Function.Injective (crossEps F hab q) ∧
      LinearMap.range (crossEps F hab q) = LinearMap.range (cut (crossR F hab) (q / 2)) := by
  obtain ⟨Q, hQ⟩ := hQ
  obtain ⟨hinj, hrange⟩ := split_loc P.split P.trivh hA
    ⟨Q, fun p hp => anchor_M P p (hQ p hp)⟩ q hq
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := (P.bijι q).2 y
    have hx : x = 0 := by
      apply hinj
      rw [map_zero]
      funext l
      apply (P.bijιR l).1
      change HRmap P.ιh.φ l (theta P.SMh P.trivh q l (HRmap (borelHom P.ρM) q x)) =
        HRmap P.ιh.φ l 0
      rw [map_zero, ← crossEps_ι]
      exact congrFun hy l
    rw [hx, map_zero]
  · ext y
    constructor
    · rintro ⟨y', rfl⟩
      obtain ⟨x, rfl⟩ := (P.bijι q).2 y'
      rw [mem_range_cut]
      intro l hl
      rw [crossEps_ι]
      have hm : (totMap (X := HR (borelInv P.SMh) q) (G := fun l => HR P.Mh l)
          (fun l => theta P.SMh P.trivh q l) ∘ₗ HRmap (borelHom P.ρM) q) x ∈
          LinearMap.range (cut (fun l => HR P.Mh l) (q / 2)) := by
        rw [← hrange]
        exact ⟨x, rfl⟩
      rw [mem_range_cut] at hm
      have := hm l hl
      change theta P.SMh P.trivh q l (HRmap (borelHom P.ρM) q x) = 0 at this
      rw [this, map_zero]
    · intro hy
      rw [mem_range_cut] at hy
      have hz : (fun l => (LinearEquiv.ofBijective _ (P.bijιR l)).symm (y l)) ∈
          LinearMap.range (cut (fun l => HR P.Mh l) (q / 2)) := by
        rw [mem_range_cut]
        intro l hl
        change (LinearEquiv.ofBijective _ (P.bijιR l)).symm (y l) = 0
        exact (LinearEquiv.map_eq_zero_iff _).mpr (hy l hl)
      rw [← hrange] at hz
      obtain ⟨x, hx⟩ := hz
      refine ⟨HRmap (borelHom P.ι) q x, funext fun l => ?_⟩
      rw [crossEps_ι]
      have := congrFun hx l
      change theta P.SMh P.trivh q l (HRmap (borelHom P.ρM) q x) =
        (LinearEquiv.ofBijective _ (P.bijιR l)).symm (y l) at this
      rw [this]
      exact (LinearEquiv.ofBijective _ (P.bijιR l)).apply_symm_apply (y l)

end Transport

/-- **Localization of single crossings from splittings into pieces.** With finitely many prime
closed geodesic images and splittings of all single crossings into pieces with slopes S and
windows of width A, in every degree q farther than 2A + 1 from all lines s·c₀ (s ∈ S) the total
normalized restriction of the K-Borel crossing group is injective with image the families of root
degrees at most q/2. -/
theorem loc_of_split (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (O : OrbitSplit F) :
    ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
      (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
      ∀ q : ℕ, (∀ s ∈ O.S, 2 * O.A + 1 < |(q : ℝ) - s * c₀|) →
        Function.Injective (crossEps F hab q) ∧
          LinearMap.range (crossEps F hab q) = LinearMap.range (cut (crossR F hab) (q / 2)) := by
  intro a b hab2 ha h2a h2b hsub c₀ hc₀ q hq
  obtain ⟨P⟩ := O.split a b hab2 ha h2a h2b hsub c₀ hc₀
  exact loc_of_pieces P O.A_nonneg (exists_crossRes_bijective F hn hfin ha hab2 h2a h2b) q hq

/-- Splittings of all single crossings into pieces give the windowed localization. -/
theorem windowLoc_of_split (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (O : OrbitSplit F) :
    Nonempty (WindowLoc F) :=
  ⟨⟨O.S, 2 * O.A + 1, loc_of_split F hn hfin O⟩⟩

/-- With the slopes of the pieces among the slopes of the labels and zero, splittings of all
single crossings give the windowed localization below the lines. -/
theorem gapLoc_of_split (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (O : OrbitSplit F)
    (hS : O.S ⊆ insert (0 : ℝ) ((labels F hfin).image (slope F))) :
    Nonempty (GapLoc F hfin) :=
  ⟨⟨2 * O.A + 1, fun a b hab ha h2a h2b hsub c₀ hc₀ q hq _ =>
    loc_of_split F hn hfin O a b hab ha h2a h2b hsub c₀ hc₀ q fun s hs => hq s (hS hs)⟩⟩

/-- **The local bounds of the events from splittings of single crossings into pieces.** -/
theorem nonempty_eventBounds_of_split (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (O : OrbitSplit F) : Nonempty (EventBounds F) := by
  obtain ⟨L⟩ := windowLoc_of_split F hn hfin O
  exact nonempty_eventBounds_of_loc F hn hfin L

end

end Finsler.OrbitAssembly
