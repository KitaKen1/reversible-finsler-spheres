module

public import Finsler.Topology.FiltrationCollapse
public import Finsler.Topology.BorelGraded

/-! From the collapsed filtration to the global reflection Borel cohomology.

A global filtration adds to a filtration (`FiltrationCollapse.Filtration`) the involutive complex
G of the whole pair (Λ, M), the tails T_m (the pairs (Λ, Z_m)), short exact sequences
0 → T_m → G → Z_m → 0, compatible restrictions ρ_m : G → Z_m, the vanishing of the ordinary
cohomology of T_m below the lowest degree l_m of the next crossing, and the evaluation operators
e of degree d + 1 on G, Z_m and P_j, compatible with restriction and with the inclusions of the
crossings, such that the second start class of every crossing is e times the first.

Then (stage A):

* the Borel cohomology of T_m vanishes below l_m, so restriction ρ_m is injective below l_m and
  surjective below l_m − 1;
* every crossing class τ_j has a global extension X_j;
* the special connecting map of `FiltrationCollapse` vanishes: a Borel class of Z_{j+1} of degree
  l_j + d + 1 is a multiple of the image of σ_j = e τ_j, hence the restriction of the global
  class e X_j, and the connecting map kills restrictions of classes of Z_{j+2};
* hence all crossing sequences collapse, and restriction ρ_m is surjective in every degree (it is
  ρ_M followed by the surjections Z_M → Z_m, and ρ_M is surjective in a given degree for large M).
-/

@[expose] public section

namespace Finsler.GlobalBasis

open Finsler.BorelCochain Finsler.BorelExact Finsler.CrossingCollapse Finsler.GysinPattern
open Finsler.FiltrationCollapse Finsler.BorelGraded Module

noncomputable section

/-! ### Degree casts -/

section Cast

variable {K L : InvComplex}

theorem castHR_self {a : ℕ} (h : a = a) (x : HR K a) : castHR h x = x := rfl

theorem castHR_castHR {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : HR K a) :
    castHR h₂ (castHR h₁ x) = castHR (h₁.trans h₂) x := by
  subst h₁
  subst h₂
  rfl

theorem HRmap_castHR (φ : InvHom K L) {a b : ℕ} (h : a = b) (x : HR K a) :
    HRmap φ b (castHR h x) = castHR h (HRmap φ a x) := by
  subst h
  rfl

theorem castHR_injective {a b : ℕ} (h : a = b) : Function.Injective (castHR (L := K) h) := by
  subst h
  exact Function.injective_id

theorem castHR_eq_zero {a b : ℕ} (h : a = b) {x : HR K a} : castHR h x = 0 ↔ x = 0 := by
  subst h
  rfl

theorem w_castHR {a b : ℕ} (h : a = b) (x : HR K a) :
    w K b (castHR h x) = castHR (congrArg (· + 1) h) (w K a x) := by
  subst h
  rfl

theorem wPow_map_add (lo : ℕ) : ∀ (k : ℕ) (x y : HR K lo),
    NilpotentW.wPow K lo k (x + y) = NilpotentW.wPow K lo k x + NilpotentW.wPow K lo k y
  | 0, _, _ => rfl
  | k + 1, x, y => by
    rw [NilpotentW.wPow_succ, NilpotentW.wPow_succ, NilpotentW.wPow_succ, wPow_map_add lo k,
      map_add]

theorem wPow_map_smul (lo : ℕ) : ∀ (k : ℕ) (c : ZMod 2) (x : HR K lo),
    NilpotentW.wPow K lo k (c • x) = c • NilpotentW.wPow K lo k x
  | 0, _, _ => rfl
  | k + 1, c, x => by
    rw [NilpotentW.wPow_succ, NilpotentW.wPow_succ, wPow_map_smul lo k, map_smul]

theorem wPow_map_zero (lo k : ℕ) : NilpotentW.wPow K lo k 0 = 0 := by
  have := wPow_map_smul lo k 0 (0 : HR K lo)
  rwa [zero_smul, zero_smul] at this

theorem wPow_castHR {a b : ℕ} (h : a = b) (x : HR K a) (k : ℕ) :
    NilpotentW.wPow K b k (castHR h x) = castHR (congrArg (· + k) h) (NilpotentW.wPow K a k x) := by
  subst h
  rfl

theorem wPow_wPow (lo k : ℕ) (x : HR K lo) : ∀ k' : ℕ,
    NilpotentW.wPow K (lo + k) k' (NilpotentW.wPow K lo k x) =
      castHR (Nat.add_assoc lo k k').symm (NilpotentW.wPow K lo (k + k') x)
  | 0 => rfl
  | k' + 1 => by
    rw [NilpotentW.wPow_succ, wPow_wPow lo k x k', w_castHR]
    rfl

/-- Casting a family along an equality of degrees. -/
theorem castHR_family {f : ∀ q, HR K q} {a b : ℕ} (h : a = b) : castHR h (f a) = f b := by
  subst h
  rfl

end Cast

/-- A global filtration. -/
structure RGlobal (d : ℕ) extends Filtration d where
  G : InvComplex
  T : ℕ → InvComplex
  κ : ∀ m, InvHom (T m) G
  ρ : ∀ m, InvHom G (Z m)
  exactT : ∀ m, ShortExact (κ m) (ρ m)
  tail : ∀ m q, q < l m → ∀ z : H (T m) q, z = 0
  ρ_π : ∀ m q (x : HR G q), HRmap (π m) q (HRmap (ρ (m + 1)) q x) = HRmap (ρ m) q x
  E : ∀ q, HR G q →ₗ[ZMod 2] HR G (d + 1 + q)
  EZ : ∀ m q, HR (Z m) q →ₗ[ZMod 2] HR (Z m) (d + 1 + q)
  EP : ∀ j q, HR (P j) q →ₗ[ZMod 2] HR (P j) (d + 1 + q)
  E_ρ : ∀ m q x, HRmap (ρ m) (d + 1 + q) (E q x) = EZ m q (HRmap (ρ m) q x)
  E_ι : ∀ j q x, HRmap (ι j) (d + 1 + q) (EP j q x) = EZ (j + 1) q (HRmap (ι j) q x)
  E_w : ∀ q x, castHR (Nat.add_assoc (d + 1) q 1).symm (E (q + 1) (w G q x)) =
    w G (d + 1 + q) (E q x)
  σ_eq : ∀ j, castHR (by omega) (EP j (l j) (pattern j).τ) = (pattern j).σ

variable {d : ℕ} (R : RGlobal d)

namespace RGlobal

/-- The Borel cohomology of the tails vanishes below the next crossing. -/
theorem HR_T_zero (m q : ℕ) (hq : q < R.l m) (x : HR (R.T m) q) : x = 0 :=
  HR_zero_below (fun q' hq' => R.tail m q' hq') q hq x

/-- Restriction to Z_m is injective below the lowest degree of the next crossing. -/
theorem ρ_injective_low (m q : ℕ) (hq : q < R.l m) : Function.Injective (HRmap (R.ρ m) q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := exact_mid (R.exactT m) q x hx
  rw [R.HR_T_zero m q hq z, map_zero]

/-- Restriction to Z_m is surjective two degrees below the next crossing. -/
theorem ρ_surjective_low (m q : ℕ) (hq : q + 1 < R.l m) :
    Function.Surjective (HRmap (R.ρ m) q) := fun x =>
  exact_delta (R.exactT m) q x (R.HR_T_zero m (q + 1) hq _)

/-- The Borel cohomology of Z_j vanishes above the crossings below j. -/
theorem HR_Z_above : ∀ (j q : ℕ), (∀ i, i < j → R.l i + d + 1 + d < q) →
    ∀ y : HR (R.Z j) q, y = 0 := by
  intro j
  induction j with
  | zero =>
    intro q _ y
    exact HR_zero_below (l := q + 1) (fun q' _ => R.zero q') q (by omega) y
  | succ j ih =>
    intro q hq y
    obtain ⟨z, rfl⟩ := exact_mid (R.exact j) q y
      (ih q (fun i hi => hq i (by omega)) _)
    rw [(R.pattern j).HR_above q (hq j (Nat.lt_succ_self j)) z, map_zero]

theorem l_step (j : ℕ) : R.l (j + 1) = R.l j + 2 * d := R.l_succ j

/-- The global extension of the bottom class of the crossing j. -/
def X (j : ℕ) : HR R.G (R.l j) :=
  Classical.choose (R.ρ_surjective_low (j + 1) (R.l j)
    (by have := R.l_succ j; have := R.two_le; omega) (HRmap (R.ι j) (R.l j) (R.pattern j).τ))

theorem ρ_X (j : ℕ) : HRmap (R.ρ (j + 1)) (R.l j) (R.X j) = HRmap (R.ι j) (R.l j) (R.pattern j).τ :=
  Classical.choose_spec (R.ρ_surjective_low (j + 1) (R.l j)
    (by have := R.l_succ j; have := R.two_le; omega) (HRmap (R.ι j) (R.l j) (R.pattern j).τ))

/-- The restriction of the global class X_j to the stage j vanishes. -/
theorem ρ_X_below (j : ℕ) : HRmap (R.ρ j) (R.l j) (R.X j) = 0 := by
  rw [← R.ρ_π j, R.ρ_X, comp_zero (R.exact j)]

/-- The restriction of e X_j to Z_{j+1} is the image of σ_j. -/
theorem ρ_EX (j : ℕ) :
    castHR (by omega) (HRmap (R.ρ (j + 1)) (d + 1 + R.l j) (R.E (R.l j) (R.X j))) =
      HRmap (R.ι j) (R.l j + d + 1) (R.pattern j).σ := by
  rw [R.E_ρ, R.ρ_X, ← R.E_ι, ← R.σ_eq, HRmap_castHR]

/-- The special connecting maps vanish. -/
theorem specialAt (m : ℕ) : SpecialAt R.toFiltration m := by
  intro j hj y
  subst hj
  have hd := R.two_le
  -- y comes from the crossing j
  have hπ : HRmap (R.π j) (R.l j + d + 1) y = 0 := by
    apply R.HR_Z_above j
    intro i hi
    have := R.l_le_of_lt hi
    omega
  obtain ⟨z, rfl⟩ := exact_mid (R.exact j) _ y hπ
  obtain ⟨c, rfl⟩ := (R.pattern j).span_σ z
  -- the image of σ_j is the restriction of a global class
  have hglob : HRmap (R.ι j) (R.l j + d + 1) (R.pattern j).σ =
      HRmap (R.ρ (j + 1)) (R.l j + d + 1) (castHR (by omega) (R.E (R.l j) (R.X j))) := by
    rw [HRmap_castHR, R.ρ_EX]
  rw [map_smul, map_smul, map_smul, hglob, ← R.ρ_π, ← forget_delta, delta_comp_zero, map_zero,
    smul_zero]

/-- All stages of the filtration are good. -/
theorem good (m : ℕ) : Good R.toFiltration m :=
  FiltrationCollapse.good R.toFiltration R.specialAt m

/-- The Borel crossing sequences collapse. -/
theorem delta_zero (m q : ℕ) (x : HR (R.Z m) q) : delta (R.exact m) q x = 0 :=
  FiltrationCollapse.delta_eq_zero R.toFiltration R.specialAt m q x

/-- The ordinary crossing sequences collapse. -/
theorem delta_ord_zero (m q : ℕ) (x : H (R.Z m) q) : OrdinaryDelta.delta (R.exact m) q x = 0 :=
  FiltrationCollapse.delta_ord_eq_zero R.toFiltration R.specialAt m q x

theorem π_surjective (m q : ℕ) : Function.Surjective (HRmap (R.π m) q) :=
  surjective_of_delta (R.delta_zero m) q

theorem ι_injective (m q : ℕ) : Function.Injective (HRmap (R.ι m) q) :=
  injective_of_delta (R.delta_zero m) q

theorem l_ge (m : ℕ) : 2 * d * m ≤ R.l m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [R.l_succ]
    rw [Nat.mul_succ]
    omega

/-- Restriction to Z_m is surjective in every degree. -/
theorem ρ_surjective (m q : ℕ) : Function.Surjective (HRmap (R.ρ m) q) := by
  have hd := R.two_le
  -- surjectivity at a large stage, then descend
  have hdesc : ∀ k, Function.Surjective (HRmap (R.ρ (m + k)) q) →
      Function.Surjective (HRmap (R.ρ m) q) := by
    intro k
    induction k with
    | zero => exact id
    | succ k ih =>
      intro hs
      apply ih
      intro x
      obtain ⟨x', rfl⟩ := R.π_surjective (m + k) q x
      obtain ⟨y, rfl⟩ := hs x'
      exact ⟨y, (R.ρ_π (m + k) q y).symm⟩
  apply hdesc (q + 1)
  apply R.ρ_surjective_low
  have := R.l_ge (m + (q + 1))
  have h2 : 2 * (m + (q + 1)) ≤ 2 * d * (m + (q + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ### Bottom and top classes -/

/-- The bottom tower of the stage j. -/
def B (j k : ℕ) : HR R.G (R.l j + k) := NilpotentW.wPow R.G (R.l j) k (R.X j)

/-- The top tower of the stage j. -/
def Tw (j k : ℕ) : HR R.G (d + 1 + R.l j + k) :=
  NilpotentW.wPow R.G (d + 1 + R.l j) k (R.E (R.l j) (R.X j))

theorem ρ_B (j k : ℕ) : HRmap (R.ρ (j + 1)) (R.l j + k) (R.B j k) =
    HRmap (R.ι j) (R.l j + k) (NilpotentW.wPow (R.P j) (R.l j) k (R.pattern j).τ) := by
  rw [B, NilpotentW.HRmap_wPow, R.ρ_X, ← NilpotentW.HRmap_wPow]

theorem B_ne (j k : ℕ) (hk : k ≤ d) : R.B j k ≠ 0 := by
  intro h0
  have h1 := R.ρ_B j k
  rw [h0, map_zero] at h1
  exact (R.pattern j).bottom_ne k hk (R.ι_injective j _ (by rw [← h1, map_zero]))

theorem B_vanish (j : ℕ) : R.B j (d + 1) = 0 := by
  have hd := R.two_le
  apply R.ρ_injective_low (j + 1) _ (by have := R.l_succ j; omega)
  rw [R.ρ_B, (R.pattern j).bottom_vanish, map_zero, map_zero]

theorem B_vanish_of_le (j k : ℕ) (hk : d + 1 ≤ k) : R.B j k = 0 :=
  wPow_zero_of_le (R.B_vanish j) hk

/-- The evaluation operator commutes with the powers of w. -/
theorem E_wPow (q : ℕ) (x : HR R.G q) : ∀ k : ℕ,
    castHR (Nat.add_assoc (d + 1) q k).symm (R.E (q + k) (NilpotentW.wPow R.G q k x)) =
      NilpotentW.wPow R.G (d + 1 + q) k (R.E q x)
  | 0 => rfl
  | k + 1 => by
    rw [NilpotentW.wPow_succ, NilpotentW.wPow_succ, ← E_wPow q x k, w_castHR, ← R.E_w,
      castHR_castHR]
    rfl

theorem Tw_eq (j k : ℕ) : R.Tw j k = castHR (Nat.add_assoc (d + 1) (R.l j) k).symm
    (R.E (R.l j + k) (R.B j k)) := by
  rw [Tw, ← E_wPow]
  rfl

theorem Tw_vanish_of_le (j k : ℕ) (hk : d + 1 ≤ k) : R.Tw j k = 0 := by
  rw [Tw_eq, R.B_vanish_of_le j k hk, map_zero, map_zero]

theorem ρ_Tw (j k : ℕ) : castHR (by omega)
    (HRmap (R.ρ (j + 1)) (d + 1 + R.l j + k) (R.Tw j k)) =
    HRmap (R.ι j) (R.l j + d + 1 + k)
      (NilpotentW.wPow (R.P j) (R.l j + d + 1) k (R.pattern j).σ) := by
  rw [Tw, NilpotentW.HRmap_wPow, R.E_ρ, R.ρ_X, ← R.E_ι, ← R.σ_eq, wPow_castHR,
    ← NilpotentW.HRmap_wPow, HRmap_castHR]

theorem Tw_ne (j k : ℕ) (hk : k ≤ d) : R.Tw j k ≠ 0 := by
  intro h0
  have h1 := R.ρ_Tw j k
  rw [h0, map_zero, map_zero] at h1
  exact (R.pattern j).top_ne k hk (R.ι_injective j _ (by rw [← h1, map_zero]))

/-- The bottom degrees of the stage j. -/
abbrev IsBot (j q : ℕ) : Prop := R.l j ≤ q ∧ q ≤ R.l j + d

theorem isBot_unique {j j' q : ℕ} (h : R.IsBot j q) (h' : R.IsBot j' q) : j = j' := by
  have hd := R.two_le
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := R.l_le_of_lt hlt
    exact absurd h'.1 (by unfold IsBot at h; omega)
  · have := R.l_le_of_lt hlt
    exact absurd h.1 (by unfold IsBot at h'; omega)

open Classical in
/-- The bottom class of degree q, zero if there is none. -/
def bot (q : ℕ) : HR R.G q :=
  if h : ∃ j, R.IsBot j q then
    castHR (Nat.add_sub_cancel' (Classical.choose_spec h).1)
      (R.B (Classical.choose h) (q - R.l (Classical.choose h)))
  else 0

theorem bot_of {j q : ℕ} (hj : R.IsBot j q) :
    R.bot q = castHR (Nat.add_sub_cancel' hj.1) (R.B j (q - R.l j)) := by
  have h : ∃ j, R.IsBot j q := ⟨j, hj⟩
  rw [bot, dif_pos h]
  have key : ∀ J, J = j → ∀ (h1 : R.l J + (q - R.l J) = q) (h2 : R.l j + (q - R.l j) = q),
      castHR h1 (R.B J (q - R.l J)) = castHR h2 (R.B j (q - R.l j)) := by
    intro J hJ h1 h2
    subst hJ
    rfl
  exact key _ (R.isBot_unique (Classical.choose_spec h) hj) _ _

theorem bot_eq (j k : ℕ) (hk : k ≤ d) : R.bot (R.l j + k) = R.B j k := by
  rw [R.bot_of (j := j) ⟨by omega, by omega⟩]
  have key : ∀ k', k' = k → ∀ h : R.l j + k' = R.l j + k, castHR h (R.B j k') = R.B j k := by
    intro k' hk' h
    subst hk'
    rfl
  exact key _ (by omega) _

theorem bot_zero {q : ℕ} (h : ¬ ∃ j, R.IsBot j q) : R.bot q = 0 := by
  rw [bot, dif_neg h]

open Classical in
/-- The top class of degree q: e times the bottom class of degree q - (d + 1). -/
def top (q : ℕ) : HR R.G q :=
  if h : d + 1 ≤ q then castHR (Nat.add_sub_cancel' h) (R.E (q - (d + 1)) (R.bot (q - (d + 1))))
  else 0

/-- The tops are e times the bottoms. -/
theorem top_eq (q : ℕ) : R.top (d + 1 + q) = R.E q (R.bot q) := by
  rw [top, dif_pos (by omega)]
  have key : ∀ a, a = q → ∀ h : d + 1 + a = d + 1 + q, castHR h (R.E a (R.bot a)) =
      R.E q (R.bot q) := by
    intro a ha h
    subst ha
    rfl
  exact key _ (by omega) _

theorem top_eq_Tw (j k : ℕ) (hk : k ≤ d) :
    R.top (d + 1 + R.l j + k) = castHR (by omega) (R.Tw j k) := by
  rw [← castHR_family (f := R.top) (show d + 1 + (R.l j + k) = d + 1 + R.l j + k by omega),
    top_eq, bot_eq _ j k hk, Tw_eq, castHR_castHR]

/-- The bottom classes of the stages are nonzero. -/
theorem bot_ne (j : ℕ) : R.bot (R.l j) ≠ 0 := by
  rw [show R.l j = R.l j + 0 from rfl, R.bot_eq j 0 (Nat.zero_le d)]
  exact R.B_ne j 0 (Nat.zero_le d)

/-! ### Spanning -/

/-- Restricted to Z_M, every class is a combination of the restricted bottom and top classes. -/
theorem span_stage : ∀ (M q : ℕ) (y : HR (R.Z M) q), ∃ c c' : ZMod 2,
    y = c • HRmap (R.ρ M) q (R.bot q) + c' • HRmap (R.ρ M) q (R.top q) := by
  intro M
  induction M with
  | zero =>
    intro q y
    refine ⟨0, 0, ?_⟩
    rw [zero_smul, zero_smul, add_zero]
    exact HR_zero_below (l := q + 1) (fun q' _ => R.zero q') q (by omega) y
  | succ M ih =>
    intro q y
    have hd := R.two_le
    obtain ⟨c, c', hcc⟩ := ih q (HRmap (R.π M) q y)
    have hz : HRmap (R.π M) q (y - c • HRmap (R.ρ (M + 1)) q (R.bot q) -
        c' • HRmap (R.ρ (M + 1)) q (R.top q)) = 0 := by
      rw [map_sub, map_sub, map_smul, map_smul, R.ρ_π, R.ρ_π, hcc]
      abel
    obtain ⟨z, hz'⟩ := exact_mid (R.exact M) q _ hz
    -- the class z of the crossing M is a multiple of a bottom or a top class, or zero
    have hzc : ∃ a b : ZMod 2, HRmap (R.ι M) q z =
        a • HRmap (R.ρ (M + 1)) q (R.bot q) + b • HRmap (R.ρ (M + 1)) q (R.top q) := by
      by_cases hb : R.l M ≤ q ∧ q ≤ R.l M + d
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb.1
        obtain ⟨a, rfl⟩ := (R.pattern M).span_bottom k (by omega) z
        refine ⟨a, 0, ?_⟩
        rw [zero_smul, add_zero, R.bot_eq M k (by omega), R.ρ_B, map_smul]
      · by_cases ht : R.l M + d + 1 ≤ q ∧ q ≤ R.l M + d + 1 + d
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht.1
          obtain ⟨b, rfl⟩ := (R.pattern M).span_top k (by omega) z
          refine ⟨0, b, ?_⟩
          rw [zero_smul, zero_add, map_smul]
          congr 1
          rw [← R.ρ_Tw M k]
          have h2 : R.top (R.l M + d + 1 + k) =
              castHR (by omega : d + 1 + R.l M + k = R.l M + d + 1 + k) (R.Tw M k) := by
            rw [← castHR_family (f := R.top)
              (show d + 1 + R.l M + k = R.l M + d + 1 + k by omega),
              R.top_eq_Tw M k (by omega), castHR_castHR]
          rw [h2, HRmap_castHR]
        · have hq : q < R.l M ∨ R.l M + d + 1 + d < q := by omega
          refine ⟨0, 0, ?_⟩
          rw [zero_smul, zero_smul, add_zero]
          rcases hq with hq | hq
          · rw [(R.pattern M).HR_below q hq z, map_zero]
          · rw [(R.pattern M).HR_above q hq z, map_zero]
    obtain ⟨a, b, hab⟩ := hzc
    refine ⟨c + a, c' + b, ?_⟩
    rw [add_smul, add_smul]
    have : y = (y - c • HRmap (R.ρ (M + 1)) q (R.bot q) - c' • HRmap (R.ρ (M + 1)) q (R.top q)) +
        c • HRmap (R.ρ (M + 1)) q (R.bot q) + c' • HRmap (R.ρ (M + 1)) q (R.top q) := by abel
    rw [this, ← hz', hab]
    abel

/-- Every global class is a combination of the bottom and the top class of its degree. -/
theorem span (q : ℕ) (x : HR R.G q) : ∃ c c' : ZMod 2, x = c • R.bot q + c' • R.top q := by
  have hd := R.two_le
  have hM : q < R.l (q + 1) := by
    have := R.l_ge (q + 1)
    have h2 : 2 * (q + 1) ≤ 2 * d * (q + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨c, c', h⟩ := R.span_stage (q + 1) q (HRmap (R.ρ (q + 1)) q x)
  refine ⟨c, c', R.ρ_injective_low (q + 1) q hM ?_⟩
  rw [map_add, map_smul, map_smul, h]

/-! ### Nilpotence of w -/

theorem wPow_bot (q : ℕ) : NilpotentW.wPow R.G q (d + 1) (R.bot q) = 0 := by
  by_cases h : ∃ j, R.IsBot j q
  · obtain ⟨j, hj⟩ := h
    have h0 : NilpotentW.wPow R.G (R.l j) (q - R.l j + (d + 1)) (R.X j) = 0 :=
      R.B_vanish_of_le j _ (by omega)
    rw [R.bot_of hj, B, wPow_castHR, wPow_wPow, h0, map_zero, map_zero]
  · rw [R.bot_zero h, wPow_map_zero]

theorem wPow_top (q : ℕ) : NilpotentW.wPow R.G q (d + 1) (R.top q) = 0 := by
  by_cases h : d + 1 ≤ q
  · rw [top, dif_pos h, wPow_castHR, ← R.E_wPow, R.wPow_bot, map_zero, map_zero, map_zero]
  · rw [top, dif_neg h, wPow_map_zero]

/-- The power w^{d+1} = w^n vanishes on the global reflection Borel cohomology. -/
theorem w_nil (lo : ℕ) (x : HR R.G lo) : NilpotentW.wPow R.G lo (d + 1) x = 0 := by
  obtain ⟨c, c', rfl⟩ := R.span lo x
  rw [wPow_map_add, wPow_map_smul, wPow_map_smul, R.wPow_bot, R.wPow_top, smul_zero, smul_zero, add_zero]

end RGlobal

end

end Finsler.GlobalBasis
