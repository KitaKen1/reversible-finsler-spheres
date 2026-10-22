module

public import Finsler.Topology.CrossingW
public import Finsler.Topology.SmallLevel

/-! Nilpotence of w at finite cuts. The k-fold power of w is natural for maps of involutive
complexes. If restriction from (t_b, M) to (t_a, M) is injective, a power of w which vanishes on
the groups of t_a vanishes on those of t_b; if w acts as zero on the crossing group of
(t_b, t_a), a k-th power which vanishes on the groups of t_a gives a (k+1)-st power vanishing on
those of t_b, by exactness of the crossing sequence. With finitely many prime closed geodesic
images, the groups of small sublevels vanish, intervals without critical levels carry level
deformations, and w acts as zero on single crossings; by induction on the number of critical
levels below a regular cut a > 0, some power of w vanishes on the reflection Borel cohomology of
(t_a, M). The induction over the critical levels is stated for an arbitrary property of a level
and a number. -/

@[expose] public section

namespace Finsler.NilpotentW

open Set
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.BorelLoop
open Finsler.BorelCochain Finsler.BorelCrossing Finsler.CriticalLevels Finsler.RegularInterval

noncomputable section

/-- The k-fold power of w on the Borel cohomology of an involutive complex, from degree lo. -/
def wPow (K : InvComplex) (lo k : ℕ) : HR K lo → HR K (lo + k) :=
  Finsler.Gysin.word (V := fun i => HR K (lo + i))
    (fun i => (w K (lo + i)).toAddMonoidHom) k

theorem wPow_zero (K : InvComplex) (lo : ℕ) (x : HR K lo) : wPow K lo 0 x = x := rfl

theorem wPow_succ (K : InvComplex) (lo k : ℕ) (x : HR K lo) :
    wPow K lo (k + 1) x = w K (lo + k) (wPow K lo k x) := rfl

/-- Powers of w are natural. -/
theorem HRmap_wPow {K L : InvComplex} (φ : InvHom K L) (lo k : ℕ) (x : HR K lo) :
    HRmap φ (lo + k) (wPow K lo k x) = wPow L lo k (HRmap φ lo x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wPow_succ, wPow_succ, ← ih]
    exact HRmap_w φ (lo + k) (wPow K lo k x)

variable {n : ℕ} (F : ReversibleMetric n)

/-- A power of w vanishing at the lower cut vanishes at the upper cut if restriction is
injective. -/
theorem nilpotent_of_injective {a b : ℝ} (hab : a ≤ b)
    (hinj : ∀ q, Function.Injective (HRmap (cutHom F hab) q)) {k : ℕ}
    (h : ∀ (lo : ℕ) (x : HR (levComplex F a) lo), wPow (levComplex F a) lo k x = 0) (lo : ℕ)
    (x : HR (levComplex F b) lo) : wPow (levComplex F b) lo k x = 0 := by
  apply hinj (lo + k)
  rw [HRmap_wPow, h, map_zero]

/-- If w acts as zero on the crossing group, a k-th power of w vanishing at the lower cut gives
a (k+1)-st power vanishing at the upper cut. -/
theorem nilpotent_of_crossing {a b : ℝ} (hab : a ≤ b)
    (hw : ∀ (q : ℕ) (z : HR (crossComplex F hab) q), w (crossComplex F hab) q z = 0) {k : ℕ}
    (h : ∀ (lo : ℕ) (x : HR (levComplex F a) lo), wPow (levComplex F a) lo k x = 0) (lo : ℕ)
    (x : HR (levComplex F b) lo) : wPow (levComplex F b) lo (k + 1) x = 0 := by
  have hcut : HRmap (cutHom F hab) (lo + k) (wPow (levComplex F b) lo k x) = 0 := by
    rw [HRmap_wPow, h]
  obtain ⟨z, hz⟩ := exact_crossing F hab (lo + k) _ hcut
  rw [wPow_succ, ← hz, ← HRmap_w, hw, map_zero]

/-- Induction over the critical levels below a regular cut. Let P be a property of a positive
level and a number which holds with number 0 at all small levels, is transported with the same
number along intervals without critical levels, and with the next number across regular cuts
with at most one critical level between them. With finitely many prime closed geodesic images
it holds with some number at every positive regular cut. -/
theorem exists_of_levels (hfin : (primeImages F).Finite) (P : ℝ → ℕ → Prop)
    (hsmall : ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → P b 0)
    (hreg : ∀ a b : ℝ, 0 < a → a ≤ b → (∀ x ∈ Icc a b, x ∉ crit F) → ∀ k : ℕ, P a k → P b k)
    (hcross : ∀ a b : ℝ, 0 < a → a ≤ b → a ∉ crit F → b ∉ crit F →
      (crit F ∩ Icc a b).Subsingleton → ∀ k : ℕ, P a k → P b (k + 1))
    (a : ℝ) (ha : 0 < a) (hac : a ∉ crit F) : ∃ k : ℕ, P a k := by
  have key : ∀ m : ℕ, ∀ a : ℝ, 0 < a → a ∉ crit F → (crit F ∩ Icc 0 a).ncard = m →
      ∃ k : ℕ, P a k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro a ha hac hm
      have hSfin : (crit F ∩ Icc 0 a).Finite := crit_finite F hfin 0 a
      by_cases hne : (crit F ∩ Icc 0 a).Nonempty
      · obtain ⟨c, hcS, hcmax⟩ := Set.exists_max_image _ id hSfin hne
        have hc0 : 0 < c := crit_pos F hcS.1
        have hca : c < a := lt_of_le_of_ne hcS.2.2 (fun h => hac (h ▸ hcS.1))
        have hTfin : (insert (0 : ℝ) ((crit F ∩ Icc 0 a) \ {c})).Finite :=
          (hSfin.subset sdiff_subset).insert 0
        obtain ⟨c', hc'T, hc'max⟩ := Set.exists_max_image _ id hTfin (insert_nonempty _ _)
        have hc'c : c' < c := by
          rcases hc'T with h | ⟨hx, hxne⟩
          · rw [h]
            exact hc0
          · exact lt_of_le_of_ne (hcmax _ hx) hxne
        have hc'0 : 0 ≤ c' := hc'max 0 (mem_insert _ _)
        have ha'0 : 0 < (c' + c) / 2 := by linarith
        have hlow : ∀ x ∈ crit F, 0 ≤ x → x ≤ a → x ≠ c → x ≤ c' := fun x hx h0 hxa hxc =>
          hc'max x (mem_insert_of_mem _ ⟨⟨hx, h0, hxa⟩, hxc⟩)
        have ha'c : (c' + c) / 2 ∉ crit F := by
          intro h
          have := hlow _ h ha'0.le (by linarith) (ne_of_lt (by linarith))
          linarith
        have hall : ∀ x ∈ crit F ∩ Icc ((c' + c) / 2) a, x = c := by
          rintro x ⟨hx, hx1, hx2⟩
          by_contra hxc
          have := hlow x hx (by linarith) hx2 hxc
          linarith
        have hsub : (crit F ∩ Icc ((c' + c) / 2) a).Subsingleton := by
          intro x hx y hy
          rw [hall x hx, hall y hy]
        have hlt : (crit F ∩ Icc 0 ((c' + c) / 2)).ncard < m := by
          rw [← hm]
          apply Set.ncard_lt_ncard _ hSfin
          refine ⟨fun x hx => ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩, fun hsup => ?_⟩
          have := (hsup hcS).2.2
          linarith
        obtain ⟨k, hk⟩ := ih _ hlt ((c' + c) / 2) ha'0 ha'c rfl
        have hab : (c' + c) / 2 ≤ a := by linarith
        exact ⟨k + 1, hcross _ a ha'0 hab ha'c hac hsub k hk⟩
      · obtain ⟨b₀, hb₀, hzero⟩ := hsmall
        have hb : 0 < min a b₀ := lt_min ha hb₀
        have hreg' : ∀ x ∈ Icc (min a b₀) a, x ∉ crit F := fun x hx hxc =>
          hne ⟨x, hxc, by linarith [hx.1], hx.2⟩
        exact ⟨0, hreg _ a hb (min_le_left _ _) hreg' 0 (hzero _ hb (min_le_right _ _))⟩
  exact key _ a ha hac rfl

/-- With finitely many prime closed geodesic images, w is nilpotent on the reflection Borel
cohomology of (t_a, M) at every regular cut a > 0. -/
theorem exists_w_nilpotent (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (a : ℝ) (ha : 0 < a)
    (hac : a ∉ crit F) :
    ∃ k : ℕ, ∀ (lo : ℕ) (x : HR (levComplex F a) lo), wPow (levComplex F a) lo k x = 0 := by
  refine exists_of_levels F hfin
    (fun a k => ∀ (lo : ℕ) (x : HR (levComplex F a) lo), wPow (levComplex F a) lo k x = 0)
    ?_ ?_ ?_ a ha hac
  · obtain ⟨b₀, hb₀, hzero⟩ := Finsler.SmallLevel.exists_HR_lev_eq_zero F
    exact ⟨b₀, hb₀, fun b hb hbb lo x => hzero b hb hbb lo x⟩
  · intro a b ha hab hreg k hk
    obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn a b b ha hab le_rfl hreg
    exact nilpotent_of_injective F hab
      (fun q => (cut_bijective_of_levelDeformation F hab D q).1) hk
  · intro a b ha hab hac hbc hsub k hk
    exact nilpotent_of_crossing F hab
      (fun q z => Finsler.CrossingW.crossW_zero_of_finite F hn hfin hab ha hac hbc hsub q z) hk

end

end Finsler.NilpotentW
