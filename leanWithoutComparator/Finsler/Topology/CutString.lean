module

public import Finsler.Topology.EventSum
public import Finsler.Topology.StringBound

/-! Strings of powers of w at a regular cut against the budget of the potentials. The normalized
restriction of the cut 2a satisfies the three rules of `StringBound`: the class v of the half
rotation leaves it unchanged, the reflection class raises the root degree, and the root degree
zero component of a multiple of the reflection class vanishes. Hence, with finitely many prime
closed geodesic images and local bounds for single crossings, a string y_l ≠ 0, w y_l = y_{l+1},
in the reflection Borel cohomology of (t_a, M), of length ν from L₀ and nonzero up to
L₀ + ν + q, a block of N₁ cutoffs above the string and a block of N₂ cutoffs below L₀ + q satisfy

  N₁ · N₂ · ν ≤ (N₁ + N₂) · 6MN · #(critical levels in [0, 2a]).

The right side grows linearly in a, so long strings are excluded at large cuts. The local bounds
are not proved. -/

@[expose] public section

namespace Finsler.CutString

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed Finsler.BorelExact
open Finsler.BorelFreeK Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK
open Finsler.BorelCoverK Finsler.LocalCoverK Finsler.TotalExact Finsler.GradedLadder
open Finsler.FixedLadder Finsler.LadderEvent Finsler.CutPotential Finsler.CutFinite
open Finsler.CriticalLevels Finsler.FiniteCut Finsler.LocalizeK Finsler.TrivialK
open Finsler.FixedGlobal Finsler.LevelCount Finsler.EventSum Finsler.StringBound

noncomputable section

variable {n : ℕ}

/-- The root degree zero component of the normalized restriction of a multiple of the reflection
class vanishes. -/
theorem eps_innerStep_zero {s t s₀ t₀ : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s)
    (ht : KInv t) (hst₀ : s₀ ⊆ t₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀) (hss : s₀ ⊆ s) (htt : t₀ ⊆ t)
    (hfix : ∀ u : SphereLoop n, u ∈ t₀ → half +ᵥ u = u) (q : ℕ)
    (x : HR (borelInv (kCommuting hst hs ht)) q) :
    eps hst hs ht hst₀ hs₀ ht₀ hss htt hfix (q + 1) 0 (innerStep (kCommuting hst hs ht) q x) =
      0 := by
  rw [eps_apply, HRmap_innerStep]
  exact theta_innerStep_zero (kCommuting hst₀ hs₀ ht₀) (kCommuting_trivial hst₀ hs₀ ht₀ hfix) q _

variable {F : ReversibleMetric n}

/-- A string in the reflection Borel cohomology of the fixed pair of a regular cut 2a against
the budget of the potentials. -/
theorem fix_string_budget (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {a : ℝ} (ha : 0 < a) (h2a : 2 * a ∉ crit F) (y : ∀ l, fixR F (2 * a) l) (L₀ ν q : ℕ)
    (hy : ∀ l, L₀ ≤ l →
      w (rComplex (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a))) l
        (y l) = y (l + 1))
    (hne : ∀ l, L₀ ≤ l → l < L₀ + ν + q → y l ≠ 0)
    (k₁ N₁ k₂ N₂ : ℕ) (h₁ : L₀ + ν ≤ k₁ + 1 + 1) (h₂ : k₂ + N₂ < L₀ + q)
    (h₁₂ : 2 * (k₁ + N₁) + q ≤ 2 * k₂ + 2) :
    (N₁ : ℤ) * (N₂ : ℤ) * (ν : ℤ) ≤
      ((N₁ : ℤ) + (N₂ : ℤ)) * (6 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ)) := by
  have h0a : 0 < 2 * a := by linarith
  have hfinA : ∀ p, Module.Finite (ZMod 2) (HR (borelInv (kCommuting (consts_subset_lev F (2 * a))
      kInv_consts (kInv_lev F (2 * a)))) p) := fun p => finite_HK F hn hfin h0a h2a p
  exact @string_budget (fixR F (2 * a)) _ _
    (fun l => w (rComplex (consts_subset_fixLev F (2 * a)) kInv_consts
      (kInv_fixLev F (2 * a))) l)
    (fun p => HR (borelInv (kCommuting (consts_subset_lev F (2 * a)) kInv_consts
      (kInv_lev F (2 * a)))) p)
    (fun p => (inferInstance : AddCommGroup (HR (borelInv (kCommuting
      (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a)))) p)))
    (fun p => (inferInstance : Module (ZMod 2) (HR (borelInv (kCommuting
      (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a)))) p)))
    (fun p l => eps (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a))
      (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a)) subset_rfl
      (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p l)
    (fun p => w (borelInv (kCommuting (consts_subset_lev F (2 * a)) kInv_consts
      (kInv_lev F (2 * a)))) p)
    (fun p => innerStep (kCommuting (consts_subset_lev F (2 * a)) kInv_consts
      (kInv_lev F (2 * a))) p)
    (finTot_fixR F hn hfin ha h2a) hfinA
    (fun p l x => eps_w (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a))
      (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a)) subset_rfl
      (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p l x)
    (fun p l x => eps_innerStep (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a))
      (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a)) subset_rfl
      (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p l x)
    (fun p x => eps_innerStep_zero (consts_subset_lev F (2 * a)) kInv_consts
      (kInv_lev F (2 * a)) (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a))
      subset_rfl (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p x)
    (pot F (2 * a)) (fun k => rfl)
    (6 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ))
    (fun K => sum_pot_le E hn hfin ha h2a K)
    y L₀ ν q hy hne k₁ N₁ k₂ N₂ h₁ h₂ h₁₂

/-- A string in the reflection Borel cohomology of (t_a, M) against the budget of the potentials
of the cut 2a. -/
theorem lev_string_budget (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {a : ℝ} (ha : 0 < a) (h2a : 2 * a ∉ crit F) (y : ∀ l, HR (levComplex F a) l) (L₀ ν q : ℕ)
    (hy : ∀ l, L₀ ≤ l → w (levComplex F a) l (y l) = y (l + 1))
    (hne : ∀ l, L₀ ≤ l → l < L₀ + ν + q → y l ≠ 0)
    (k₁ N₁ k₂ N₂ : ℕ) (h₁ : L₀ + ν ≤ k₁ + 1 + 1) (h₂ : k₂ + N₂ < L₀ + q)
    (h₁₂ : 2 * (k₁ + N₁) + q ≤ 2 * k₂ + 2) :
    (N₁ : ℤ) * (N₂ : ℤ) * (ν : ℤ) ≤
      ((N₁ : ℤ) + (N₂ : ℤ)) * (6 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ)) :=
  fix_string_budget E hn hfin ha h2a (fun l => doublingEquiv F a l (y l)) L₀ ν q
    (fun l hl => (HRmap_w (rootHom F a) l (y l)).symm.trans
      (congrArg (HRmap (rootHom F a) (l + 1)) (hy l hl)))
    (fun l hl hl' h0 => hne l hl hl'
      ((doublingEquiv F a l).injective (h0.trans (doublingEquiv F a l).map_zero.symm)))
    k₁ N₁ k₂ N₂ h₁ h₂ h₁₂

end

end Finsler.CutString
