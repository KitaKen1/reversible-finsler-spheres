module

public import Finsler.Topology.RootParitySupport
public import Finsler.Topology.FixedAmbientSupport
public import Finsler.Topology.ScaledRootSupport

/-! Odd normal multiplicity: retain the loop crossing cutoff across the equal vertex
counts s*(2*N)=2*(s*N), half-fixed normalization, sampling and positive energy scaling. -/

@[expose] public section

namespace Finsler.OddRootSupport

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientPenalty
open Finsler.AmbientSymmetry Finsler.PolygonIterate Finsler.CircleHalfRotation
open Finsler.FixedAmbientNormalize Finsler.FixedAmbientSupport Finsler.FixedSampleK
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelFixed Finsler.CutPotential Finsler.FlowLens Finsler.LensFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def Supports {B : TopCat.{0}} (h : B → ℝ) {a b : ℝ} (hab : a ≤ b) (A : ℕ) : Prop :=
  (∀ q, Module.Finite (ZMod 2) (crossH h hab q)) ∧
    ∀ q, A ≤ q → ∀ z : crossH h hab q, z = 0

theorem supports_set_eq {B : TopCat.{0}} (P Q : Set B) (heq : P = Q) (h : B → ℝ)
    {a b : ℝ} (hab : a ≤ b) (A : ℕ) :
    Supports (fun z : TopCat.of P => h z) hab A ↔
      Supports (fun z : TopCat.of Q => h z) hab A := by
  subst Q
  rfl

def rotationSupport {n : ℕ} (F : ReversibleMetric n) (N : ℕ) [NeZero N]
    (j : ℕ) (r lam : ℝ) {a b : ℝ} (hab : a ≤ b) (A : ℕ) : Prop :=
  Supports (fun z : TopCat.of {z : Om n N | rotA N (j : ZMod N) z.1 = z.1} =>
    r * pen F N lam z.1.1) hab A

theorem reindex {n : ℕ} (F : ReversibleMetric n) {K L : ℕ} [NeZero K] [NeZero L]
    (heq : K = L) (j : ℕ) (r lam : ℝ) {a b : ℝ} (hab : a ≤ b) (A : ℕ) :
    rotationSupport F K j r lam hab A ↔ rotationSupport F L j r lam hab A := by
  subst L
  rfl

theorem scaled_half_support {n : ℕ} (F : ReversibleMetric n) (M : ℕ) [NeZero M]
    {r lam l u : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (hl : 0 < l) (hlu : l ≤ u)
    (hsample : ∀ q, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) hl hlu)) q)) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hlu))) q))
    (hz : ∀ q, A ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hlu))) q, z = 0) :
    rotationSupport F (2 * M) M r lam
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hlu 2) hr.le) A := by
  obtain ⟨hfa, hza⟩ := ambient_support_of_loop M F hlam hl hlu hsample A hf hz
  obtain ⟨hfi, hzi⟩ := Finsler.SubspacePairs.support_inside (fixOm M)
    (sub_mono (penW F (2 * M) lam) (pow_le_pow_left₀ hl.le hlu 2)) A hfa hza
  have hs := Finsler.ScaledRootSupport.cross_support r hr (pow_le_pow_left₀ hl.le hlu 2) A hfi hzi
  have heq : {z : Om n (2 * M) | rotA (2 * M) (M : ZMod (2 * M)) z.1 = z.1} =
      fixOm M := by
    ext z
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact (supports_set_eq _ _ heq (fun z : Om n (2 * M) => r * pen F (2 * M) lam z.1)
    _ A).mpr hs

theorem odd_support {n : ℕ} (F : ReversibleMetric n) (m s N : ℕ)
    [NeZero m] [NeZero s] [NeZero N] (hm : Odd m) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hsample : ∀ q, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := s * N) hl hlu)) q)) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hlu))) q))
    (hz : ∀ q, A ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hlu))) q, z = 0) :
    Supports (fun z : TopCat.of {z : Om n (s * (2 * N)) |
        rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
      (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hlu 2) (sq_nonneg (m : ℝ))) A := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hs := scaled_half_support F (s * N) (sq_pos_of_pos hmpos)
    (le_of_lt (div_pos zero_lt_one hmpos)) hl hlu hsample A hf hz
  have heq : s * (2 * N) = 2 * (s * N) := by ring
  have hsg := (reindex F heq (s * N) ((m : ℝ) ^ 2) (1 / m) _ A).mpr hs
  exact (supports_set_eq _ _ (Finsler.RootFlowFixed.fixed_odd m s N hm)
    (fun z : Om n (s * (2 * N)) => (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1) _ A).mpr hsg

theorem exists_odd_support {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (Finsler.Geodesics.primeImages F).Finite) (m s : ℕ) [NeZero m] [NeZero s]
    (hm : Odd m) (upper : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u),
      u ≤ upper → l ∉ Finsler.CriticalLevels.crit F → u ∉ Finsler.CriticalLevels.crit F →
      ∃ A : ℕ, Supports (fun z : TopCat.of {z : Om n (s * (2 * N)) |
          rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hlu 2) (sq_nonneg (m : ℝ))) A := by
  obtain ⟨N₀, hN₀⟩ := exists_sample_ordinary F hn upper
  refine ⟨N₀, fun N hN _ l u hl hlu hu hlc huc => ?_⟩
  have hNN : N ≤ s * N := by
    simpa only [one_mul] using Nat.mul_le_mul_right N (Nat.one_le_iff_ne_zero.mpr (NeZero.ne s))
  obtain ⟨A, hf, hz⟩ := Finsler.FixedCrossingSupport.fixed_cross_finite F hn hfin hl hlu hlc huc
  exact ⟨A, odd_support F m s N hm hl hlu (hN₀ (s * N) (hN.trans hNN) hl hlu hu) A hf hz⟩

end

end Finsler.OddRootSupport
