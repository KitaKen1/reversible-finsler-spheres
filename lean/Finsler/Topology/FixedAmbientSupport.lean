module

public import Finsler.Topology.FixedAmbientNormalize
public import Finsler.Topology.FixedCrossingSupport

/-! Fixed crossing support and sampled half-index comparisons. -/

@[expose] public section

namespace Finsler.FixedAmbientSupport

open CategoryTheory Set Module
open Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics Finsler.CriticalLevels
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.PolygonLoopPairs
open Finsler.PolygonDescent Finsler.FlowLens Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.BorelFixed Finsler.CutPotential
open Finsler.AmbientPenalty Finsler.FixedAmbientNormalize Finsler.FixedSampleK
open Finsler.LensFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

theorem exists_sample_ordinary (F : ReversibleMetric n) (hn : 1 ≤ n) (A : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ [NeZero M] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b), b ≤ A →
      ∀ q : ℕ, Function.Bijective (Hmap (trivHom (samplePairFix (F := F) (M := M) ha hab)) q) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := A) S.pos
  obtain ⟨c, hc, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (A ^ 2 / (c * S.δ ^ 2))
  refine ⟨max N₁ N₂, fun M hM _ a b ha hab hbA => ?_⟩
  have hN : max N₁ N₂ ≤ 2 * M := le_trans hM (by omega)
  have hNpos : 0 < 2 * M := by have := NeZero.ne M; omega
  let P : PolygonModelData F A (2 * M) :=
    PolygonModelData.mk S fun u hu s t hs ht hst =>
      hN₁ (2 * M) ((le_max_left _ _).trans hN) hNpos u hu s t hs ht hst
  have hNR : A ^ 2 / (c * S.δ ^ 2) < ((2 * M : ℕ) : ℝ) :=
    hN₂.trans_le (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  have hshort : ∀ q : ZMod (2 * M) → Sphere n, energy F (2 * M) q < b ^ 2 →
      ShortPolygon P.δ q := fun q hq =>
    short_of_energy_lt hc S.pos hedge hbA (ha.le.trans hab) hNR q hq
  exact fun q => fixed_sample_bijective P hshort ha hab hbA q

variable (M : ℕ) [NeZero M] (F : ReversibleMetric n) {lam a b : ℝ}

abbrev ambientFixedH (ha : 0 < a) (hab : a ≤ b) (q : ℕ) :=
  H (triv (pairOf (inter_subset_inter_left (fixOm M)
    (sub_mono (penW F (2 * M) lam) (pow_le_pow_left₀ ha.le hab 2))))) q

def ambientLoopEquiv (hlam : 0 ≤ lam) (ha : 0 < a) (hab : a ≤ b)
    (hsample : ∀ q : ℕ, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) ha hab)) q)) (q : ℕ) :
    ambientFixedH M F (lam := lam) ha hab q ≃ₗ[ZMod 2]
      H (triv (pairOf (fixLev_mono F hab))) q :=
  (LinearEquiv.ofBijective
    (Hmap (trivHom (normalizeFixPair M F hlam (pow_le_pow_left₀ ha.le hab 2))) q)
    (normalizeFix_bijective M F hlam (pow_le_pow_left₀ ha.le hab 2) q)).symm.trans
    (LinearEquiv.ofBijective (Hmap (trivHom (samplePairFix (F := F) (M := M) ha hab)) q) (hsample q))

theorem ambient_support_of_loop (hlam : 0 ≤ lam) (ha : 0 < a) (hab : a ≤ b)
    (hsample : ∀ q : ℕ, Function.Bijective
      (Hmap (trivHom (samplePairFix (F := F) (M := M) ha hab)) q)) (D : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hab))) q))
    (hz : ∀ q, D ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hab))) q, z = 0) :
    (∀ q, Module.Finite (ZMod 2) (ambientFixedH M F (lam := lam) ha hab q)) ∧
      ∀ q, D ≤ q → ∀ z : ambientFixedH M F (lam := lam) ha hab q, z = 0 := by
  let e := fun q => ambientLoopEquiv M F hlam ha hab hsample q
  constructor
  · intro q
    have := hf q
    exact Module.Finite.equiv (e q).symm
  · intro q hq z
    exact (e q).injective ((hz q hq ((e q) z)).trans ((e q).map_zero).symm)

theorem exists_ambient_fixed_finite (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (A : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ [NeZero M] {lam a b : ℝ}, 0 ≤ lam →
      ∀ (ha : 0 < a) (hab : a ≤ b), b ≤ A → a ∉ crit F → b ∉ crit F →
      ∃ D : ℕ, (∀ q, Module.Finite (ZMod 2) (ambientFixedH M F (lam := lam) ha hab q)) ∧
        ∀ q, D ≤ q → ∀ z : ambientFixedH M F (lam := lam) ha hab q, z = 0 := by
  obtain ⟨M₀, hM₀⟩ := exists_sample_ordinary F hn A
  refine ⟨M₀, fun M hM _ lam a b hlam ha hab hbA hac hbc => ?_⟩
  obtain ⟨D, hf, hz⟩ := FixedCrossingSupport.fixed_cross_finite F hn hfin ha hab hac hbc
  exact ⟨D, ambient_support_of_loop M F hlam ha hab (hM₀ M hM ha hab hbA) D hf hz⟩

end

end Finsler.FixedAmbientSupport
