module

public import Finsler.Topology.CutFinite
public import Finsler.Topology.LevelBounds

/-! Fixed crossing support and sampled half-index comparisons. -/

@[expose] public section

namespace Finsler.FixedCrossingSupport

open Module Set CategoryTheory
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.CriticalLevels
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelFixed Finsler.BorelLocalK Finsler.CutPotential Finsler.LevelBounds
open Finsler.LocalCoverK

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem finite_H_of_HR (K : InvComplex) (q : ℕ)
    (h : Module.Finite (ZMod 2) (HR K q)) : Module.Finite (ZMod 2) (H K q) := by
  have := h
  exact Finsler.TameHomology.finite_of_exact_linear (forget K q) (transfer K q)
    (fun z hz => (exact_transfer K q z).mp hz)

theorem H_eq_zero_of_HR (K : InvComplex) (q : ℕ)
    (h : ∀ z : HR K q, z = 0) (x : H K q) : x = 0 := by
  obtain ⟨y, hy⟩ := (exact_transfer K q x).mp (h _)
  rw [h y, map_zero] at hy
  exact hy.symm

theorem fixed_cross_finite {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hac : a ∉ crit F) (hbc : b ∉ crit F) :
    ∃ D : ℕ, (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F hab))) q)) ∧
      ∀ q, D ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F hab))) q, z = 0 := by
  have hhalf : ∃ D : ℕ, (∀ q, Module.Finite (ZMod 2) (crossR F hab q)) ∧
      ∀ q, D ≤ q → ∀ z : crossR F hab q, z = 0 := by
    obtain ⟨a', rfl⟩ : ∃ a' : ℝ, a = 2 * a' := ⟨a / 2, by ring⟩
    obtain ⟨b', rfl⟩ : ∃ b' : ℝ, b = 2 * b' := ⟨b / 2, by ring⟩
    exact Finsler.CutFinite.exists_crossR_finite F hn hfin (by linarith) hab hac hbc
  obtain ⟨D, hf, hz⟩ := hhalf
  let K := Finsler.FixedLadder.rComplex (fixLev_mono F hab)
    (kInv_fixLev F a) (kInv_fixLev F b)
  let e := fun q => LevelBounds.ofPairEquiv (pairOf (fixLev_mono F hab))
    (Finsler.AvoidPoint.revSub_sq (fixLev_mono F hab) (kInv_fixLev F a).rev_mem
      (kInv_fixLev F b).rev_mem) (Category.comp_id _) q
  refine ⟨D, fun q => ?_, fun q hq z => ?_⟩
  · have := finite_H_of_HR K q (hf q)
    exact Module.Finite.equiv (e q)
  · have hzero := H_eq_zero_of_HR K q (hz q hq) ((e q).symm z)
    exact (e q).symm.injective (hzero.trans ((e q).symm.map_zero).symm)

end

end Finsler.FixedCrossingSupport
