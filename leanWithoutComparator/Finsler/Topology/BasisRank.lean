module

public import Finsler.Topology.BasisBudget
public import Finsler.Topology.FixedCrossingSupport
public import Finsler.Topology.BandRank
public import Finsler.Topology.RankAssembly

/-! The global basis's two generators bound ordinary groups and
all restriction images. The existence of the global basis remains an input. -/

@[expose] public section

namespace Finsler.BasisRank

open Set Module Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BasisBudget Finsler.CriticalLevels

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1000000

variable {n : ℕ} {hn : 1 ≤ n} (G : Data n hn)

include G hn

def generators (q : ℕ) : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] HR (fullComplex n) q :=
  (LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2)).smulRight (G.bot q) +
    (LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2)).smulRight (G.top q)

theorem generators_surjective (q : ℕ) : Function.Surjective (generators G q) := by
  intro x
  obtain ⟨c, c', h⟩ := G.span q x
  exact ⟨(c, c'), h.symm⟩

theorem finite_HR (q : ℕ) : Module.Finite (ZMod 2) (HR (fullComplex n) q) :=
  Module.Finite.of_surjective (generators G q) (generators_surjective G q)

theorem finrank_HR_le (q : ℕ) : finrank (ZMod 2) (HR (fullComplex n) q) ≤ 2 := by
  have h := LinearMap.finrank_le_finrank_of_surjective (generators_surjective G q)
  simpa only [Module.finrank_prod, Module.finrank_self] using h

theorem finite_H (q : ℕ) : Module.Finite (ZMod 2) (H (fullComplex n) q) :=
  Finsler.FixedCrossingSupport.finite_H_of_HR (fullComplex n) q (finite_HR G q)

theorem finrank_H_le (q : ℕ) : finrank (ZMod 2) (H (fullComplex n) q) ≤ 4 := by
  have := finite_HR G q
  have := finite_H G q
  have h := Finsler.BandRank.finrank_le_of_exact (forget (fullComplex n) q)
    (transfer (fullComplex n) q) (fun z hz => (exact_transfer (fullComplex n) q z).mp hz)
  have hR := finrank_HR_le G q
  omega

theorem restriction_rank (F : ReversibleMetric n) (a : ℝ) (q : ℕ) :
    finrank (ZMod 2) (LinearMap.range (Hmap (resHom F a) q)) ≤ 4 := by
  have := finite_H G q
  exact (LinearMap.finrank_range_le (Hmap (resHom F a) q)).trans (finrank_H_le G q)

theorem nonempty_rankInputs (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (a₀ : ℝ) :
    Nonempty (Finsler.ComparisonRank.RankInputs F a₀) :=
  Finsler.RankAssembly.nonempty_rankInputs F hn hfin fun J =>
    ⟨4, fun a _ i _ => restriction_rank G F a i⟩

end

end Finsler.BasisRank
