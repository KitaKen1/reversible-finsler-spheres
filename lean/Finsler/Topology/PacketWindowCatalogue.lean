module

public import Finsler.Topology.RootPacketWindows

/-! Choose the root cutoff before choosing a critical level or its finite active family. -/

@[expose] public section

namespace Finsler.PacketWindowCatalogue

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics
open Finsler.CriticalCircles Finsler.RootPacketWindows Finsler.CircleRootWindow

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

variable {n : ℕ}

def Catalogue (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (A : ℕ) : Prop :=
  ∀ ℓ (hℓ : ℓ ∈ Finsler.CriticalCircles.labels F hfin) (k : ℕ), 0 < k →
    ∃ Q : ℕ, Ready F hfin ℓ hℓ k A Q

theorem exists_catalogue (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, Finsler.RootCatalogue.Bounds F hfin A ∧ Catalogue F hfin A := by
  obtain ⟨A, hA, hwindow⟩ := exists_uniform_window F hn hfin
  refine ⟨A, hA, fun ℓ hℓ k hk => ?_⟩
  by_cases he : Even k
  · obtain ⟨j, hj⟩ := he
    have hkj : k = 2 * j := by omega
    have : NeZero j := ⟨by omega⟩
    obtain ⟨Q, hQ⟩ := hwindow ℓ hℓ k j hk hkj
    refine ⟨Q, fun N hN _ K _ c 𝒰 d hshare j' _ hj' => ?_⟩
    have hjj : j' = j := by omega
    subst j'
    exact @hQ N hN inferInstance K inferInstance c 𝒰 d hshare
  · exact ⟨0, fun N _ _ K _ c 𝒰 d _ j _ hj => False.elim (he ⟨j, by omega⟩)⟩

end

end Finsler.PacketWindowCatalogue
