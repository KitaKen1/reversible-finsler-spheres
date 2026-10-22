module

public import Finsler.Topology.RootCatalogue
public import Finsler.Topology.FixedCrossingSupport

/-! Fixed crossing support and sampled half-index comparisons. -/

@[expose] public section

namespace Finsler.FixedRootCatalogue

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels
open Finsler.CriticalCircles Finsler.CircleLabel Finsler.GeodesicFrames Finsler.OrientedCritical
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LevelBounds Finsler.CircleRoot Finsler.RootCatalogue Finsler.CutPotential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (F : ReversibleMetric n) (hfin : (primeImages F).Finite)

abbrev fixedRootH (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k q : ℕ) :=
  H (triv (pairOf (fixLev_mono F (isoBand_le F hfin (rootLevel F hfin ℓ hℓ k))))) q

def FixedBounds (A : ℕ) : Prop :=
  ∀ ℓ (hℓ : ℓ ∈ labels F hfin) (k : ℕ), 0 < k →
    (∀ q, Module.Finite (ZMod 2) (fixedRootH F hfin ℓ hℓ k q)) ∧
      ∀ q, A ≤ q → ∀ z : fixedRootH F hfin ℓ hℓ k q, z = 0

theorem ordinary_bounds_mono {A B : ℕ} (h : RootCatalogue.Bounds F hfin A) (hAB : A ≤ B) :
    RootCatalogue.Bounds F hfin B := by
  intro ℓ hℓ k hk
  obtain ⟨hI, hf, hz⟩ := h ℓ hℓ k hk
  exact ⟨hI.trans hAB, hf, fun q hq => hz q (hAB.trans hq)⟩

theorem exists_bounds (hn : 1 ≤ n) :
    ∃ A : ℕ, RootCatalogue.Bounds F hfin A ∧ FixedBounds F hfin A := by
  classical
  obtain ⟨A₀, hA₀⟩ := RootCatalogue.exists_bounds F hfin hn
  let C : Type := Σ ℓ : ↑(labels F hfin),
    ↑(Nat.divisors (2 * (iterData (labelGeod F ℓ.1 ((mem_labels F hfin ℓ.1).mp ℓ.2))).L))
  let level : C → ℝ := fun j => (j.2.1 : ℝ) * Real.sqrt
    (Finsler.LoopEnergy.energy F (chosen F j.1.1.1 ((mem_labels F hfin j.1.1).mp j.1.2)).loop)
  have hpositive : ∀ j : C, 0 < level j := by
    intro j
    exact mul_pos (by exact_mod_cast Nat.pos_of_mem_divisors j.2.2)
      (chosen_energy_pos F j.1.1.1 ((mem_labels F hfin j.1.1).mp j.1.2))
  have hbands : ∀ j : C, ∃ D : ℕ,
      (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (fixLev_mono F
        (isoBand_le F hfin (level j))))) q)) ∧
      ∀ q, D ≤ q → ∀ z : H (triv (pairOf (fixLev_mono F (isoBand_le F hfin (level j))))) q, z = 0 := by
    intro j
    obtain ⟨ha, hb⟩ := isoBand_regular F hfin (hpositive j)
    obtain ⟨h0, _, _, _⟩ := isoBand_spec F hfin (hpositive j)
    exact FixedCrossingSupport.fixed_cross_finite F hn hfin h0 (isoBand_le F hfin (level j)) ha hb
  choose D hf hz using hbands
  let A : ℕ := max A₀ (Finset.univ.sup D)
  refine ⟨A, ordinary_bounds_mono F hfin hA₀ (le_max_left _ _), fun ℓ hℓ k hk => ?_⟩
  have hL : 0 < 2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L := by
    have := (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).one_le
    omega
  have hroot : rootOrder F hfin ℓ hℓ k ∈
      Nat.divisors (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hL.ne'⟩
  let j : C := ⟨⟨ℓ, hℓ⟩, ⟨rootOrder F hfin ℓ hℓ k, hroot⟩⟩
  have hj : D j ≤ A :=
    (Finset.le_sup (f := D) (Finset.mem_univ j)).trans (le_max_right _ _)
  exact ⟨hf j, fun q hq => hz j q (hj.trans hq)⟩

end

end Finsler.FixedRootCatalogue
