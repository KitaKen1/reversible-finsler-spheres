module

public import Finsler.Topology.PacketSupport

/-! the divisor roots of all
oriented prime labels form a finite catalogue. One maximum bounds their indices and all
ordinary root-crossing support cutoffs, independently of the iterate and critical level. -/

@[expose] public section

namespace Finsler.RootCatalogue

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels
open Finsler.CriticalCircles Finsler.CircleLabel Finsler.GeodesicFrames Finsler.OrientedCritical
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LevelBounds
open Finsler.CircleRoot

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (F : ReversibleMetric n) (hfin : (primeImages F).Finite)

abbrev rootOrder (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k : ℕ) :=
  Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L)

abbrev rootIndex (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k : ℕ) :=
  (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I (rootOrder F hfin ℓ hℓ k)

abbrev rootLevel (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k : ℕ) : ℝ :=
  (rootOrder F hfin ℓ hℓ k : ℝ) *
    Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)

abbrev rootH (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k q : ℕ) :=
  H (triv (pairOf (lev_mono F (isoBand_le F hfin (rootLevel F hfin ℓ hℓ k))))) q

def Bounds (A : ℕ) : Prop :=
  ∀ ℓ (hℓ : ℓ ∈ labels F hfin) (k : ℕ), 0 < k →
    rootIndex F hfin ℓ hℓ k ≤ A ∧
      (∀ q, Module.Finite (ZMod 2) (rootH F hfin ℓ hℓ k q)) ∧
      ∀ q, A ≤ q → ∀ z : rootH F hfin ℓ hℓ k q, z = 0

theorem rootLevel_pos (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin)
    {k : ℕ} (hk : 0 < k) : 0 < rootLevel F hfin ℓ hℓ k :=
  mul_pos (by exact_mod_cast Nat.gcd_pos_of_pos_left _ hk)
    (chosen_energy_pos F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ))

/-- The finite divisor-root catalogue supplies one index/support bound for all iterates. -/
theorem exists_bounds (hn : 1 ≤ n) : ∃ A : ℕ, Bounds F hfin A := by
  classical
  let C : Type := Σ ℓ : ↑(labels F hfin),
    ↑(Nat.divisors (2 * (iterData (labelGeod F ℓ.1 ((mem_labels F hfin ℓ.1).mp ℓ.2))).L))
  let level : C → ℝ := fun j => (j.2.1 : ℝ) * Real.sqrt
    (Finsler.LoopEnergy.energy F (chosen F j.1.1.1 ((mem_labels F hfin j.1.1).mp j.1.2)).loop)
  let index : C → ℕ := fun j =>
    (iterData (labelGeod F j.1.1 ((mem_labels F hfin j.1.1).mp j.1.2))).I j.2.1
  have hpositive : ∀ j : C, 0 < level j := by
    intro j
    exact mul_pos (by exact_mod_cast Nat.pos_of_mem_divisors j.2.2)
      (chosen_energy_pos F j.1.1.1 ((mem_labels F hfin j.1.1).mp j.1.2))
  have hbands : ∀ j : C, ∃ D : ℕ,
      (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F
        (isoBand_le F hfin (level j))))) q)) ∧
      ∀ q, D ≤ q → ∀ z : H (triv (pairOf (lev_mono F (isoBand_le F hfin (level j))))) q, z = 0 := by
    intro j
    obtain ⟨h0, _, _, _⟩ := isoBand_spec F hfin (hpositive j)
    obtain ⟨ha, hb⟩ := isoBand_regular F hfin (hpositive j)
    exact cross_finite F hn hfin h0 (isoBand_le F hfin (level j)) ha hb
  choose D hfinite hzero using hbands
  let A := Finset.univ.sup fun j : C => max (index j) (D j)
  refine ⟨A, fun ℓ hℓ k hk => ?_⟩
  have hL : 0 < 2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L := by
    have := (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).one_le
    omega
  have hroot : rootOrder F hfin ℓ hℓ k ∈
      Nat.divisors (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hL.ne'⟩
  let j : C := ⟨⟨ℓ, hℓ⟩, ⟨rootOrder F hfin ℓ hℓ k, hroot⟩⟩
  have hj : max (index j) (D j) ≤ A :=
    Finset.le_sup (f := fun j : C => max (index j) (D j)) (Finset.mem_univ j)
  exact ⟨(le_max_left _ _).trans hj, hfinite j,
    fun q hq => hzero j q ((le_max_right _ _).trans (hj.trans hq))⟩

end

end Finsler.RootCatalogue

