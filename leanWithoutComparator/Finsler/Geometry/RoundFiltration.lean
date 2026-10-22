module

public import Finsler.Geometry.RoundCrossPattern
public import Finsler.Topology.FiltrationCollapse
public import Finsler.Topology.SmallLevel
public import Finsler.Topology.CrossingW

/-! The round sublevel filtration (G1).

With the cuts c_j = 2π(j + 1/2), the stages are Z_j = (t_{c_j}, M), the crossings
P_j = (t_{c_{j+1}}, t_{c_j}) contain the single critical level 2π(j + 1) of index
l_j = (2j + 1)(n − 1), the crossing sequences P_j → Z_{j+1} → Z_j are short exact, and Z_0 is
acyclic (small sublevels deform into the constant loops, and [b, π] carries a level deformation).
Given the e-compatibility of the start classes of the crossings, every crossing has its Gysin
pattern, which makes a `FiltrationCollapse.Filtration (n − 1)` for n ≥ 3. -/

@[expose] public section

namespace Finsler.RoundFiltration

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.RoundCrossPattern
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.CriticalLevels Finsler.GysinPattern Finsler.FiltrationCollapse Finsler.BorelGraded
open Finsler.RegularInterval
open Set Module

noncomputable section

variable {n : ℕ}

/-- The cuts. -/
def cut (j : ℕ) : ℝ := 2 * Real.pi * ((j : ℝ) + 1 / 2)

theorem cut_mono (j : ℕ) : cut j ≤ cut (j + 1) := by
  unfold cut
  push_cast
  have := Real.pi_pos
  nlinarith

theorem cut_lo (j : ℕ) : 2 * Real.pi * (((j + 1 : ℕ) : ℝ) - 1) < cut j := by
  unfold cut
  push_cast
  have := Real.pi_pos
  nlinarith

theorem cut_ac (j : ℕ) : cut j < 2 * Real.pi * ((j + 1 : ℕ) : ℝ) := by
  unfold cut
  push_cast
  have := Real.pi_pos
  nlinarith

theorem cut_cb (j : ℕ) : 2 * Real.pi * ((j + 1 : ℕ) : ℝ) < cut (j + 1) := by
  unfold cut
  push_cast
  have := Real.pi_pos
  nlinarith

theorem cut_hi (j : ℕ) : cut (j + 1) < 2 * Real.pi * (((j + 1 : ℕ) : ℝ) + 1) := by
  unfold cut
  push_cast
  have := Real.pi_pos
  nlinarith

/-! ### The acyclic first stage -/

/-- Ordinary cohomology vanishes where reflection Borel cohomology does. -/
theorem H_zero_of_HR_zero {K : InvComplex} (h : ∀ q (x : HR K q), x = 0) (q : ℕ) (z : H K q) :
    z = 0 := by
  obtain ⟨y, hy⟩ := (exact_transfer K q z).mp (h q _)
  rw [← hy, h q y, map_zero]

theorem HR_Z0_zero (hn : 1 ≤ n) (q : ℕ) (x : HR (levComplex (roundMetric n) (cut 0)) q) :
    x = 0 := by
  obtain ⟨b₀, hb₀, h⟩ := Finsler.SmallLevel.exists_HR_lev_eq_zero (roundMetric n)
  have hπ := Real.pi_pos
  set b := min b₀ Real.pi with hb
  have hb0 : 0 < b := lt_min hb₀ hπ
  have hbc : b ≤ cut 0 := by
    have : cut 0 = Real.pi := by unfold cut; push_cast; ring
    rw [this]
    exact min_le_right _ _
  have hreg : ∀ x ∈ Icc b (cut 0), x ∉ crit (roundMetric n) := by
    intro x hx hc
    obtain ⟨m', hm', rfl⟩ := Finsler.RoundCrossW.crit_round hc
    have h1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'
    have : cut 0 = Real.pi := by unfold cut; push_cast; ring
    have h2 := hx.2
    rw [this] at h2
    nlinarith
  obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular (roundMetric n) hn b (cut 0) (cut 0)
    hb0 hbc le_rfl hreg
  apply (cut_bijective_of_levelDeformation (roundMetric n) hbc D q).1
  rw [h b hb0 (min_le_left _ _) q (HRmap (cutHom (roundMetric n) hbc) q x), map_zero]

/-! ### The filtration -/

theorem l_succ (n j : ℕ) :
    lc n (j + 1 + 1) = lc n (j + 1) + 2 * (n - 1) := by
  unfold lc
  have h : 2 * (j + 1 + 1) - 1 = (2 * (j + 1) - 1) + 2 := by omega
  rw [h, add_mul]

/-- The e-compatibility of the round crossings: the e-multiple of a start class is not
forgotten to zero. -/
def ECompat (n : ℕ) (hn : 3 ≤ n) : Prop :=
  ∀ j (τ : HR (crossComplex (roundMetric n) (cut_mono j)) (lc n (j + 1))),
    forget _ (lc n (j + 1)) τ ≠ 0 →
      forget _ (lc n (j + 1) + (n - 1) + 1)
        (castHR (deg_eq (by omega) (lc n (j + 1)))
          (crossE (roundMetric n) (cut_mono j) (by omega) (lc n (j + 1)) τ)) ≠ 0

/-- The start class of the crossing j. -/
def startClass (hn : 3 ≤ n) (j : ℕ) :
    HR (crossComplex (roundMetric n) (cut_mono j)) (lc n (j + 1)) :=
  Classical.choose (cross_start (by omega) (Nat.succ_pos j) (cut_lo j) (cut_ac j) (cut_cb j)
    (cut_hi j) (cut_mono j))

theorem startClass_ne (hn : 3 ≤ n) (j : ℕ) : forget _ (lc n (j + 1)) (startClass hn j) ≠ 0 :=
  Classical.choose_spec (cross_start (by omega) (Nat.succ_pos j) (cut_lo j) (cut_ac j) (cut_cb j)
    (cut_hi j) (cut_mono j))

/-- **The round sublevel filtration.** -/
def roundFiltration (hn : 3 ≤ n) (he : ECompat n hn) : Filtration (n - 1) where
  two_le := by omega
  l j := lc n (j + 1)
  l_succ j := l_succ n j
  Z j := levComplex (roundMetric n) (cut j)
  P j := crossComplex (roundMetric n) (cut_mono j)
  ι j := relHom (roundMetric n) (cut_mono j)
  π j := cutHom (roundMetric n) (cut_mono j)
  exact j := shortExact (roundMetric n) (cut_mono j)
  zero q z := H_zero_of_HR_zero (HR_Z0_zero (by omega)) q z
  pattern j := roundPattern (by omega) (Nat.succ_pos j) (cut_lo j) (cut_ac j) (cut_cb j)
    (cut_hi j) (cut_mono j) (startClass hn j) (startClass_ne hn j)
    (he j (startClass hn j) (startClass_ne hn j))

end

end Finsler.RoundFiltration
