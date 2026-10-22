module

public import Finsler.Topology.GlobalBasis
public import Finsler.Geometry.RoundYTop

/-! Ordinary classes of the loop space pair in the four degrees of every block.

For a global filtration (`GlobalBasis.RGlobal`) the reflection Borel cohomology of the whole pair
has, for every stage j, the bottom X_j in degree l_j, its w-tower B_{j,k} = w^k X_j and the
e-tower Tw_{j,k} = w^k (e X_j), k ≤ d, with w^{d+1} = 0. The Gysin sequence
H_R^{q−1} →w H_R^q →forget H^q →transfer H_R^q →w H_R^{q+1} then gives nonzero ordinary classes in
the four degrees l_j, l_j + d, l_j + d + 1 and l_j + 2d + 1:
* forget X_j and forget (e X_j) are nonzero, since their restrictions to the stage j + 1 are the
  images of the start class τ_j and of σ_j = e τ_j, which are not forgotten to zero, under the
  ordinary inclusion of the crossing, injective because the ordinary connecting maps vanish;
* B_{j,d} and Tw_{j,d} are nonzero and killed by w, so they are transfers of nonzero ordinary
  classes.
For the round filtration this is the ordinary cohomology of (Λ, M) in the degrees
lc n (j+1) + {0, n−1, n, 2n−1}. -/

@[expose] public section

namespace Finsler.OrdinaryBasis

open Finsler.BorelCochain Finsler.BorelExact Finsler.CrossingCollapse Finsler.GysinPattern
open Finsler.FiltrationCollapse Finsler.BorelGraded Finsler.GlobalBasis Finsler.NilpotentW
open Module

noncomputable section

variable {d : ℕ} (R : RGlobal d)

/-- The ordinary inclusion of a crossing into its stage is injective in positive degrees. -/
theorem ι_injective (j q : ℕ) (hq : 1 ≤ q) : Function.Injective (Hmap (R.ι j) q) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := OrdinaryDelta.exact_sub (R.exact j) q' z hz
  exact R.delta_ord_zero j q' y

theorem forget_castHR {K : InvComplex} {a b : ℕ} (h : a = b) (x : HR K a) :
    forget K b (castHR h x) = 0 ↔ forget K a x = 0 := by
  subst h
  rfl

theorem l_pos (hl0 : 1 ≤ R.l 0) (j : ℕ) : 1 ≤ R.l j := by
  induction j with
  | zero => exact hl0
  | succ j ih =>
    have := R.l_succ j
    omega

/-- **The ordinary bottom class** forget X_j is nonzero. -/
theorem forget_X_ne (hl0 : 1 ≤ R.l 0) (j : ℕ) : forget R.G (R.l j) (R.X j) ≠ 0 := by
  intro h0
  have h := congrArg (forget (R.Z (j + 1)) (R.l j)) (R.ρ_X j)
  rw [← Hmap_forget, ← Hmap_forget, h0, LinearMap.map_zero] at h
  apply (R.pattern j).forget_τ
  exact ι_injective R j (R.l j) (l_pos R hl0 j) (h.symm.trans (LinearMap.map_zero _).symm)

/-- **The ordinary class of e X_j** is nonzero. -/
theorem forget_EX_ne (j : ℕ) : forget R.G (d + 1 + R.l j) (R.E (R.l j) (R.X j)) ≠ 0 := by
  intro h0
  have h := R.ρ_EX j
  have h1 : forget (R.Z (j + 1)) (R.l j + d + 1)
      (castHR (by omega) (HRmap (R.ρ (j + 1)) (d + 1 + R.l j) (R.E (R.l j) (R.X j)))) = 0 := by
    rw [forget_castHR, ← Hmap_forget, h0, LinearMap.map_zero]
  rw [h, ← Hmap_forget] at h1
  apply (R.pattern j).forget_σ
  exact ι_injective R j (R.l j + d + 1) (by omega) (h1.trans (LinearMap.map_zero _).symm)

/-- **The ordinary middle class** of degree l_j + d: a transfer preimage of w^d X_j. -/
theorem exists_mid (j : ℕ) : ∃ z : H R.G (R.l j + d), z ≠ 0 ∧ transfer R.G (R.l j + d) z = R.B j d := by
  have hw : w R.G (R.l j + d) (R.B j d) = 0 := R.B_vanish j
  obtain ⟨z, hz⟩ := (exact_w R.G (R.l j + d) (R.B j d)).mp hw
  refine ⟨z, fun h0 => R.B_ne j d le_rfl ?_, hz⟩
  rw [← hz, h0, LinearMap.map_zero]

/-- **The ordinary top class** of degree l_j + 2d + 1: a transfer preimage of w^d (e X_j). -/
theorem exists_top (j : ℕ) :
    ∃ z : H R.G (d + 1 + R.l j + d), z ≠ 0 ∧ transfer R.G (d + 1 + R.l j + d) z = R.Tw j d := by
  have hw : w R.G (d + 1 + R.l j + d) (R.Tw j d) = 0 := R.Tw_vanish_of_le j (d + 1) le_rfl
  obtain ⟨z, hz⟩ := (exact_w R.G _ (R.Tw j d)).mp hw
  refine ⟨z, fun h0 => R.Tw_ne j d le_rfl ?_, hz⟩
  rw [← hz, h0, LinearMap.map_zero]

/-- **Nonzero ordinary classes in the four degrees of every block.** -/
theorem exists_four (hl0 : 1 ≤ R.l 0) (j : ℕ) :
    (∃ z : H R.G (R.l j), z ≠ 0) ∧ (∃ z : H R.G (R.l j + d), z ≠ 0) ∧
      (∃ z : H R.G (d + 1 + R.l j), z ≠ 0) ∧ (∃ z : H R.G (d + 1 + R.l j + d), z ≠ 0) := by
  obtain ⟨zm, hzm, -⟩ := exists_mid R j
  obtain ⟨zt, hzt, -⟩ := exists_top R j
  exact ⟨⟨_, forget_X_ne R hl0 j⟩, ⟨zm, hzm⟩, ⟨_, forget_EX_ne R j⟩, ⟨zt, hzt⟩⟩

end

end Finsler.OrdinaryBasis

namespace Finsler.OrdinaryBasisRound

open Finsler.BorelCochain Finsler.BorelLoop Finsler.RoundCrossPattern

noncomputable section

variable {n : ℕ}

/-- **The ordinary cohomology of (Λ, M) is nonzero in the degrees lc n (j+1) + {0, n−1, n, 2n−1}**
for n ≥ 3 (computed with the round filtration; it depends only on the loop space). -/
theorem exists_four (hn : 3 ≤ n) (j : ℕ) :
    (∃ z : H (fullComplex n) (lc n (j + 1)), z ≠ 0) ∧
      (∃ z : H (fullComplex n) (lc n (j + 1) + (n - 1)), z ≠ 0) ∧
      (∃ z : H (fullComplex n) ((n - 1) + 1 + lc n (j + 1)), z ≠ 0) ∧
      (∃ z : H (fullComplex n) ((n - 1) + 1 + lc n (j + 1) + (n - 1)), z ≠ 0) :=
  Finsler.OrdinaryBasis.exists_four
    (Finsler.RoundRGlobal.roundRGlobal hn (Finsler.RoundECompat.ecompat hn)
      (Finsler.RoundSupports.round_supports n)) (by
        change 1 ≤ lc n (0 + 1)
        unfold lc
        have : 2 * (0 + 1) - 1 = 1 := by norm_num
        rw [this, one_mul]
        omega) j

end

end Finsler.OrdinaryBasisRound
