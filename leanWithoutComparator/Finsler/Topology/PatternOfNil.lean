module

public import Finsler.Topology.GysinPattern

/-! Patterns of crossing groups from w-nilpotence.

If the ordinary cohomology of an involutive complex P vanishes above a degree Q₀, forgetting is
zero in the degrees above Q₀, so every Borel class of degree Q₀ + j is w^j of a class of degree
Q₀ (walk down with the Gysin sequence). Hence a vanishing power w^k forces the Borel cohomology to
vanish in degree Q₀ + k. This is the vanishing hypothesis of `patternOfVanishing`.

The first start class needs no geometric construction: below the lowest degree l of ordinary
cohomology the Borel cohomology vanishes, so forgetting is injective in degree l; a nonzero
ordinary class z of degree l is then either a forgetful image (if its transfer vanishes) or its
transfer is a Borel class with nonzero forgetful image. -/

@[expose] public section

namespace Finsler.PatternOfNil

open Finsler.BorelCochain Finsler.NilpotentW Finsler.GysinPattern Module

noncomputable section

variable {P : InvComplex}

/-- Above a degree where ordinary cohomology vanishes, every Borel class is w^j of a class of
that degree. -/
theorem exists_wPow_preimage {Q₀ : ℕ} (hH : ∀ q, Q₀ < q → ∀ z : H P q, z = 0) :
    ∀ (j : ℕ) (x : HR P (Q₀ + j)), ∃ y : HR P Q₀, wPow P Q₀ j y = x
  | 0, x => ⟨x, rfl⟩
  | j + 1, x => by
    obtain ⟨x', hx'⟩ := (exact_forget P (Q₀ + j) x).mp (hH _ (by omega) _)
    obtain ⟨y, rfl⟩ := exists_wPow_preimage hH j x'
    exact ⟨y, by rw [wPow_succ]; exact hx'⟩

/-- A vanishing power of w kills the Borel cohomology k degrees above the ordinary cohomology. -/
theorem HR_zero_of_wPow {k : ℕ} (hk : ∀ q (x : HR P q), wPow P q k x = 0) {Q₀ : ℕ}
    (hH : ∀ q, Q₀ < q → ∀ z : H P q, z = 0) (x : HR P (Q₀ + k)) : x = 0 := by
  obtain ⟨y, rfl⟩ := exists_wPow_preimage hH k x
  exact hk Q₀ y

/-- The first start class: a nonzero ordinary class in the lowest degree gives a Borel class
with nonzero forgetful image. -/
theorem exists_start {l : ℕ} (hbelow : ∀ q, q < l → ∀ z : H P q, z = 0)
    (hl : ∃ z : H P l, z ≠ 0) : ∃ τ : HR P l, forget P l τ ≠ 0 := by
  obtain ⟨z, hz⟩ := hl
  by_cases ht : transfer P l z = 0
  · obtain ⟨y, hy⟩ := (exact_transfer P l z).mp ht
    exact ⟨y, by rw [hy]; exact hz⟩
  · refine ⟨transfer P l z, fun h0 => ht ?_⟩
    cases l with
    | zero => exact BorelQuasiIso.forget_zero_injective P (h0.trans (map_zero _).symm)
    | succ l =>
      obtain ⟨y, hy⟩ := (exact_forget P l _).mp h0
      rw [← hy, HR_zero_below hbelow l (by omega) y, map_zero]

/-- **The pattern of a crossing from w-nilpotence.** Ordinary cohomology of dimension at most
one in the four degrees l, l + d, l + d + 1, l + 2d + 1, two start classes and a vanishing power
of w give the two towers. -/
def patternOfNil {l d k : ℕ} (hd : 1 ≤ d) (hfin : ∀ q, FiniteDimensional (ZMod 2) (H P q))
    (hdim : ∀ q, finrank (ZMod 2) (H P q) ≤ 1)
    (hsupp : ∀ q, q ≠ l → q ≠ l + d → q ≠ l + d + 1 → q ≠ l + d + 1 + d → ∀ z : H P q, z = 0)
    (τ : HR P l) (hτ : forget P l τ ≠ 0) (σ : HR P (l + d + 1))
    (hσ : forget P (l + d + 1) σ ≠ 0) (hk : ∀ q (x : HR P q), wPow P q k x = 0) :
    Pattern P l d :=
  patternOfVanishing hd hfin hdim hsupp τ hτ σ hσ (Q := l + d + 1 + d + (k + 1)) (by omega)
    (HR_zero_of_wPow (fun q x => by rw [wPow_succ, hk q x, map_zero])
      (fun q hq => hsupp q (by omega) (by omega) (by omega) (by omega)))

end

end Finsler.PatternOfNil
