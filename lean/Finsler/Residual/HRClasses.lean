module

public import Finsler.Loop.NativeGHRankOne
public import Finsler.Loop.NativeThetaRankOne
public import Finsler.Loop.NativeLoopResidueVanishing
public import Finsler.Loop.ConstantRelativeLift
public import Finsler.Topology.OrdinaryBasis
public import Finsler.Topology.ECupUnit

/-! Uniqueness of nonzero loop space classes and base classes in the four residues (Claude,
full-HR prototype).

In every degree q ≥ m the free loop space homology has rank at most one (residues 0 and 1 mod m:
`NativeGHRankOne.full_finite_rank_le_one`, `NativeThetaRankOne.full_embedding`) or vanishes
(residues 2, …, m−1: `NativeLoopResidueVanishing`). Hence two nonzero cohomology classes of the same
degree q ≥ m are equal (`coh_unique`) and a nonzero cohomology class pairs to one with every
nonzero homology class of its degree (`pair_one`). The official ordinary classes of (Λ, M)
(`OrdinaryBasisRound.exists_four`) give nonzero absolute classes in the degrees 3m, 4m, 4m+1 and
5m+1 (`base_classes`), through the singular comparison and the relative-to-absolute isomorphism. -/

@[expose] public section

namespace Finsler.HRClasses

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.BorelCochain

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

theorem exists_mul_of_mod (q : ℕ) (hq : m ≤ q) (hmq : 0 < m) :
    ∃ k : ℕ, q = (k + 1) * m + q % m := by
  have hd := Nat.mod_add_div q m
  have hpos : 0 < q / m := Nat.div_pos hq hmq
  refine ⟨q / m - 1, ?_⟩
  have h1 : q / m - 1 + 1 = q / m := by omega
  rw [h1]
  calc q = q % m + m * (q / m) := hd.symm
    _ = (q / m) * m + q % m := by rw [Nat.mul_comm]; omega

include hm P v₀ in
/-- **Rank at most one** of the loop space homology in the residues 0 and 1 mod m. -/
theorem homology_rank (q : ℕ) (hq : m ≤ q) (hres : q % m = 0 ∨ q % m = 1) :
    Module.Finite (ZMod 2) (homologyZMod2 (Loops (m + 1)) q) ∧
      Module.finrank (ZMod 2) (homologyZMod2 (Loops (m + 1)) q) ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_mul_of_mod m q hq (by omega)
  have hfull : Module.Finite (ZMod 2) (homologyZMod2 (fullPair (m + 1)).fst q) ∧
      Module.finrank (ZMod 2) (homologyZMod2 (fullPair (m + 1)).fst q) ≤ 1 := by
    rcases hres with h0 | h1
    · rw [h0, add_zero] at hk
      rw [hk]
      exact NativeGHRankOne.full_finite_rank_le_one m hm P v₀ k
    · rw [h1] at hk
      rw [hk]
      obtain ⟨f, hf⟩ := NativeThetaRankOne.full_embedding m hm P v₀ k
      have := Module.Finite.of_injective f hf
      exact ⟨this, (LinearMap.finrank_le_finrank_of_injective hf).trans_eq
        (Module.finrank_self (ZMod 2))⟩
  obtain ⟨h1, h2⟩ := hfull
  let e := NativeUnitEvaluationKernelRoute.fullHomology (m + 1) q
  exact ⟨Module.Finite.equiv e, e.finrank_eq ▸ h2⟩

theorem zmod2_cases (d : ZMod 2) : d = 0 ∨ d = 1 := by
  revert d
  decide

include hm P v₀ in
/-- A nonzero cohomology class pairs to one with every nonzero homology class (q ≥ m,
residue 0 or 1). -/
theorem pair_one (q : ℕ) (hq : m ≤ q) (hres : q % m = 0 ∨ q % m = 1)
    {x : cohomologyZMod2 (Loops (m + 1)) q} (hx : x ≠ 0)
    {z : homologyZMod2 (Loops (m + 1)) q} (hz : z ≠ 0) :
    (kroneckerMap (Loops (m + 1)) q).hom x z = 1 := by
  obtain ⟨hfin, hrank⟩ := homology_rank m hm P v₀ q hq hres
  have hk : (kroneckerMap (Loops (m + 1)) q).hom x ≠ 0 := fun h =>
    hx (kroneckerMap_injective (Loops (m + 1)) q (h.trans (map_zero _).symm))
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, (kroneckerMap (Loops (m + 1)) q).hom x z₀ ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hk (LinearMap.ext fun w => (hall w).trans (LinearMap.zero_apply w).symm)
  have hz₀ne : z₀ ≠ 0 := fun h => hz₀ (by rw [h, map_zero])
  have he : z₀ = z := Finsler.ECupUnit.eq_of_ne_zero_dim hrank hz₀ne hz
  rw [← he]
  rcases zmod2_cases ((kroneckerMap (Loops (m + 1)) q).hom x z₀) with h | h
  · exact absurd h hz₀
  · exact h

include hm P v₀ in
/-- **Two nonzero cohomology classes of the same degree q ≥ m are equal.** -/
theorem coh_unique (q : ℕ) (hq : m ≤ q) {x y : cohomologyZMod2 (Loops (m + 1)) q}
    (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  by_cases hres : q % m = 0 ∨ q % m = 1
  · apply kroneckerMap_injective (Loops (m + 1)) q
    apply LinearMap.ext
    intro z
    by_cases hz : z = 0
    · rw [hz, map_zero, map_zero]
    · rw [pair_one m hm P v₀ q hq hres hx hz, pair_one m hm P v₀ q hq hres hy hz]
  · exfalso
    apply hx
    have h2 : 2 ≤ q % m := by omega
    have hlt : q % m < m := Nat.mod_lt _ (by omega)
    have h := NativeLoopResidueVanishing.cohomology_eq_zero m (q % m) h2 hlt P v₀ (q / m)
    have hq' : q / m * m + q % m = q := by
      have hd := Nat.mod_add_div q m
      rw [Nat.mul_comm] at hd
      omega
    rw [hq'] at h
    exact h x

include P v₀ in
/-- Outside the residues 0 and 1 mod m every class vanishes. -/
theorem coh_eq_zero_of_res (q : ℕ) (hm2 : 2 ≤ m) (hres : ¬(q % m = 0 ∨ q % m = 1))
    (x : cohomologyZMod2 (Loops (m + 1)) q) : x = 0 := by
  have h2 : 2 ≤ q % m := by omega
  have hlt : q % m < m := Nat.mod_lt _ (by omega)
  have h := NativeLoopResidueVanishing.cohomology_eq_zero m (q % m) h2 hlt P v₀ (q / m)
  have hq' : q / m * m + q % m = q := by
    have hd := Nat.mod_add_div q m
    rw [Nat.mul_comm] at hd
    omega
  rw [hq'] at h
  exact h x

/-- The absolute class of an ordinary class of (Λ, M) in degree q > n + 1. -/
def toAbs (n q : ℕ) (hq : n + 1 < q) :
    H (fullComplex n) q ≃ₗ[ZMod 2] cohomologyZMod2 (Loops n) q :=
  (Finsler.BorelComparison.ordinaryEquiv (fullPair n) (revFullPair n) (revFullPair_sq n) q).trans
    (ConstantRelativeLift.equiv n q hq)

theorem exists_abs (n q : ℕ) (hq : n + 1 < q) (h : ∃ z : H (fullComplex n) q, z ≠ 0) :
    ∃ y : cohomologyZMod2 (Loops n) q, y ≠ 0 := by
  obtain ⟨z, hz⟩ := h
  exact ⟨toAbs n q hq z, fun h0 => hz ((toAbs n q hq).injective (h0.trans (map_zero _).symm))⟩

include hm in
/-- **Nonzero absolute classes in the degrees 3m, 4m, 4m + 1 and 5m + 1.** -/
theorem base_classes :
    (∃ y : cohomologyZMod2 (Loops (m + 1)) (3 * m), y ≠ 0) ∧
      (∃ y : cohomologyZMod2 (Loops (m + 1)) (4 * m), y ≠ 0) ∧
      (∃ y : cohomologyZMod2 (Loops (m + 1)) (4 * m + 1), y ≠ 0) ∧
      (∃ y : cohomologyZMod2 (Loops (m + 1)) (5 * m + 1), y ≠ 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := Finsler.OrdinaryBasisRound.exists_four (n := m + 1) (by omega) 1
  have e1 : Finsler.RoundCrossPattern.lc (m + 1) (1 + 1) = 3 * m := by
    simp only [Finsler.RoundCrossPattern.lc]
    omega
  rw [e1] at h1 h2 h3 h4
  have e2 : 3 * m + (m + 1 - 1) = 4 * m := by omega
  have e3 : m + 1 - 1 + 1 + 3 * m = 4 * m + 1 := by omega
  have e4 : m + 1 - 1 + 1 + 3 * m + (m + 1 - 1) = 5 * m + 1 := by omega
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  exact ⟨exists_abs (m + 1) _ (by omega) h1, exists_abs (m + 1) _ (by omega) h2,
    exists_abs (m + 1) _ (by omega) h3, exists_abs (m + 1) _ (by omega) h4⟩

/-- A nonzero cohomology class has a homology class pairing to one with it. -/
theorem exists_dual (X : TopCat.{0}) (q : ℕ) {y : cohomologyZMod2 X q} (hy : y ≠ 0) :
    ∃ z : homologyZMod2 X q, (kroneckerMap X q).hom y z = 1 := by
  have hk : (kroneckerMap X q).hom y ≠ 0 := fun h =>
    hy (kroneckerMap_injective X q (h.trans (map_zero _).symm))
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, (kroneckerMap X q).hom y z₀ ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hk (LinearMap.ext fun w => (hall w).trans (LinearMap.zero_apply w).symm)
  refine ⟨z₀, ?_⟩
  rcases zmod2_cases ((kroneckerMap X q).hom y z₀) with h | h
  · exact absurd h hz₀
  · exact h

end

end Finsler.HRClasses
