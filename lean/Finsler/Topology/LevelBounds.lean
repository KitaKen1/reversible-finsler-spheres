module

public import Finsler.Topology.LoopLabels
public import Finsler.Topology.OrdinaryRank
public import Finsler.Topology.BorelComparison

/-! Finite ordinary crossings. For a short exact sequence of involutive complexes the ordinary
cohomology map of the subcomplex in degree zero is injective. With finitely many prime closed
geodesic images, for regular cuts 0 < a ≤ b the ordinary cohomology of the crossing pair
(t_b, t_a) is finite dimensional in every degree and vanishes in high degrees (the short exact
sequence of the triple (t_b, t_a, M) and the finiteness of the ordinary cohomology of (t_a, M)
at regular cuts). The ends of the chosen isolated band around a positive level are regular. -/

@[expose] public section

namespace Finsler.LevelBounds

open Module Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CircleLabel
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelExact Finsler.BorelCrossing

noncomputable section

section Algebra

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''}

/-- The ordinary cohomology map of the subcomplex is injective in degree zero. -/
theorem Hmap_zero_injective (h : ShortExact ι π) : Function.Injective (Hmap ι 0) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  have hz' : ι.f 0 (c : K'.C 0) ∈ (⊥ : Submodule (ZMod 2) (K.C 0)) := hz
  rw [Submodule.mem_bot] at hz'
  have hc : (c : K'.C 0) = 0 := h.inj 0 (by rw [hz', map_zero])
  rw [Submodule.Quotient.mk_eq_zero]
  change (c : K'.C 0) ∈ (⊥ : Submodule (ZMod 2) (K'.C 0))
  rw [hc]
  exact zero_mem _

/-- The ordinary cohomology of the cochains of a pair does not depend on the involution: both
are the native cohomology of the pair. -/
def ofPairEquiv (P : TopPair.{0}) {r₁ r₂ : P ⟶ P} (h₁ : r₁ ≫ r₁ = 𝟙 P) (h₂ : r₂ ≫ r₂ = 𝟙 P)
    (q : ℕ) : H (ofPair P r₁ h₁) q ≃ₗ[ZMod 2] H (ofPair P r₂ h₂) q :=
  (Finsler.BorelComparison.ordinaryEquiv P r₁ h₁ q).trans
    (Finsler.BorelComparison.ordinaryEquiv P r₂ h₂ q).symm

end Algebra

variable {n : ℕ} (F : ReversibleMetric n)

/-- **Finite ordinary crossings.** -/
theorem cross_finite (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) :
    ∃ D : ℕ, (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q)) ∧
      ∀ q, D ≤ q → ∀ x : H (triv (pairOf (lev_mono F hab))) q, x = 0 := by
  obtain ⟨ka, hfa, hza⟩ := Finsler.FiniteCut.exists_finite_H F hn hfin ha hac
  obtain ⟨kb, hfb, hzb⟩ := Finsler.FiniteCut.exists_finite_H F hn hfin (ha.trans_le hab) hbc
  have hse := shortExact F hab
  have hfc : ∀ q, Module.Finite (ZMod 2) (H (crossComplex F hab) q) := by
    intro q
    cases q with
    | zero =>
      have := hfb 0
      exact Module.Finite.of_injective (Hmap (relHom F hab) 0) (Hmap_zero_injective hse)
    | succ q =>
      have := hfa q
      have := hfb (q + 1)
      exact Finsler.OrdinaryDelta.finite_sub hse q
  have hzc : ∀ q, max ka kb + 1 ≤ q → ∀ x : H (crossComplex F hab) q, x = 0 := by
    intro q hq x
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h1 : Hmap (relHom F hab) (q' + 1) x = 0 :=
      hzb (q' + 1) (by have := le_max_right ka kb; omega) _
    obtain ⟨y, hy⟩ := Finsler.OrdinaryDelta.exact_sub hse q' x h1
    have hy0 : y = 0 := hza q' (by have := le_max_left ka kb; omega) y
    rw [hy0, map_zero] at hy
    exact hy.symm
  refine ⟨max ka kb + 1, fun q => ?_, fun q hq x => ?_⟩
  · have := hfc q
    exact Module.Finite.equiv (ofPairEquiv (crossPair F hab) (revCross_sq F hab)
      (Category.comp_id _) q)
  · have e := ofPairEquiv (crossPair F hab) (revCross_sq F hab) (Category.comp_id _) q
    have h := hzc q hq (e.symm x)
    rw [← e.apply_symm_apply x, h, map_zero]

/-- The ends of the chosen isolated band around a positive level are regular. -/
theorem isoBand_regular (hfin : (primeImages F).Finite) {x : ℝ} (hx : 0 < x) :
    (isoBand F hfin x).1 ∉ crit F ∧ (isoBand F hfin x).2 ∉ crit F := by
  obtain ⟨h0, h1, h2, h3⟩ := isoBand_spec F hfin hx
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h3 _ h le_rfl (h1.trans h2).le
    linarith
  · have := h3 _ h (h1.trans h2).le le_rfl
    linarith

end

end Finsler.LevelBounds
