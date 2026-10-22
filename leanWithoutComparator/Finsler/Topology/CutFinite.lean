module

public import Finsler.Topology.CutPotential

/-! Finite dimensionality of the fixed and crossing groups at regular cuts, and the invariance of
the potential on intervals without critical levels. With finitely many prime closed geodesic
images, at a regular cut 2a the reflection Borel cohomology of the fixed pair of t_{2a} is finite
dimensional and vanishes in high degrees, since doubling identifies it with that of (t_a, M).
For regular cuts 2a ≤ 2b the K-Borel cohomology of the crossing pair (t_{2b}, t_{2a}) and the
reflection Borel cohomology of the fixed crossing pair are finite dimensional, by the exact
sequences of the triples. If there is no critical level in [2a, 2b], restriction from 2b to 2a is
bijective on the K-Borel cohomology and on the reflection Borel cohomology of the fixed pairs
(through doubling and the interval [a, b]); so both crossing groups vanish and the potential of
every cutoff is the same at 2a and at 2b. -/

@[expose] public section

namespace Finsler.CutFinite

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.SobolevEnergy Finsler.SobolevReflectionAction
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed Finsler.BorelExact
open Finsler.BorelFreeK Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK
open Finsler.BorelCoverK Finsler.LocalCoverK Finsler.TotalExact Finsler.GradedLadder
open Finsler.FixedLadder Finsler.LadderEvent Finsler.CutPotential
open Finsler.CriticalLevels Finsler.FiniteCut Finsler.LocalizeK Finsler.TameHomology
open Finsler.RegularInterval

noncomputable section

/-! ### Subcomplexes of short exact sequences -/

section Exact

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

include h in
/-- The Borel cohomology of the subcomplex is finite dimensional in a degree if that of the
quotient complex is in all degrees and that of the middle complex in this degree. -/
theorem finite_sub (q : ℕ) (hK'' : ∀ p, Module.Finite (ZMod 2) (HR K'' p))
    (hK : Module.Finite (ZMod 2) (HR K q)) : Module.Finite (ZMod 2) (HR K' q) := by
  cases q with
  | zero => exact Module.Finite.of_injective (HRmap ι 0) (injective_zero h)
  | succ q =>
    have := hK'' q
    exact finite_of_exact_linear (delta h q) (HRmap ι (q + 1)) fun y hy => exact_sub h q y hy

include h in
/-- If the map to the quotient complex is bijective on Borel cohomology in all degrees, the Borel
cohomology of the subcomplex vanishes. -/
theorem sub_eq_zero_of_bijective (hbij : ∀ q, Function.Bijective (HRmap π q)) (q : ℕ)
    (y : HR K' q) : y = 0 := by
  cases q with
  | zero =>
    apply injective_zero h
    rw [map_zero]
    exact (hbij 0).1 ((comp_zero h 0 y).trans (map_zero (HRmap π 0)).symm)
  | succ q =>
    have h1 : HRmap ι (q + 1) y = 0 :=
      (hbij (q + 1)).1 ((comp_zero h (q + 1) y).trans (map_zero (HRmap π (q + 1))).symm)
    obtain ⟨x, rfl⟩ := exact_sub h q y h1
    obtain ⟨z, rfl⟩ := (hbij q).2 x
    exact delta_comp_zero h q z

include h in
/-- If the Borel cohomology of the middle complex vanishes in a degree and that of the quotient
complex in the preceding degrees, that of the subcomplex vanishes in this degree. -/
theorem sub_eq_zero_of_zero (q : ℕ) (hK : ∀ x : HR K q, x = 0)
    (hK'' : ∀ p, p + 1 = q → ∀ x : HR K'' p, x = 0) (y : HR K' q) : y = 0 := by
  cases q with
  | zero =>
    apply injective_zero h
    rw [map_zero]
    exact hK _
  | succ q =>
    obtain ⟨x, rfl⟩ := exact_sub h q y (hK _)
    rw [hK'' q rfl x, map_zero]

end Exact

variable {n : ℕ} (F : ReversibleMetric n)

/-! ### The fixed pair of a regular cut -/

/-- With finitely many prime closed geodesic images, at a regular cut 2a the reflection Borel
cohomology of the fixed pair is finite dimensional in every degree and vanishes in high
degrees. -/
theorem exists_fixR_finite (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, (∀ l, Module.Finite (ZMod 2) (fixR F (2 * a) l)) ∧
      ∀ l, Q ≤ l → ∀ x : fixR F (2 * a) l, x = 0 := by
  have hac : a ∉ crit F := fun h => h2a (crit_double F h)
  obtain ⟨Q, hfinR, hz⟩ := exists_finite_HR F hn hfin ha hac
  refine ⟨Q, fun l => ?_, fun l hl x => HR_fix_eq_zero F hz l hl x⟩
  have := hfinR l
  exact Module.Finite.equiv (doublingEquiv F a l)

/-- The product over all root degrees of the reflection Borel cohomology of the fixed pair of a
regular cut 2a is finite dimensional. -/
theorem finTot_fixR (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) : FinTot (fixR F (2 * a)) := by
  obtain ⟨Q, hf, hz⟩ := exists_fixR_finite F hn hfin ha h2a
  have := hf
  exact finTot_of_vanish (fixR F (2 * a)) hz

/-! ### The crossing groups of two regular cuts -/

/-- The K-Borel cohomology of the crossing pair of two regular cuts is finite dimensional. -/
theorem finite_crossK (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (hxc : x ∉ crit F) (hyc : y ∉ crit F) (q : ℕ) :
    Module.Finite (ZMod 2) (crossK F hxy q) :=
  finite_sub (shortExactK (consts_subset_lev F x) (lev_mono F hxy) kInv_consts (kInv_lev F x)
    (kInv_lev F y)) q (fun p => finite_HK F hn hfin hx hxc p)
    (finite_HK F hn hfin (hx.trans_le hxy) hyc q)

/-- The reflection Borel cohomology of the fixed crossing pair of two regular cuts 2a ≤ 2b is
finite dimensional in every degree and vanishes in high degrees. -/
theorem exists_crossR_finite (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F) :
    ∃ Q : ℕ, (∀ l, Module.Finite (ZMod 2) (crossR F hab l)) ∧
      ∀ l, Q ≤ l → ∀ x : crossR F hab l, x = 0 := by
  have hb : 0 < b := by linarith
  obtain ⟨Q₁, hf₁, hz₁⟩ := exists_fixR_finite F hn hfin ha h2a
  obtain ⟨Q₂, hf₂, hz₂⟩ := exists_fixR_finite F hn hfin hb h2b
  refine ⟨max Q₁ Q₂ + 1, fun l => ?_, fun l hl x => ?_⟩
  · exact finite_sub (shortExact_incl (consts_subset_fixLev F (2 * a)) (fixLev_mono F hab)
      kInv_consts (kInv_fixLev F (2 * a)) (kInv_fixLev F (2 * b))) l hf₁ (hf₂ l)
  · exact sub_eq_zero_of_zero (shortExact_incl (consts_subset_fixLev F (2 * a))
      (fixLev_mono F hab) kInv_consts (kInv_fixLev F (2 * a)) (kInv_fixLev F (2 * b))) l
      (fun z => hz₂ l (by omega) z) (fun p hp z => hz₁ p (by omega) z) x

/-- The product over all root degrees of the reflection Borel cohomology of the fixed crossing
pair of two regular cuts is finite dimensional. -/
theorem finTot_crossR (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F) :
    FinTot (crossR F hab) := by
  obtain ⟨Q, hf, hz⟩ := exists_crossR_finite F hn hfin ha hab h2a h2b
  have := hf
  exact finTot_of_vanish (crossR F hab) hz

end

end Finsler.CutFinite
