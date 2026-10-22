module

public import Finsler.Topology.EventFar
public import Finsler.Topology.GapInputs
public import Finsler.Topology.RankAssembly
public import Finsler.Topology.BasisBudget

/-! The inputs which remain for the main assertion, with the local input reduced to the windowed
localization below the lines. For one reversible metric with finitely many prime closed geodesic
images, `Inputs` collects: a global basis with its K-lifts (`BasisBudget.Data`); the windowed
localization of single crossings below the lines (`EventFar.GapLoc`); the global inputs of the
gap data, namely a power of w vanishing on the reflection Borel cohomology of the loop space,
the filling and the resonance band of ordinary restriction from the loop space; a bound for the
images of ordinary restriction from the loop space in each degree; and the detection band of
reflection Borel restriction. The local bounds of the events follow from the first local input
(`EventFar.nonempty_eventBounds_of_gap`), the gap data and the rank inputs from the global ones
(`GapInputs.nonempty_gapData`, `RankAssembly.nonempty_rankInputs`), the bound for the defect from
these (`ComparisonRank.exists_defect_le_of_data`), and with the basis and the detection band the
inputs are contradictory (`BasisBudget.false_of_basisInputs`). Hence the candidate main assertion
follows if the inputs exist for every metric with finitely many prime closed geodesic images.
The local GapLoc input is now constructed by `ActualWindowPieces.nonempty_gapLoc`.
The global inputs remain open; this legacy interface retains its original theorem types. -/

@[expose] public section

namespace Finsler.CoreLocal

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.EventSum Finsler.BasisBudget Finsler.ComparisonRank
open Finsler.EndgameAssembly Finsler.EndgameLevels Finsler.NilpotentW

noncomputable section

variable {n : ℕ}

/-- The inputs which remain: a global basis, the windowed localization of single crossings below
the lines, the global inputs of the gap data, a bound for the images of restriction from the
loop space, and the detection band. -/
structure Inputs (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) where
  basis : Data n hn
  /-- windowed localization below the lines (local Morse theory) -/
  gapLoc : Finsler.EventFar.GapLoc F hfin
  /-- a power of w vanishing on the reflection Borel cohomology of the loop space -/
  N : ℕ
  w_nil : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0
  /-- resonance slope, margins and start of the filling -/
  α : ℝ
  c₁ : ℝ
  D : ℝ
  a₀ : ℝ
  α_nonneg : 0 ≤ α
  c₁_nonneg : 0 ≤ c₁
  D_nonneg : 0 ≤ D
  a₀_pos : 0 < a₀
  fill : ∀ (a b : ℝ) (hab : a ≤ b), a₀ ≤ a → a + D ≤ b → ∀ (i : ℕ)
    (y : H (levComplex F b) i),
    ∃ x : H (fullComplex n) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y
  res_inj : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, c₁ < (i : ℝ) → (i : ℝ) < α * a - c₁ →
    Function.Injective (Hmap (resHom F a) i)
  res_zero : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, α * a + c₁ < (i : ℝ) →
    ∀ x : H (fullComplex n) i, Hmap (resHom F a) i x = 0
  /-- bounded images of ordinary restriction from the loop space -/
  res_rank : ∀ J : ℕ, ∃ G : ℕ, ∀ a : ℝ, 0 < a → ∀ i : ℕ, i ≤ J →
    finrank (ZMod 2) (LinearMap.range (Hmap (resHom F a) i)) ≤ G
  /-- detection band of reflection Borel restriction -/
  αd : ℝ
  αd_pos : 0 < αd
  C : ℝ
  q₀ : ℕ
  det_inj : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → (q : ℝ) < αd * a - C →
    Function.Injective (HRmap (resHom F a) q)
  det_zero : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → αd * a + C < (q : ℝ) →
    ∀ x, HRmap (resHom F a) q x = 0

variable {F : ReversibleMetric n} {hn : 1 ≤ n}

/-- With finitely many prime closed geodesic images, the remaining inputs give a global basis, a
bound for the defect and a detection band. -/
theorem nonempty_basisInputs (hfin : (primeImages F).Finite) (I : Inputs F hn hfin) :
    Nonempty (BasisInputs F hn) := by
  obtain ⟨E⟩ := Finsler.EventFar.nonempty_eventBounds_of_gap F hn hfin I.gapLoc
  obtain ⟨Gd⟩ := Finsler.GapInputs.nonempty_gapData F hn hfin I.w_nil I.α_nonneg I.c₁_nonneg
    I.D_nonneg I.a₀_pos I.fill I.res_inj I.res_zero
  obtain ⟨R⟩ := Finsler.RankAssembly.nonempty_rankInputs F hn hfin (a₀ := Gd.a₀) fun J => by
    obtain ⟨G, hG⟩ := I.res_rank J
    exact ⟨G, fun a ha i hi => hG a (lt_of_lt_of_le Gd.a₀_pos ha) i hi⟩
  obtain ⟨B, hB⟩ := exists_defect_le_of_data E Gd R hn hfin
  exact ⟨{ basis := I.basis
           bound := B
           defect_le := hB
           α := I.αd
           α_pos := I.αd_pos
           C := I.C
           q₀ := I.q₀
           det_inj := I.det_inj
           det_zero := I.det_zero }⟩

/-- With finitely many prime closed geodesic images, the remaining inputs are contradictory. -/
theorem false_of_inputs (h2 : 2 ≤ n) (hfin : (primeImages F).Finite) (I : Inputs F hn hfin) :
    False := by
  obtain ⟨J⟩ := nonempty_basisInputs hfin I
  exact false_of_basisInputs h2 hfin J

/-- **Reduction of the candidate main assertion to the remaining inputs**, with the local input
reduced to the windowed localization of single crossings below the lines. -/
theorem assertion_of_inputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, ∀ hfin : (primeImages F).Finite,
      Nonempty (Inputs F (le_trans (by norm_num) h3) hfin)) :
    ReversibleSphereAssertion :=
  assertion_of_basisInputs fun n h3 F hfin => by
    obtain ⟨I⟩ := h n h3 F hfin
    exact nonempty_basisInputs hfin I

end

end Finsler.CoreLocal
