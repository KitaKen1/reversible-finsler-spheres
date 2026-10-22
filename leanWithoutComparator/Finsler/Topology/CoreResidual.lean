module

public import Finsler.Topology.CoreLocal
public import Finsler.Topology.ActualWindowPieces
public import Finsler.Topology.BasisRank
public import Finsler.Topology.GlobalDetection

/-! Local events, restriction-rank bounds and detection are
constructed. Only the actual global basis, nilpotence, filling and positive resonance remain. -/

@[expose] public section

namespace Finsler.CoreResidual

open Set Module Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.BasisBudget Finsler.NilpotentW

noncomputable section

variable {n : ℕ}

structure Inputs (F : ReversibleMetric n) (hn : 1 ≤ n) where
  basis : Data n hn
  /-- a power of w vanishing on the reflection Borel cohomology of the loop space -/
  N : ℕ
  w_nil : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0
  /-- resonance slope, margins and start of the filling -/
  α : ℝ
  c₁ : ℝ
  D : ℝ
  a₀ : ℝ
  α_pos : 0 < α
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


theorem nonempty_coreLocal {F : ReversibleMetric n} {hn : 1 ≤ n}
    (hfin : (primeImages F).Finite) (I : Inputs F hn) :
    Nonempty (Finsler.CoreLocal.Inputs F hn hfin) := by
  obtain ⟨L⟩ := Finsler.ActualWindowPieces.nonempty_gapLoc F hn hfin
  obtain ⟨C, q₀, hdi, hdz⟩ := Finsler.GlobalDetection.exists_detection F I.w_nil
    I.a₀_pos I.α_pos.le I.c₁_nonneg I.D_nonneg I.fill I.res_inj I.res_zero
  exact ⟨{
    basis := I.basis
    gapLoc := L
    N := I.N
    w_nil := I.w_nil
    α := I.α
    c₁ := I.c₁
    D := I.D
    a₀ := I.a₀
    α_nonneg := I.α_pos.le
    c₁_nonneg := I.c₁_nonneg
    D_nonneg := I.D_nonneg
    a₀_pos := I.a₀_pos
    fill := I.fill
    res_inj := I.res_inj
    res_zero := I.res_zero
    res_rank := fun J => ⟨4, fun a _ i _ => Finsler.BasisRank.restriction_rank I.basis F a i⟩
    αd := I.α
    αd_pos := I.α_pos
    C := C
    q₀ := q₀
    det_inj := hdi
    det_zero := hdz }⟩

theorem false_of_inputs {F : ReversibleMetric n} {hn : 1 ≤ n} (h2 : 2 ≤ n)
    (hfin : (primeImages F).Finite) (I : Inputs F hn) : False := by
  obtain ⟨J⟩ := nonempty_coreLocal hfin I
  exact Finsler.CoreLocal.false_of_inputs h2 hfin J

theorem assertion_of_inputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, ∀ hfin : (primeImages F).Finite,
      Nonempty (Inputs F (le_trans (by norm_num) h3))) : ReversibleSphereAssertion :=
  Finsler.CoreLocal.assertion_of_inputs fun n h3 F hfin => by
    obtain ⟨I⟩ := h n h3 F hfin
    exact nonempty_coreLocal hfin I

end

end Finsler.CoreResidual
