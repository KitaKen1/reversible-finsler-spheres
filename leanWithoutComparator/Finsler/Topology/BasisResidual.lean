module

public import Finsler.Geometry.RoundYTop
public import Finsler.Topology.CoreResidual

/-! The residual inputs of the main assertion after the global basis.

The global basis of the reflection Borel cohomology of the loop space pair with its K-lifts
(`RoundYTop.stage13`) and w^n = 0 (`RoundYTop.basis_w_nil`) are proved for every
n ≥ 3; they depend only on the topology of the loop space, computed with the round metric. Hence
the inputs `CoreResidual.Inputs` of a metric reduce to the filling bound and the ordinary resonance
bands (`FillRes`), and the main assertion follows as soon as every metric with finitely many prime
closed geodesic images has these two inputs. -/

@[expose] public section

namespace Finsler.BasisResidual

open Set Module Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.BasisBudget Finsler.NilpotentW

noncomputable section

variable {n : ℕ}

/-- The filling bound and the ordinary resonance bands of a metric: the inputs of
`CoreResidual.Inputs` other than the global basis and w-nilpotence. -/
structure FillRes (F : ReversibleMetric n) where
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

/-- The inputs of a metric from its filling bound and resonance bands. -/
def inputs (hn : 3 ≤ n) (F : ReversibleMetric n) (R : FillRes F) :
    Finsler.CoreResidual.Inputs F (le_trans (by norm_num) hn) where
  basis := Finsler.RoundYTop.stage13 hn
  N := n
  w_nil := Finsler.RoundYTop.basis_w_nil hn
  α := R.α
  c₁ := R.c₁
  D := R.D
  a₀ := R.a₀
  α_pos := R.α_pos
  c₁_nonneg := R.c₁_nonneg
  D_nonneg := R.D_nonneg
  a₀_pos := R.a₀_pos
  fill := R.fill
  res_inj := R.res_inj
  res_zero := R.res_zero

theorem nonempty_inputs (hn : 3 ≤ n) (F : ReversibleMetric n) (R : FillRes F) :
    Nonempty (Finsler.CoreResidual.Inputs F (le_trans (by norm_num) hn)) :=
  ⟨inputs hn F R⟩

/-- **The main assertion from the filling bound and the ordinary resonance bands** of the
metrics with finitely many prime closed geodesic images. -/
theorem assertion_of_fillRes
    (h : ∀ n : ℕ, ∀ hn : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (FillRes F)) : ReversibleSphereAssertion :=
  Finsler.CoreResidual.assertion_of_inputs fun n hn F hfin => by
    obtain ⟨R⟩ := h n hn F hfin
    exact nonempty_inputs hn F R

end

end Finsler.BasisResidual
