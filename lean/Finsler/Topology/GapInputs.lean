module

public import Finsler.Topology.CrossingSlopes
public import Finsler.Topology.ComparisonRank

/-! The basic data of the comparison on degree gaps from its global inputs. With finitely many
prime closed geodesic images, the fields of the basic data which concern single crossings (the
vanishing of the ordinary crossing groups away from the slope lines, and of the reflection Borel
crossing groups above them) follow from the uniform bounds for single crossings. Hence the basic
data exist as soon as the global inputs are given: a power of w annihilating the global
reflection classes, a resonance slope α ≥ 0 with a margin for which the restriction from the
loop space is injective below the resonance line and zero above it, and a filling increment. The
slopes of the data are the slopes of the uniform bounds together with α, and the margin is the
larger of the two margins. -/

@[expose] public section

namespace Finsler.GapInputs

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.CriticalLevels Finsler.ComparisonRank Finsler.CrossingSlopes
open Finsler.NilpotentW

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- **The basic data from the global inputs.** -/
theorem nonempty_gapData (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {N : ℕ}
    (w_nil : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0)
    {α c₁ D a₀ : ℝ} (hα : 0 ≤ α) (hc₁ : 0 ≤ c₁) (hD : 0 ≤ D) (ha₀ : 0 < a₀)
    (fill : ∀ (a b : ℝ) (hab : a ≤ b), a₀ ≤ a → a + D ≤ b → ∀ (i : ℕ)
      (y : H (levComplex F b) i),
      ∃ x : H (fullComplex n) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y)
    (res_inj : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, c₁ < (i : ℝ) → (i : ℝ) < α * a - c₁ →
      Function.Injective (Hmap (resHom F a) i))
    (res_zero : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, α * a + c₁ < (i : ℝ) →
      ∀ x : H (fullComplex n) i, Hmap (resHom F a) i x = 0) :
    Nonempty (GapData F) := by
  classical
  obtain ⟨-, S, h0, hnn, -, hS⟩ := exists_crossing_slopes F hn hfin
  obtain ⟨c₂, hc₂, hzero, htop⟩ := hS D hD
  have hSS : S ⊆ insert α S := Finset.subset_insert α S
  exact ⟨{
    N := N
    w_nil := w_nil
    S := insert α S
    zero_mem := hSS h0
    S_nonneg := fun s hs => by
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hα
      · exact hnn s hs
    α := α
    α_mem := Finset.mem_insert_self α S
    c := max c₁ c₂
    c_nonneg := le_max_of_le_left hc₁
    D := D
    D_nonneg := hD
    a₀ := a₀
    a₀_pos := ha₀
    cross_zero := fun a a' b' hab' ha haa' hb' hac hbc hsub i hfar z =>
      hzero a a' b' hab' (ha₀.trans_le ha) haa' hb' hac hbc hsub i
        (fun s hs => lt_of_le_of_lt (le_max_right c₁ c₂) (hfar s (hSS hs))) z
    cross_top := fun a a' b' hab' _ ha' hb' hac hbc hsub i habove z =>
      htop a a' b' hab' ha' hb' hac hbc hsub i
        (fun s hs => lt_of_le_of_lt (by linarith [le_max_right c₁ c₂]) (habove s (hSS hs))) z
    fill := fill
    res_inj := fun a ha i h1 h2 => res_inj a ha i (lt_of_le_of_lt (le_max_left c₁ c₂) h1)
      (lt_of_lt_of_le h2 (by linarith [le_max_left c₁ c₂]))
    res_zero := fun a ha i h1 => res_zero a ha i
      (lt_of_le_of_lt (by linarith [le_max_left c₁ c₂]) h1) }⟩

end

end Finsler.GapInputs
