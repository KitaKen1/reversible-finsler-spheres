module

public import Finsler.Topology.PrismShuffle

/-! The second-factor dimension alone forces a degenerate cut or output
block. This applies to every simplex in the product of the standard
input simplices, and therefore requires no enumeration of shuffle paths.
Normalization and the genuine partial cut domain are separate steps. -/

@[expose] public section
namespace Finsler.ShuffleBlockDegeneracy

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 900000

def block {N : ℕ} (a b : ℕ) (h : a + b ≤ N) : ⦋b⦌ ⟶ ⦋N⦌ :=
  SimplexCategory.Hom.mk
    (show Fin (b + 1) →o Fin (N + 1) from
    { toFun := fun i => ⟨a + i.val, by omega⟩
      monotone' := by intro i j hij; change a + i.val ≤ a + j.val; exact Nat.add_le_add_left hij a }
    )

def face {N k : ℕ} (a b : ℕ) (h : a + b ≤ N) (z : (Δ[k] : SSet.{0}) _⦋N⦌) :
    (Δ[k] : SSet.{0}) _⦋b⦌ :=
  (Δ[k] : SSet.{0}).map (block a b h).op z

private theorem strictMono_span {b : ℕ} (f : Fin (b + 1) → ℕ) (hf : StrictMono f) :
    b + f 0 ≤ f (Fin.last b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hi := ih (fun i => f i.castSucc) (hf.comp Fin.strictMono_castSucc)
    have hs := hf (show (Fin.last b).castSucc < (Fin.last b).succ from Fin.castSucc_lt_succ)
    change b + f 0 ≤ f (Fin.last b).castSucc at hi
    change f (Fin.last b).castSucc < f (Fin.last (b + 1)) at hs
    omega

theorem cut_or_output_degenerate (j k a b c d : ℕ)
    (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (z : (Δ[k] : SSet.{0}) _⦋a + b + c + d⦌) :
    face a b (by omega) z ∈ (Δ[k] : SSet.{0}).degenerate b ∨
      face (a + b + c) d (by omega) z ∈ (Δ[k] : SSet.{0}).degenerate d := by
  by_contra hn
  push_neg at hn
  have hb := (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mp hn.1
  have hd := (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mp hn.2
  have hb' := strictMono_span (fun i => (face a b (by omega) z i).val)
    (Fin.val_strictMono.comp hb)
  have hd' := strictMono_span (fun i => (face (a + b + c) d (by omega) z i).val)
    (Fin.val_strictMono.comp hd)
  change b + (z ⟨a, by omega⟩).val ≤ (z ⟨a + b, by omega⟩).val at hb'
  change d + (z ⟨a + b + c, by omega⟩).val ≤
    (z ⟨a + b + c + d, by omega⟩).val at hd'
  have hm := SSet.stdSimplex.monotone_apply z
    (show (⟨a + b, by omega⟩ : Fin (a + b + c + d + 1)) ≤ ⟨a + b + c, by omega⟩ by
      change a + b ≤ a + b + c; omega)
  have hlast := (z ⟨a + b + c + d, by omega⟩).isLt
  change (z ⟨a + b, by omega⟩).val ≤ (z ⟨a + b + c, by omega⟩).val at hm
  omega

theorem product_cut_or_output_degenerate (j k a b c d : ℕ)
    (htotal : j + k = a + b + c + d) (hdegree : a + c < j)
    (z : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) _⦋a + b + c + d⦌) :
    face a b (by omega) z.2 ∈ (Δ[k] : SSet.{0}).degenerate b ∨
      face (a + b + c) d (by omega) z.2 ∈ (Δ[k] : SSet.{0}).degenerate d :=
  cut_or_output_degenerate j k a b c d htotal hdegree z.2

end
end Finsler.ShuffleBlockDegeneracy
