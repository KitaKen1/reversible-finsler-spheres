module

public import Finsler.Loop.ShuffleWordSimplex
public import Finsler.Loop.NormalizedPrismCapFront

/-! Any word without the full initial horizontal cap block has a
degenerate first-factor front. This includes short words and requires
no enumeration of the positions of vertical steps. -/

@[expose] public section
namespace Finsler.ShuffleWordCapFront

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ShuffleWords Finsler.ShuffleWordSimplex
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

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

private theorem eq_replicate_of_horizontal_eq_length (w : List Bool)
    (hw : horizontal w = w.length) : w = List.replicate w.length false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false =>
      simp only [horizontal, List.length_cons] at hw
      have he := ih (by omega)
      simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons false) he
    | true =>
      have hl := counts_length w
      simp only [horizontal, List.length_cons] at hw
      omega

def front (p N a : ℕ) (ha : a ≤ N) (w : List Bool) : (Δ[p] : SSet.{0}) _⦋a⦌ :=
  (Δ[p] : SSet.{0}).map (SimplexCategory.subinterval 0 a (by omega)).op (simplex p 0 N w).1

theorem front_degenerate (p N a : ℕ) (ha : a ≤ N) (w : List Bool)
    (hw : w.take a ≠ List.replicate a false) :
    front p N a ha w ∈ (Δ[p] : SSet.{0}).degenerate a := by
  by_contra hn
  have hs := (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mp hn
  have hspan := strictMono_span (fun i => (front p N a ha w i).val) (Fin.val_strictMono.comp hs)
  have hlast : (front p N a ha w (Fin.last a)).val = min (horizontal (w.take a)) p := by
    change min (horizontal (w.take (a + 0))) p = min (horizontal (w.take a)) p
    rw [Nat.add_zero]
  rw [hlast] at hspan
  have hc := counts_length (w.take a)
  have hl : (w.take a).length ≤ a := by simp only [List.length_take]; omega
  have hlen : (w.take a).length = a := by omega
  have he := eq_replicate_of_horizontal_eq_length (w.take a) (by omega)
  rw [hlen] at he
  exact hw he

theorem normalized_front_zero (p N a : ℕ) (ha : a ≤ N) (w : List Bool)
    (hw : w.take a ≠ List.replicate a false) (X : TopCat.{0})
    (g : (Δ[p] : SSet.{0}) ⟶ TopCat.toSSet.obj X)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    (TopCat.toSSet.obj X).ιChainComplex (g.app _ (front p N a ha w)) ≫ φ = 0 := by
  rw [← NormalizedPrismCapFront.normalize_eq X a φ hφ]
  exact ShuffleBlockNormalization.normalize_simplex_zero X a φ _
    (ShuffleBlockNormalization.map_degenerate g _ (front_degenerate p N a ha w hw))

end
end Finsler.ShuffleWordCapFront
