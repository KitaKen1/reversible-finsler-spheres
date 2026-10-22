module

public import Finsler.Topology.InvPairs
public import Finsler.Topology.BorelFree

/-! Reflection Borel windows from ordinary windows. By the Gysin sequence, the reflection Borel
cohomology of an involutive complex vanishes in a degree in which w vanishes and the cohomology
of the complex vanishes (every class killed by w is a transfer). If the involution of a pair
exchanges a closed and open set of the space with its complement, w vanishes (`BorelFree`), so the
reflection Borel cohomology of the pair vanishes in every degree in which its actual relative
cohomology does. For pairs of invariant sets this applies when the reversal exchanges the parts
of the pair inside and outside an open set U, for instance when the pair lies in a neighbourhood
of an orbit of critical circles whose two halves (the neighbourhoods of the positive and of the
negative circle) are exchanged by the reversal: the windows of the parts reduce to windows of
their ordinary cohomology. -/

@[expose] public section

namespace Finsler.SwapWindows

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelComparison
open Finsler.BorelFree Finsler.InvPairs Finsler.BorelDeformation Finsler.BorelLoop

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Where w vanishes, reflection Borel cohomology vanishes if the cohomology of the complex
does. -/
theorem HR_eq_zero_of_w {K : InvComplex} {q : ℕ} (hw : ∀ y : HR K q, w K q y = 0)
    (hH : ∀ z : H K q, z = 0) (x : HR K q) : x = 0 := by
  obtain ⟨z, rfl⟩ := (exact_w K q x).mp (hw x)
  rw [hH z, map_zero]

/-- If the involution of a pair exchanges a closed and open set of the space with its
complement, the reflection Borel cohomology vanishes in every degree in which the actual relative
cohomology does. -/
theorem HR_ofPair_eq_zero (P : TopPair.{0}) (r : P ⟶ P) (hr : r ≫ r = 𝟙 P) (U : Set P.fst)
    (hU : IsClopen U) (hswap : ∀ x : P.fst, (TopPair.Hom.fst r).hom x ∈ U ↔ x ∉ U) {q : ℕ}
    (hq : ∀ z : native P q, z = 0) (x : HR (ofPair P r hr) q) : x = 0 :=
  HR_eq_zero_of_w (fun y => w_eq_zero_of_isClopen P r hr U hU hswap q y)
    (fun _ => (ordinaryEquiv P r hr q).map_eq_zero_iff.mp (hq _)) x

/-- **Windows of pairs of invariant sets exchanged around an open set.** If the reversal
exchanges the points of t inside and outside an open set U, the reflection Borel cohomology of
the pair (t, s) vanishes in every degree in which its actual relative cohomology does. -/
theorem HR_gComplex_eq_zero {X : TopCat.{0}} (k : KAct X) {s t : Set X} (hst : s ⊆ t)
    (hs : Inv k s) (ht : Inv k t) {U : Set X} (hU : IsOpen U)
    (hswap : ∀ x ∈ t, k.ρ x ∈ U ↔ x ∉ U) {q : ℕ} (hq : ∀ z : native (pairOf hst) q, z = 0)
    (x : HR (gComplex k hst hs ht) q) : x = 0 := by
  have e : (Subtype.val ⁻¹' U : Set ↥t)ᶜ = (fun y : ↥t => k.ρ y.1) ⁻¹' U := by
    ext y
    exact (hswap y.1 y.2).symm
  refine HR_ofPair_eq_zero (pairOf hst) (restrictPair k.ρ hst hs.ρ_mem ht.ρ_mem) _
    (Subtype.val ⁻¹' U : Set ↥t) ⟨?_, hU.preimage continuous_subtype_val⟩
    (fun y => hswap y.1 y.2) hq x
  rw [← isOpen_compl_iff, e]
  exact hU.preimage (k.ρ.continuous.comp continuous_subtype_val)

end

end Finsler.SwapWindows
