module

public import Finsler.Topology.LensLabels
public import Finsler.Topology.CutMove

/-! Lens pairs depend only on their core. For a continuous function with a descent, cuts
a' < a ≤ b and a time T, the lens pair in a set 𝒲 is an excision of its piece, the part of 𝒲
below b whose points the flow does not take to energy at most a' in time T (v0.108). If two
sets 𝒲 and 𝒲' contain the same points below b which are not taken to energy at most a' in time
T, the two pieces are the same sets, so the lens pairs in 𝒲 and 𝒲' have isomorphic cohomology.
This lets a label set be shrunk to a bounded set or enlarged to all fibres over a base set. -/

@[expose] public section

namespace Finsler.LensCore

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens
open Finsler.LensContinuation Finsler.LensLabels Finsler.CutMove Finsler.PairAdditive

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) {a' a b T : ℝ}

/-- **Lens pairs with the same core.** -/
theorem nonempty_core_equiv (hg : Continuous g) (ha : a' < a) {𝒲 𝒲' : Set W}
    (hcore : ∀ w, g w < b → a' < g (D.flow T w) → (w ∈ 𝒲 ↔ w ∈ 𝒲')) (n : ℕ) :
    Nonempty (H (triv (pairOf (partY_sub_partU g D 𝒲 a b T))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU g D 𝒲' a b T))) n) := by
  have hU : (lensN D a' T ∩ sub g b) ∩ 𝒲 = (lensN D a' T ∩ sub g b) ∩ 𝒲' := by
    ext w
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2 h1).mp h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2 h1).mpr h3⟩
  have hY : (lensN D a' T ∩ lensY D a b T) ∩ 𝒲 = (lensN D a' T ∩ lensY D a b T) ∩ 𝒲' := by
    ext w
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2.1 h1).mp h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (hcore w h2.1 h1).mpr h3⟩
  have hb1 := piece_bijective D (b := b) (T := T) hg ha 𝒲 n
  have hb2 := piece_bijective D (b := b) (T := T) hg ha 𝒲' n
  have hb3 := eq_bijective
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
    (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲') hY hU n
  exact ⟨((LinearEquiv.ofBijective _ hb1).trans (LinearEquiv.ofBijective _ hb3).symm).trans
    (LinearEquiv.ofBijective _ hb2).symm⟩

end

end Finsler.LensCore
