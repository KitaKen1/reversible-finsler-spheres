module

public import Finsler.Topology.LensK

/-! Restriction of the K-structure and of descents to an invariant subspace. For a space W with two
commuting involutions and a subset Z invariant under both, the involutions restrict to commuting
involutions of Z. A descent of a function on W whose flow keeps Z restricts to a descent of the
restricted function on Z, and it commutes with the restricted involutions if the flow commutes
with the involutions. In particular for the polygons fixed by the half rotation (`FixedSampleK`)
the lens decomposition of `LensK` applies inside the fixed subspace. If the second involution is
the identity on Z, the second involution of the cochains of a pair of subsets of Z is the
identity. -/

@[expose] public section

namespace Finsler.SubspaceK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.FlowLens Finsler.InvPairs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} (k : KAct W) {Z : Set W} (hZ : Inv k Z)

/-- The two involutions restricted to an invariant subset. -/
def subK : KAct (TopCat.of Z) where
  ρ := restrictSet k.ρ hZ.ρ_mem
  σ := restrictSet k.σ hZ.σ_mem
  ρρ x := Subtype.ext (k.ρρ x)
  σσ x := Subtype.ext (k.σσ x)
  ρσ x := Subtype.ext (k.ρσ x)

variable {g : W → ℝ} (D : Descent W g) (hDZ : ∀ t (z : W), 0 ≤ t → z ∈ Z → D.flow t z ∈ Z)

/-- The flow of a descent keeping Z, restricted to Z (for nonnegative times; the descent is
determined by them). -/
def subFlow (t : ℝ) (z : TopCat.of Z) : TopCat.of Z :=
  ⟨D.flow (max t 0) z, hDZ _ _ (le_max_right t 0) z.2⟩

/-- A descent keeping Z restricts to a descent of the restriction of the function to Z. -/
def subDescent : Descent (TopCat.of Z) (fun z => g z) where
  flow := subFlow D hDZ
  cont := by
    refine Continuous.subtype_mk ?_ _
    exact D.cont.comp ((continuous_fst.max continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd))
  zero z := Subtype.ext (by
    change D.flow (max 0 0) z = z
    rw [max_self, D.zero])
  add s t z hs ht := Subtype.ext (by
    change D.flow (max (s + t) 0) z = D.flow (max s 0) (D.flow (max t 0) z)
    rw [max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, D.add s t z hs ht])
  mono t z ht := by
    change g (D.flow (max t 0) z) ≤ g z
    exact D.mono _ _ (le_max_right t 0)

include hZ in
theorem subDescent_ρ (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w)) (t : ℝ) (z : TopCat.of Z) :
    (subDescent D hDZ).flow t ((subK k hZ).ρ z) = (subK k hZ).ρ ((subDescent D hDZ).flow t z) :=
  Subtype.ext (hDρ _ _)

include hZ in
theorem subDescent_σ (hDσ : ∀ t w, D.flow t (k.σ w) = k.σ (D.flow t w)) (t : ℝ) (z : TopCat.of Z) :
    (subDescent D hDZ).flow t ((subK k hZ).σ z) = (subK k hZ).σ ((subDescent D hDZ).flow t z) :=
  Subtype.ext (hDσ _ _)

/-- If the second involution is the identity on a pair of invariant sets, the second involution
of their cochains is the identity. -/
theorem gCommuting_trivial {X : TopCat.{0}} (k' : KAct X) {s t : Set X} (hst : s ⊆ t)
    (hs : Inv k' s) (ht : Inv k' t) (hσ : ∀ x ∈ t, k'.σ x = x) :
    ∀ j x, (gCommuting k' hst hs ht).s j x = x := by
  intro j x
  have e : restrictPair k'.σ hst hs.σ_mem ht.σ_mem = 𝟙 (pairOf hst) := by
    ext y
    · exact Subtype.ext (hσ _ (hst y.2))
    · exact Subtype.ext (hσ _ y.2)
  change ((pull (restrictPair k'.σ hst hs.σ_mem ht.σ_mem)).f j).hom x = x
  rw [e]
  exact pull_id_apply _ j x

end

end Finsler.SubspaceK
