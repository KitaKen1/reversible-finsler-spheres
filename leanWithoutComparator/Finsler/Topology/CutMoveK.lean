module

public import Finsler.Topology.CutMove
public import Finsler.Topology.LensK

/-! K-Borel cut moves through the actual inclusion maps.
Ordinary deformation isomorphisms and the existing K comparison principle suffice. -/

@[expose] public section

namespace Finsler.CutMoveK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.FlowLens Finsler.InvPairs
open Finsler.LensK Finsler.CutMove Finsler.PairTriple
open Finsler.LensFamily

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} (k : KAct W) {g : W → ℝ}
variable (hgρ : ∀ w, g (k.ρ w) = g w) (hgσ : ∀ w, g (k.σ w) = g w)
variable (D : Descent W g)

/-- Moving the lower cut induces an isomorphism on actual K-Borel cohomology. -/
theorem lower_bijective {a a' b s₀ : ℝ} (haa : a ≤ a') (hab : a' ≤ b) (hs₀ : 0 ≤ s₀)
    (hpush : ∀ w, g w < a' → g (D.flow s₀ w) < a) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      (sub_mono g (haa.trans hab)) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b)
      (sub_mono g hab) (inv_sub k hgρ hgσ a') (inv_sub k hgρ hgσ b)
      (sub_mono g haa) subset_rfl)) q) := by
  apply bijective_gHom k _ _ _ _ _ _ _ _
  intro m
  exact nativePull_bijective_of_Hmap _ m (Finsler.CutMove.lower_bijective D haa hab hs₀ hpush m)

/-- Moving the upper cut induces an isomorphism on actual K-Borel cohomology. -/
theorem upper_bijective {a b b' s₀ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hs₀ : 0 ≤ s₀)
    (hpush : ∀ w, g w < b' → g (D.flow s₀ w) < b) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      (sub_mono g hab) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b)
      (sub_mono g (hab.trans hbb)) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b')
      subset_rfl (sub_mono g hbb))) q) := by
  apply bijective_gHom k _ _ _ _ _ _ _ _
  intro m
  exact nativePull_bijective_of_Hmap _ m (Finsler.CutMove.upper_bijective D hab hbb hs₀ hpush m)

omit hgρ hgσ D in
/-- Equality of both sublevel sets transports K-Borel cohomology by the inclusion map. -/
theorem eq_bijective {s t s' t' : Set W} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (hsK : Inv k s) (htK : Inv k t) (hsK' : Inv k s') (htK' : Inv k t')
    (hs : s = s') (ht : t = t') (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k hst hsK htK hst' hsK' htK'
      (hs ▸ subset_rfl) (ht ▸ subset_rfl))) q) := by
  apply bijective_gHom k _ _ _ _ _ _ _ _
  intro m
  exact nativePull_bijective_of_Hmap _ m (Finsler.CutMove.eq_bijective hst hst' hs ht m)

end

end Finsler.CutMoveK
