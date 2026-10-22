module

public import Finsler.Topology.CutMove
public import Finsler.Topology.LensK

/-! the actual time-flow map which moves the upper cut induces
K and reflection Borel isomorphisms. This supplies a map in the direction needed to transport
the deformed ambient lens to the wide loop crossing, rather than only an abstract inverse. -/

@[expose] public section

namespace Finsler.FlowCutK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.FlowLens Finsler.InvPairs
open Finsler.LensK Finsler.CutMove Finsler.PairTriple Finsler.LensFamily
open Finsler.BorelComparison

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} (k : KAct W) {g : W → ℝ}
variable (hgρ : ∀ w, g (k.ρ w) = g w) (hgσ : ∀ w, g (k.σ w) = g w)
variable (D : Descent W g)
variable (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w))
variable (hDσ : ∀ t w, D.flow t (k.σ w) = k.σ (D.flow t w))
variable {a b b' τ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hτ : 0 ≤ τ)
variable (hpush : ∀ w, g w < b' → g (D.flow τ w) < b)

def upperFlowPair : pairOf (sub_mono g (hab.trans hbb)) ⟶ pairOf (sub_mono g hab) :=
  retract (sub_mono g hab) (sub_mono g (hab.trans hbb)) (upperDeformation D hτ hpush)

include hDρ in
theorem upperFlowPair_ρ : upperFlowPair D hab hbb hτ hpush ≫
      restrictPair k.ρ (sub_mono g hab) (inv_sub k hgρ hgσ a).ρ_mem (inv_sub k hgρ hgσ b).ρ_mem =
    restrictPair k.ρ (sub_mono g (hab.trans hbb))
      (inv_sub k hgρ hgσ a).ρ_mem (inv_sub k hgρ hgσ b').ρ_mem ≫
        upperFlowPair D hab hbb hτ hpush := by
  ext Q
  · exact Subtype.ext (hDρ τ Q.1).symm
  · exact Subtype.ext (hDρ τ Q.1).symm

include hDσ in
theorem upperFlowPair_σ : upperFlowPair D hab hbb hτ hpush ≫
      restrictPair k.σ (sub_mono g hab) (inv_sub k hgρ hgσ a).σ_mem (inv_sub k hgρ hgσ b).σ_mem =
    restrictPair k.σ (sub_mono g (hab.trans hbb))
      (inv_sub k hgρ hgσ a).σ_mem (inv_sub k hgρ hgσ b').σ_mem ≫
        upperFlowPair D hab hbb hτ hpush := by
  ext Q
  · exact Subtype.ext (hDσ τ Q.1).symm
  · exact Subtype.ext (hDσ τ Q.1).symm

def upperFlowHom :
    CommHom (gCommuting k (sub_mono g hab) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b))
      (gCommuting k (sub_mono g (hab.trans hbb)) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b')) :=
  BorelInvariance.commHom
    (restrictPair_sq k.ρ k.ρρ _ (inv_sub k hgρ hgσ a).ρ_mem (inv_sub k hgρ hgσ b').ρ_mem)
    (restrictPair_sq k.ρ k.ρρ _ (inv_sub k hgρ hgσ a).ρ_mem (inv_sub k hgρ hgσ b).ρ_mem)
    (upperFlowPair D hab hbb hτ hpush) (upperFlowPair_ρ k hgρ hgσ D hDρ hab hbb hτ hpush)
    (restrictPair_sq k.σ k.σσ _ (inv_sub k hgρ hgσ a).σ_mem (inv_sub k hgρ hgσ b').σ_mem)
    (restrictPair_sq k.σ k.σσ _ (inv_sub k hgρ hgσ a).σ_mem (inv_sub k hgρ hgσ b).σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ _ (inv_sub k hgρ hgσ a).ρ_mem (inv_sub k hgρ hgσ b').ρ_mem
      (inv_sub k hgρ hgσ a).σ_mem (inv_sub k hgρ hgσ b').σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ _ (inv_sub k hgρ hgσ a).ρ_mem (inv_sub k hgρ hgσ b).ρ_mem
      (inv_sub k hgρ hgσ a).σ_mem (inv_sub k hgρ hgσ b).σ_mem)
    (upperFlowPair_σ k hgρ hgσ D hDσ hab hbb hτ hpush)

private theorem upperFlow_native (q : ℕ) :
    Function.Bijective (nativePull (upperFlowPair D hab hbb hτ hpush) q) := by
  obtain ⟨H₁⟩ := nonempty_homotopy_left (sub_mono g hab) (sub_mono g (hab.trans hbb))
    subset_rfl (sub_mono g hbb) (upperDeformation D hτ hpush)
  obtain ⟨H₂⟩ := nonempty_homotopy_right (sub_mono g hab) (sub_mono g (hab.trans hbb))
    subset_rfl (sub_mono g hbb) (upperDeformation D hτ hpush)
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv
    (upperFlowPair D hab hbb hτ hpush)
    (inclPair (sub_mono g hab) (sub_mono g (hab.trans hbb)) subset_rfl (sub_mono g hbb)) H₂ H₁ q

theorem HK_upperFlow_bijective (q : ℕ) :
    Function.Bijective (HRmap (borelHom (upperFlowHom k hgρ hgσ D hDρ hDσ hab hbb hτ hpush)) q) := by
  exact BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _
    (upperFlow_native D hab hbb hτ hpush) q

theorem HR_upperFlow_bijective (q : ℕ) :
    Function.Bijective (HRmap (upperFlowHom k hgρ hgσ D hDρ hDσ hab hbb hτ hpush).φ q) := by
  exact BorelInvariance.bijective_HRmap _ _ (upperFlowPair D hab hbb hτ hpush)
    (upperFlowPair_ρ k hgρ hgσ D hDρ hab hbb hτ hpush)
    (upperFlow_native D hab hbb hτ hpush) q

end

end Finsler.FlowCutK
