module

public import Finsler.Topology.AmbientInclusionK
public import Finsler.Topology.FixedCutK

/-! actual pair maps from wide cuts of the original function to
tight cuts of the deformed function, simultaneously on the full space and a preserved subset. -/

@[expose] public section

namespace Finsler.PairCutTransportK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.FlowLens Finsler.InvPairs
open Finsler.LensK Finsler.CutMove Finsler.PairTriple Finsler.LensFamily
open Finsler.BorelComparison Finsler.BorelLens Finsler.FlowCutK Finsler.FixedCutK
open Finsler.AmbientInclusionK

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem native_comp_bijective {P Q R : TopPair.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (q : ℕ)
    (hf : Function.Bijective (nativePull f q)) (hg : Function.Bijective (nativePull g q)) :
    Function.Bijective (nativePull (f ≫ g) q) := by
  have he : ⇑(nativePull (f ≫ g) q) = ⇑(nativePull f q) ∘ ⇑(nativePull g q) :=
    funext (nativePull_comp f g q)
  rw [he]
  exact hf.comp hg

theorem native_retract_bijective {X : TopCat.{0}} {s t s' t' : Set X}
    (hst : s ⊆ t) (hst' : s' ⊆ t') (hss : s ⊆ s') (htt : t ⊆ t')
    (d : PairDeformation s t s' t') (q : ℕ) :
    Function.Bijective (nativePull (retract hst hst' d) q) := by
  obtain ⟨H₁⟩ := nonempty_homotopy_left hst hst' hss htt d
  obtain ⟨H₂⟩ := nonempty_homotopy_right hst hst' hss htt d
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv
    (retract hst hst' d) (inclPair hst hst' hss htt) H₂ H₁ q

variable {W : TopCat.{0}} (k : KAct W) {g : W → ℝ}
variable (hgρ : ∀ w, g (k.ρ w) = g w) (hgσ : ∀ w, g (k.σ w) = g w)
variable (D : Descent W g)
variable (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w))
variable (hDσ : ∀ t w, D.flow t (k.σ w) = k.σ (D.flow t w))
variable {Z : Set W} (hZ : Inv k Z)
variable (hDZ : ∀ t (w : W), 0 ≤ t → w ∈ Z → D.flow t w ∈ Z)
variable {h : W → ℝ} {aw a b bw τ : ℝ} (haw : aw ≤ a) (hab : a ≤ b) (hbw : b ≤ bw)
variable (hsa : sub h aw = sub g aw) (hsb : sub h bw = sub g bw) (hτ : 0 ≤ τ)
variable (hpush : ∀ w, g w < bw → g (D.flow τ w) < b)
variable (hhρ : ∀ w, h (k.ρ w) = h w) (hhσ : ∀ w, h (k.σ w) = h w)

def equalWidePair : pairOf (sub_mono h (haw.trans (hab.trans hbw))) ⟶
    pairOf (sub_mono g (haw.trans (hab.trans hbw))) :=
  inclPair _ _ (fun _ hx => hsa ▸ hx) (fun _ hx => hsb ▸ hx)

def equalWidePairIn :
    pairOf (inter_subset_inter_left Z (sub_mono h (haw.trans (hab.trans hbw)))) ⟶
      pairOf (inter_subset_inter_left Z (sub_mono g (haw.trans (hab.trans hbw)))) :=
  inclPair _ _ (fun _ hx => ⟨hsa ▸ hx.1, hx.2⟩) (fun _ hx => ⟨hsb ▸ hx.1, hx.2⟩)

def toTightPair : pairOf (sub_mono h (haw.trans (hab.trans hbw))) ⟶ pairOf (sub_mono g hab) :=
  equalWidePair haw hab hbw hsa hsb ≫ upperFlowPair D (haw.trans hab) hbw hτ hpush ≫
    inclPair (sub_mono g (haw.trans hab)) (sub_mono g hab) (sub_mono g haw) subset_rfl

def toTightPairIn :
    pairOf (inter_subset_inter_left Z (sub_mono h (haw.trans (hab.trans hbw)))) ⟶
      pairOf (inter_subset_inter_left Z (sub_mono g hab)) :=
  equalWidePairIn haw hab hbw hsa hsb ≫ upperFlowPairIn D hDZ (haw.trans hab) hbw hτ hpush ≫
    inclPair (inter_subset_inter_left Z (sub_mono g (haw.trans hab)))
      (inter_subset_inter_left Z (sub_mono g hab))
      (inter_subset_inter_left Z (sub_mono g haw)) subset_rfl

theorem toTight_native {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (nativePull (toTightPair D haw hab hbw hsa hsb hτ hpush) q) := by
  unfold toTightPair
  apply native_comp_bijective _ _ q
  · exact Finsler.LensK.nativePull_bijective_of_Hmap _ q
      (Finsler.CutMove.eq_bijective _ _ hsa hsb q)
  · apply native_comp_bijective _ _ q
    · exact native_retract_bijective _ _ subset_rfl (sub_mono g hbw)
        (upperDeformation D hτ hpush) q
    · exact bijective_nativePull_inclPair _ _ _ _ (lowerDeformation D hτl hpushl) q

theorem toTightIn_native {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (nativePull (toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush) q) := by
  unfold toTightPairIn
  apply native_comp_bijective _ _ q
  · exact Finsler.LensK.nativePull_bijective_of_Hmap _ q (Finsler.CutMove.eq_bijective _ _
      (congrArg (fun A : Set W => A ∩ Z) hsa) (congrArg (fun A : Set W => A ∩ Z) hsb) q)
  · apply native_comp_bijective _ _ q
    · exact FixedCutK.upperFlow_native D hDZ (haw.trans hab) hbw hτ hpush q
    · exact FixedCutK.lower_native D hDZ haw hab hτl hpushl q

def transportHom : CommHom
    (gCommuting k (sub_mono g hab) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b))
    (gCommuting k (sub_mono h (haw.trans (hab.trans hbw)))
      (inv_sub k hhρ hhσ aw) (inv_sub k hhρ hhσ bw)) :=
  equivPairHom k k _ _ _ _ _ _ (toTightPair D haw hab hbw hsa hsb hτ hpush)
    (by ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm)
    (by ext Q <;> exact Subtype.ext (hDσ τ Q.1).symm)

def transportHomIn : CommHom
    (gCommuting k (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b))
    (gCommuting k (inter_subset_inter_left Z (sub_mono h (haw.trans (hab.trans hbw))))
      (invSubIn k hhρ hhσ hZ aw) (invSubIn k hhρ hhσ hZ bw)) :=
  equivPairHom k k _ _ _ _ _ _ (toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush)
    (by ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm)
    (by ext Q <;> exact Subtype.ext (hDσ τ Q.1).symm)

theorem HK_transport_bijective {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap (borelHom
      (transportHom k hgρ hgσ D hDρ hDσ haw hab hbw hsa hsb hτ hpush hhρ hhσ)) q) :=
  BorelInvariance.bijective_iterated _ _ (toTightPair D haw hab hbw hsa hsb hτ hpush)
    (by ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm) _ _ _ _
    (by ext Q <;> exact Subtype.ext (hDσ τ Q.1).symm)
    (toTight_native D haw hab hbw hsa hsb hτ hpush hτl hpushl) q

theorem HR_transport_bijective {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap
      (transportHom k hgρ hgσ D hDρ hDσ haw hab hbw hsa hsb hτ hpush hhρ hhσ).φ q) :=
  BorelInvariance.bijective_HRmap _ _ (toTightPair D haw hab hbw hsa hsb hτ hpush)
    (by ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm)
    (toTight_native D haw hab hbw hsa hsb hτ hpush hτl hpushl) q

theorem HK_transportIn_bijective {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap (borelHom
      (transportHomIn k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ)) q) :=
  BorelInvariance.bijective_iterated _ _ (toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush)
    (by ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm) _ _ _ _
    (by ext Q <;> exact Subtype.ext (hDσ τ Q.1).symm)
    (toTightIn_native D hDZ haw hab hbw hsa hsb hτ hpush hτl hpushl) q

theorem HR_transportIn_bijective {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap
      (transportHomIn k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ).φ q) :=
  BorelInvariance.bijective_HRmap _ _ (toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush)
    (by ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm)
    (toTightIn_native D hDZ haw hab hbw hsa hsb hτ hpush hτl hpushl) q

theorem transport_restriction_square : toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush ≫
      inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
        inter_subset_left inter_subset_left =
    inclPair (inter_subset_inter_left Z (sub_mono h (haw.trans (hab.trans hbw))))
        (sub_mono h (haw.trans (hab.trans hbw))) inter_subset_left inter_subset_left ≫
      toTightPair D haw hab hbw hsa hsb hτ hpush := by
  ext Q <;> rfl

theorem transport_restriction_cochains (j : ℕ) (x : (cochains (pairOf (sub_mono g hab))).X j) :
    ((pull (inclPair (inter_subset_inter_left Z (sub_mono h (haw.trans (hab.trans hbw))))
      (sub_mono h (haw.trans (hab.trans hbw))) inter_subset_left inter_subset_left)).f j).hom
      (((pull (toTightPair D haw hab hbw hsa hsb hτ hpush)).f j).hom x) =
    ((pull (toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush)).f j).hom
      (((pull (inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
        inter_subset_left inter_subset_left)).f j).hom x) := by
  have h₁ := pull_comp_apply
    (inclPair (inter_subset_inter_left Z (sub_mono h (haw.trans (hab.trans hbw))))
      (sub_mono h (haw.trans (hab.trans hbw))) inter_subset_left inter_subset_left)
    (toTightPair D haw hab hbw hsa hsb hτ hpush) j x
  have h₂ := pull_comp_apply (toTightPairIn D hDZ haw hab hbw hsa hsb hτ hpush)
    (inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
      inter_subset_left inter_subset_left) j x
  rw [transport_restriction_square D hDZ haw hab hbw hsa hsb hτ hpush] at h₂
  exact h₁.symm.trans h₂

end

end Finsler.PairCutTransportK
