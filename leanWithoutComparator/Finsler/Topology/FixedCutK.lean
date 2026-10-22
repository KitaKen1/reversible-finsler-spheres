module

public import Finsler.Topology.FlowCutK
public import Finsler.Topology.LensFixed

/-! Cut comparison inside a flow-invariant subset. The actual upper-cut flow map on the
subset commutes with restriction from the full pair. Ordinary deformation isomorphisms give
K-Borel and reflection-Borel comparisons through these same maps. -/

@[expose] public section

namespace Finsler.FixedCutK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.FlowLens Finsler.InvPairs
open Finsler.LensK Finsler.CutMove Finsler.PairTriple Finsler.LensFamily
open Finsler.BorelComparison Finsler.FlowCutK

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

include hDσ in
theorem flow_fixed (t : ℝ) {w : W} (hw : k.σ w = w) : k.σ (D.flow t w) = D.flow t w := by
  rw [← hDσ, hw]

variable {Z : Set W} (hZ : Inv k Z)
variable (hDZ : ∀ t (w : W), 0 ≤ t → w ∈ Z → D.flow t w ∈ Z)

abbrev invSubIn (c : ℝ) : Inv k (sub g c ∩ Z) := inv_inter (inv_sub k hgρ hgσ c) hZ

def lowerDeformationIn {a a' b τ : ℝ} (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < a' → g (D.flow τ w) < a) :
    PairDeformation (sub g a ∩ Z) (sub g b ∩ Z) (sub g a' ∩ Z) (sub g b ∩ Z) where
  r := ⟨fun w => ⟨D.flow τ w, sub_flow D b τ w hτ w.2.1, hDZ τ w hτ w.2.2⟩,
    ((flow_continuous D τ).comp continuous_subtype_val).subtype_mk _⟩
  H := flowHomotopy D (u := sub g b ∩ Z) τ hτ fun t w ht hw =>
    ⟨sub_flow D b t w ht hw.1, hDZ t w ht hw.2⟩
  r_mem w := ⟨sub_flow D b τ w hτ w.2.1, hDZ τ w hτ w.2.2⟩
  r_sub w hw := ⟨hpush w hw.1, hDZ τ w hτ hw.2⟩
  keep_sub' s w hw := ⟨sub_flow D a' _ w (mul_nonneg s.2.1 hτ) hw.1,
    hDZ _ w (mul_nonneg s.2.1 hτ) hw.2⟩
  keep s w hw := ⟨sub_flow D b _ w (mul_nonneg s.2.1 hτ) hw.1,
    hDZ _ w (mul_nonneg s.2.1 hτ) hw.2⟩
  keep_sub s w hw := ⟨sub_flow D a _ w (mul_nonneg s.2.1 hτ) hw.1,
    hDZ _ w (mul_nonneg s.2.1 hτ) hw.2⟩

def upperDeformationIn {a b b' τ : ℝ} (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < b' → g (D.flow τ w) < b) :
    PairDeformation (sub g a ∩ Z) (sub g b ∩ Z) (sub g a ∩ Z) (sub g b' ∩ Z) where
  r := ⟨fun w => ⟨D.flow τ w, sub_flow D b' τ w hτ w.2.1, hDZ τ w hτ w.2.2⟩,
    ((flow_continuous D τ).comp continuous_subtype_val).subtype_mk _⟩
  H := flowHomotopy D (u := sub g b' ∩ Z) τ hτ fun t w ht hw =>
    ⟨sub_flow D b' t w ht hw.1, hDZ t w ht hw.2⟩
  r_mem w := ⟨hpush w w.2.1, hDZ τ w hτ w.2.2⟩
  r_sub w hw := ⟨sub_flow D a τ w hτ hw.1, hDZ τ w hτ hw.2⟩
  keep_sub' s w hw := ⟨sub_flow D a _ w (mul_nonneg s.2.1 hτ) hw.1,
    hDZ _ w (mul_nonneg s.2.1 hτ) hw.2⟩
  keep s w hw := ⟨sub_flow D b _ w (mul_nonneg s.2.1 hτ) hw.1,
    hDZ _ w (mul_nonneg s.2.1 hτ) hw.2⟩
  keep_sub s w hw := ⟨sub_flow D a _ w (mul_nonneg s.2.1 hτ) hw.1,
    hDZ _ w (mul_nonneg s.2.1 hτ) hw.2⟩

include hDZ in
theorem lower_native {a a' b τ : ℝ} (haa : a ≤ a') (hab : a' ≤ b) (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < a' → g (D.flow τ w) < a) (q : ℕ) :
    Function.Bijective (nativePull (inclPair
      (inter_subset_inter_left Z (sub_mono g (haa.trans hab)))
      (inter_subset_inter_left Z (sub_mono g hab))
      (inter_subset_inter_left Z (sub_mono g haa)) subset_rfl) q) :=
  bijective_nativePull_inclPair _ _ _ _ (lowerDeformationIn D hDZ hτ hpush) q

include hDZ in
theorem upper_native {a b b' τ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < b' → g (D.flow τ w) < b) (q : ℕ) :
    Function.Bijective (nativePull (inclPair
      (inter_subset_inter_left Z (sub_mono g hab))
      (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      subset_rfl (inter_subset_inter_left Z (sub_mono g hbb))) q) :=
  bijective_nativePull_inclPair _ _ _ _ (upperDeformationIn D hDZ hτ hpush) q

include hDZ in
theorem HK_lowerIn_bijective {a a' b τ : ℝ} (haa : a ≤ a') (hab : a' ≤ b) (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < a' → g (D.flow τ w) < a) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      (inter_subset_inter_left Z (sub_mono g (haa.trans hab)))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b)
      (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a') (invSubIn k hgρ hgσ hZ b)
      (inter_subset_inter_left Z (sub_mono g haa)) subset_rfl)) q) :=
  bijective_gHom k _ _ _ _ _ _ _ _ (lower_native D hDZ haa hab hτ hpush) q

include hDZ in
theorem HR_lowerIn_bijective {a a' b τ : ℝ} (haa : a ≤ a') (hab : a' ≤ b) (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < a' → g (D.flow τ w) < a) (q : ℕ) :
    Function.Bijective (HRmap (gHom k
      (inter_subset_inter_left Z (sub_mono g (haa.trans hab)))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b)
      (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a') (invSubIn k hgρ hgσ hZ b)
      (inter_subset_inter_left Z (sub_mono g haa)) subset_rfl).φ q) :=
  BorelInvariance.bijective_HRmap _ _ _
    (inclPair_restrict k.ρ _ _ _ _ _ _ _ _) (lower_native D hDZ haa hab hτ hpush) q

include hDZ in
theorem HK_upperIn_bijective {a b b' τ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < b' → g (D.flow τ w) < b) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b)
      (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b')
      subset_rfl (inter_subset_inter_left Z (sub_mono g hbb)))) q) :=
  bijective_gHom k _ _ _ _ _ _ _ _ (upper_native D hDZ hab hbb hτ hpush) q

include hDZ in
theorem HR_upperIn_bijective {a b b' τ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hτ : 0 ≤ τ)
    (hpush : ∀ w, g w < b' → g (D.flow τ w) < b) (q : ℕ) :
    Function.Bijective (HRmap (gHom k
      (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b)
      (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b')
      subset_rfl (inter_subset_inter_left Z (sub_mono g hbb))).φ q) :=
  BorelInvariance.bijective_HRmap _ _ _
    (inclPair_restrict k.ρ _ _ _ _ _ _ _ _) (upper_native D hDZ hab hbb hτ hpush) q

variable {a b b' τ : ℝ} (hab : a ≤ b) (hbb : b ≤ b') (hτ : 0 ≤ τ)
variable (hpush : ∀ w, g w < b' → g (D.flow τ w) < b)

def upperFlowPairIn :
    pairOf (inter_subset_inter_left Z (sub_mono g (hab.trans hbb))) ⟶
      pairOf (inter_subset_inter_left Z (sub_mono g hab)) :=
  retract _ _ (upperDeformationIn D hDZ hτ hpush)

theorem upperFlow_native (q : ℕ) :
    Function.Bijective (nativePull (upperFlowPairIn D hDZ hab hbb hτ hpush) q) := by
  obtain ⟨H₁⟩ := nonempty_homotopy_left
    (inter_subset_inter_left Z (sub_mono g hab))
    (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
    subset_rfl (inter_subset_inter_left Z (sub_mono g hbb)) (upperDeformationIn D hDZ hτ hpush)
  obtain ⟨H₂⟩ := nonempty_homotopy_right
    (inter_subset_inter_left Z (sub_mono g hab))
    (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
    subset_rfl (inter_subset_inter_left Z (sub_mono g hbb)) (upperDeformationIn D hDZ hτ hpush)
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv
    (upperFlowPairIn D hDZ hab hbb hτ hpush)
    (inclPair _ _ subset_rfl (inter_subset_inter_left Z (sub_mono g hbb))) H₂ H₁ q

include hDρ in
theorem upperFlowPairIn_ρ : upperFlowPairIn D hDZ hab hbb hτ hpush ≫ restrictPair k.ρ
      (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a).ρ_mem (invSubIn k hgρ hgσ hZ b).ρ_mem =
    restrictPair k.ρ (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (invSubIn k hgρ hgσ hZ a).ρ_mem (invSubIn k hgρ hgσ hZ b').ρ_mem ≫
        upperFlowPairIn D hDZ hab hbb hτ hpush := by
  ext Q <;> exact Subtype.ext (hDρ τ Q.1).symm

include hDσ in
theorem upperFlowPairIn_σ : upperFlowPairIn D hDZ hab hbb hτ hpush ≫ restrictPair k.σ
      (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a).σ_mem (invSubIn k hgρ hgσ hZ b).σ_mem =
    restrictPair k.σ (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (invSubIn k hgρ hgσ hZ a).σ_mem (invSubIn k hgρ hgσ hZ b').σ_mem ≫
        upperFlowPairIn D hDZ hab hbb hτ hpush := by
  ext Q <;> exact Subtype.ext (hDσ τ Q.1).symm

def upperFlowHomIn : CommHom
    (gCommuting k (inter_subset_inter_left Z (sub_mono g hab))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b))
    (gCommuting k (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b')) :=
  BorelInvariance.commHom
    (restrictPair_sq k.ρ k.ρρ _ (invSubIn k hgρ hgσ hZ a).ρ_mem (invSubIn k hgρ hgσ hZ b').ρ_mem)
    (restrictPair_sq k.ρ k.ρρ _ (invSubIn k hgρ hgσ hZ a).ρ_mem (invSubIn k hgρ hgσ hZ b).ρ_mem)
    (upperFlowPairIn D hDZ hab hbb hτ hpush)
    (upperFlowPairIn_ρ k hgρ hgσ D hDρ hZ hDZ hab hbb hτ hpush)
    (restrictPair_sq k.σ k.σσ _ (invSubIn k hgρ hgσ hZ a).σ_mem (invSubIn k hgρ hgσ hZ b').σ_mem)
    (restrictPair_sq k.σ k.σσ _ (invSubIn k hgρ hgσ hZ a).σ_mem (invSubIn k hgρ hgσ hZ b).σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ _ (invSubIn k hgρ hgσ hZ a).ρ_mem
      (invSubIn k hgρ hgσ hZ b').ρ_mem (invSubIn k hgρ hgσ hZ a).σ_mem (invSubIn k hgρ hgσ hZ b').σ_mem)
    (restrictPair_comm k.ρ k.σ k.ρσ _ (invSubIn k hgρ hgσ hZ a).ρ_mem
      (invSubIn k hgρ hgσ hZ b).ρ_mem (invSubIn k hgρ hgσ hZ a).σ_mem (invSubIn k hgρ hgσ hZ b).σ_mem)
    (upperFlowPairIn_σ k hgρ hgσ D hDσ hZ hDZ hab hbb hτ hpush)

theorem HK_upperFlowIn_bijective (q : ℕ) :
    Function.Bijective (HRmap (borelHom
      (upperFlowHomIn k hgρ hgσ D hDρ hDσ hZ hDZ hab hbb hτ hpush)) q) :=
  BorelInvariance.bijective_iterated _ _ _ _ _ _ _ _ _
    (upperFlow_native D hDZ hab hbb hτ hpush) q

theorem HR_upperFlowIn_bijective (q : ℕ) :
    Function.Bijective (HRmap
      (upperFlowHomIn k hgρ hgσ D hDρ hDσ hZ hDZ hab hbb hτ hpush).φ q) :=
  BorelInvariance.bijective_HRmap _ _ (upperFlowPairIn D hDZ hab hbb hτ hpush)
    (upperFlowPairIn_ρ k hgρ hgσ D hDρ hZ hDZ hab hbb hτ hpush)
    (upperFlow_native D hDZ hab hbb hτ hpush) q

theorem upperFlow_restriction_square :
    upperFlowPairIn D hDZ hab hbb hτ hpush ≫
      inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
        inter_subset_left inter_subset_left =
    inclPair (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
        (sub_mono g (hab.trans hbb)) inter_subset_left inter_subset_left ≫
      upperFlowPair D hab hbb hτ hpush := by
  ext Q <;> rfl

theorem upperFlow_restriction_cochains (j : ℕ)
    (x : (cochains (pairOf (sub_mono g hab))).X j) :
    ((pull (inclPair (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (sub_mono g (hab.trans hbb)) inter_subset_left inter_subset_left)).f j).hom
      (((pull (upperFlowPair D hab hbb hτ hpush)).f j).hom x) =
    ((pull (upperFlowPairIn D hDZ hab hbb hτ hpush)).f j).hom
      (((pull (inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
        inter_subset_left inter_subset_left)).f j).hom x) := by
  have h₁ := pull_comp_apply
    (inclPair (inter_subset_inter_left Z (sub_mono g (hab.trans hbb)))
      (sub_mono g (hab.trans hbb)) inter_subset_left inter_subset_left)
    (upperFlowPair D hab hbb hτ hpush) j x
  have h₂ := pull_comp_apply (upperFlowPairIn D hDZ hab hbb hτ hpush)
    (inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
      inter_subset_left inter_subset_left) j x
  rw [upperFlow_restriction_square D hDZ hab hbb hτ hpush] at h₂
  exact h₁.symm.trans h₂

end

end Finsler.FixedCutK
