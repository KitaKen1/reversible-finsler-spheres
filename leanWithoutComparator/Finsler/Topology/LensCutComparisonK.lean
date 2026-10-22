module

public import Finsler.Topology.PairCutTransportK
public import Finsler.Topology.PolyPieces

/-! compare a deformed lens to an unchanged wide crossing,
with the same actual maps on a preserved invariant subset. -/

@[expose] public section

namespace Finsler.LensCutComparisonK

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.FlowLens Finsler.InvPairs
open Finsler.LensK Finsler.PairTriple Finsler.LensFamily Finsler.BorelComparison
open Finsler.BorelLens Finsler.FixedCutK Finsler.PairCutTransportK Finsler.PolyPieces
open Finsler.PolySplit Finsler.LensFixed

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
variable {Z : Set W} (hZ : Inv k Z)
variable (hDZ : ∀ t (w : W), 0 ≤ t → w ∈ Z → D.flow t w ∈ Z)
variable {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T)

abbrev lensRes :=
  gHom k (sub_mono g hab) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b)
    (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T)
    (inv_sub k hgρ hgσ b) (sub_subset_lensY D hab hT) subset_rfl

abbrev fixLensRes :=
  gHom k (inter_subset_inter_left Z (sub_mono g hab))
    (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b)
    (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
    (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZ)
    (invSubIn k hgρ hgσ hZ b) (sub_inter_subset_lensY D hab hT) subset_rfl

abbrev crossingRes := gHom k (inter_subset_inter_left Z (sub_mono g hab))
  (invSubIn k hgρ hgσ hZ a) (invSubIn k hgρ hgσ hZ b)
  (sub_mono g hab) (inv_sub k hgρ hgσ a) (inv_sub k hgρ hgσ b)
  inter_subset_left inter_subset_left

theorem lensRes_comm (i : ℕ)
    (x : (cochains (pairOf (lensY_subset D a b T))).X i) :
    (crossingRes k hgρ hgσ hZ hab).φ.f i ((lensRes k hgρ hgσ D hDρ hDσ hab hT).φ.f i x) =
      (fixLensRes k hgρ hgσ D hDρ hDσ hZ hab hT).φ.f i
        ((mainHom k hZ hgρ hgσ D hDρ hDσ a b T).φ.f i x) := by
  have e : inclPair (inter_subset_inter_left Z (sub_mono g hab)) (sub_mono g hab)
        inter_subset_left inter_subset_left ≫
      inclPair (sub_mono g hab) (lensY_subset D a b T)
        (sub_subset_lensY D hab hT) subset_rfl =
    inclPair (inter_subset_inter_left Z (sub_mono g hab))
        (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
        (sub_inter_subset_lensY D hab hT) subset_rfl ≫
      inclPair (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
        (lensY_subset D a b T) inter_subset_left inter_subset_left := by
    ext Q <;> rfl
  exact (pull_comp_apply _ _ i x).symm.trans
    ((congrArg (fun f => ((pull f).f i).hom x) e).trans (pull_comp_apply _ _ i x))

variable {h : W → ℝ} {aw bw τ : ℝ} (haw : aw ≤ a) (hbw : b ≤ bw)
variable (hsa : sub h aw = sub g aw) (hsb : sub h bw = sub g bw) (hτ : 0 ≤ τ)
variable (hpush : ∀ w, g w < bw → g (D.flow τ w) < b)
variable (hhρ : ∀ w, h (k.ρ w) = h w) (hhσ : ∀ w, h (k.σ w) = h w)

abbrev toWide := commComp (lensRes k hgρ hgσ D hDρ hDσ hab hT)
  (transportHom k hgρ hgσ D hDρ hDσ haw hab hbw hsa hsb hτ hpush hhρ hhσ)

abbrev toWideIn := commComp (fixLensRes k hgρ hgσ D hDρ hDσ hZ hab hT)
  (transportHomIn k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ)

theorem toWide_comm (i : ℕ)
    (x : (cochains (pairOf (lensY_subset D a b T))).X i) :
    (crossingRes k hhρ hhσ hZ (haw.trans (hab.trans hbw))).φ.f i
        ((toWide k hgρ hgσ D hDρ hDσ hab hT haw hbw hsa hsb hτ hpush hhρ hhσ).φ.f i x) =
      (toWideIn k hgρ hgσ D hDρ hDσ hZ hDZ hab hT haw hbw hsa hsb hτ hpush hhρ hhσ).φ.f i
        ((mainHom k hZ hgρ hgσ D hDρ hDσ a b T).φ.f i x) := by
  have hc := transport_restriction_cochains D hDZ haw hab hbw hsa hsb hτ hpush i
    ((lensRes k hgρ hgσ D hDρ hDσ hab hT).φ.f i x)
  change (crossingRes k hhρ hhσ hZ (haw.trans (hab.trans hbw))).φ.f i
      ((transportHom k hgρ hgσ D hDρ hDσ haw hab hbw hsa hsb hτ hpush hhρ hhσ).φ.f i
        ((lensRes k hgρ hgσ D hDρ hDσ hab hT).φ.f i x)) =
    (transportHomIn k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ).φ.f i
      ((crossingRes k hgρ hgσ hZ hab).φ.f i
        ((lensRes k hgρ hgσ D hDρ hDσ hab hT).φ.f i x)) at hc
  exact hc.trans (congrArg
    ((transportHomIn k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ).φ.f i)
    (lensRes_comm k hgρ hgσ D hDρ hDσ hZ hab hT i x))

theorem toWide_bijective {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap (borelHom
      (toWide k hgρ hgσ D hDρ hDσ hab hT haw hbw hsa hsb hτ hpush hhρ hhσ)) q) :=
  HK_commComp_bijective _ _ q (HK_lens_bijective k hgρ hgσ D hDρ hDσ hab hT q)
    (HK_transport_bijective k hgρ hgσ D hDρ hDσ haw hab hbw hsa hsb hτ hpush hhρ hhσ hτl hpushl q)

theorem toWideIn_bijective {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap (borelHom
      (toWideIn k hgρ hgσ D hDρ hDσ hZ hDZ hab hT haw hbw hsa hsb hτ hpush hhρ hhσ)) q) :=
  HK_commComp_bijective _ _ q
    (bijective_gHom k _ _ _ _ _ _ _ _
      (fun m => lens_nativePull_in (Z := Z) D hDZ hab hT m) q)
    (HK_transportIn_bijective k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ
      hτl hpushl q)

theorem toWideIn_bijective_R {τl : ℝ} (hτl : 0 ≤ τl)
    (hpushl : ∀ w, g w < a → g (D.flow τl w) < aw) (q : ℕ) :
    Function.Bijective (HRmap
      (toWideIn k hgρ hgσ D hDρ hDσ hZ hDZ hab hT haw hbw hsa hsb hτ hpush hhρ hhσ).φ q) :=
  HR_commComp_bijective _ _ q
    (BorelInvariance.bijective_HRmap _ _ _ (inclPair_restrict k.ρ _ _ _ _ _ _ _ _)
      (fun m => lens_nativePull_in (Z := Z) D hDZ hab hT m) q)
    (HR_transportIn_bijective k hgρ hgσ D hDρ hDσ hZ hDZ haw hab hbw hsa hsb hτ hpush hhρ hhσ
      hτl hpushl q)

end

end Finsler.LensCutComparisonK
