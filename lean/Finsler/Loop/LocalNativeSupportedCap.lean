module

public import Finsler.Loop.NativeBallSupportPatch
public import Finsler.Loop.LocalNativeBallOriginalSplit
public import Finsler.Loop.SupportedCutCochainCarrierZero

/-! A real source-local first normalized Thom cap on the WHOLE ball
product. Its cover and Thom cocycle are pulled back from the ORIGINAL
cut parameters. Cochain differential and actual support are retained.
No comparison of independently chosen subdivision retractions is assumed. -/
@[expose] public section
namespace Finsler.LocalNativeSupportedCap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def exterior {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ : ℝ) :
    Set (LocalNativeBallCut.space P v₀) :=
  LocalNativeBallCut.cutParameters P v₀ b ⁻¹' SupportedSelfCut.exterior n ρ

theorem exterior_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ : ℝ) :
    IsOpen (exterior P v₀ b ρ) :=
  (SupportedSelfCut.exterior_open n ρ).preimage (LocalNativeBallCut.cutParameters P v₀ b).hom.continuous

theorem near_open {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :
    IsOpen (LocalNativeBallCut.near P v₀ b r) :=
  (SupportedSelfCut.neighborhood_open n r).preimage (LocalNativeBallCut.cutParameters P v₀ b).hom.continuous

theorem cover {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ} (hρr : ρ < r) :
    exterior P v₀ b ρ ∪ LocalNativeBallCut.near P v₀ b r = Set.univ := by
  change (LocalNativeBallCut.cutParameters P v₀ b ⁻¹' SupportedSelfCut.exterior n ρ) ∪
    (LocalNativeBallCut.cutParameters P v₀ b ⁻¹' SupportedSelfCut.neighborhood n r) = Set.univ
  rw [← Set.preimage_union, SupportedSelfCut.cover n hρr, Set.preimage_univ]

def cocycle (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) :=
  cochainPullback (LocalNativeBallCut.cutParameters P v₀ b) n (NormalizedSelfCut.cocycle n hn hρ)

theorem cocycle_closed (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) n (cocycle n hn P v₀ b hρ) = 0 :=
  pullback_closed (LocalNativeBallCut.cutParameters P v₀ b) n _ (NormalizedSelfCut.cocycle_closed n hn hρ)

theorem cocycle_supported (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (exterior P v₀ b ρ)) n
      (cocycle n hn P v₀ b hρ) = 0 :=
  pullback_support (LocalNativeBallCut.cutParameters P v₀ b) _ _ (fun _ h => h) n _
    (NormalizedSelfCut.cocycle_supported n hn hρ)

def operation (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) :=
  SupportedCapHomology.operation (LocalNativeBallCut.space P v₀) (exterior P v₀ b ρ) (LocalNativeBallCut.near P v₀ b r)
    (exterior_open P v₀ b ρ) (near_open P v₀ b r) (cover P v₀ b hρr) n
    (cocycle n hn P v₀ b hρ) (cocycle_supported n hn P v₀ b hρ) (cocycle_closed n hn P v₀ b hρ)

def cochain (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q) :=
  (operation n hn P v₀ b hρ hρr).component q ≫
    cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) q ψ

theorem cochain_boundary (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) (n + q) (cochain n hn P v₀ b hρ hρr q ψ) =
      cochain n hn P v₀ b hρ hρr (q + 1) (cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) q ψ) := by
  change (chains (LocalNativeBallCut.space P v₀)).d (n + (q + 1)) (n + q) ≫
    ((operation n hn P v₀ b hρ hρr).component q ≫ _) = _
  rw [← Category.assoc, ← (operation n hn P v₀ b hρ hρr).comm q, Category.assoc]
  exact congrArg (fun a => (operation n hn P v₀ b hρ hρr).component (q + 1) ≫ a)
    (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map
      (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r).op).comm q (q + 1)) ψ)

theorem cochain_sub (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ χ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q) :
    cochain n hn P v₀ b hρ hρr q (ψ - χ) =
      cochain n hn P v₀ b hρ hρr q ψ - cochain n hn P v₀ b hρ hρr q χ := by
  change (operation n hn P v₀ b hρ hρr).component q ≫
    ((push (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r)).f q ≫ (ψ - χ)) =
      (operation n hn P v₀ b hρ hρr).component q ≫ ((push (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r)).f q ≫ ψ) -
      (operation n hn P v₀ b hρ hρr).component q ≫ ((push (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r)).f q ≫ χ)
  simp only [Preadditive.comp_sub]

theorem cochain_outside_zero (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q)
    (hψ : cochainPullback
      (restriction (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
        ((SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ) ⁻¹'
          LocalNativeBallCut.near P v₀ b r) (LocalNativeBallCut.near P v₀ b r) (fun _ h => h)) q
      (cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) q ψ) = 0) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
      (n + q) (cochain n hn P v₀ b hρ hρr q ψ) = 0 := by
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero
    (LocalNativeBallCut.space P v₀) (exterior P v₀ b ρ) (LocalNativeBallCut.near P v₀ b r)
    (NativeBallSupportPatch.localGood P v₀)ᶜ (exterior_open P v₀ b ρ) (near_open P v₀ b r) (cover P v₀ b hρr)
    n q (cocycle n hn P v₀ b hρ) (cocycle_supported n hn P v₀ b hρ)
    (cochainPullback (LocalNativeBallOriginalSplit.nearInclusion P v₀ b r) q ψ) hψ

end
end Finsler.LocalNativeSupportedCap
