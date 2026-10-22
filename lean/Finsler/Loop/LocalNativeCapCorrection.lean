module

public import Finsler.Loop.LocalNativeSupportedCap

/-! Carry the ACTUAL tested primitive through the source-local first
normalized Thom cap. Its POST-cap correction is literallyzero outside
the real quarter support, and gives a genuine RELATIVE class equality.
The separate comparison with the original target subdivision remains. -/
@[expose] public section
namespace Finsler.LocalNativeCapCorrection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

theorem outside_farCarrier {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (z : LocalNativeBallCut.space P v₀) (hz : z ∉ NativeBallSupportPatch.localGood P v₀) :
    LocalNativeBallCut.cutParameters P v₀ b z ∈
      LocalizedParameterCutCochain.farCarrier n (LocalNativeBallCut.center P v₀) (1 / 4) := by
  have he := LocalNativeBallCut.self_evaluation P v₀ b z
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  change H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z).2 = z.1.val at hl
  change H1SelfCutNeighborhood.endpoint (LocalNativeBallCut.cutParameters P v₀ b z) = z.2.1.val at hr
  by_cases h : ‖(z.1.val : Ambient n) - (LocalNativeBallCut.center P v₀ : Ambient n)‖ < 1 / 4
  · right
    rw [hr]
    exact le_of_not_gt (fun h₂ => hz ⟨h, h₂⟩)
  · left
    rw [hl]
    exact le_of_not_gt h

theorem near_first_far {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hηr : η + r ≤ 1 / 4)
    (z : LocalNativeBallCut.near P v₀ b r) (hz : z.val ∉ NativeBallSupportPatch.localGood P v₀) :
    η ≤ ‖(z.val.1.val : Ambient n) - (LocalNativeBallCut.center P v₀ : Ambient n)‖ := by
  have he := congrArg Prod.fst (LocalNativeBallCut.self_evaluation P v₀ b z.val)
  change H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z.val).2 = z.val.1.val at he
  have hf := LocalizedParameterCutCochain.farCarrier_near_start n (LocalNativeBallCut.center P v₀)
    (lt_trans hρ hρr) hηr (LocalNativeBallCut.toNeighborhood P v₀ b r z) (outside_farCarrier P v₀ b z.val hz)
  change η ≤ ‖(H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z.val).2 : Ambient n) -
    (LocalNativeBallCut.center P v₀ : Ambient n)‖ at hf
  rw [he] at hf
  exact hf

def correction (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :=
  LocalNativeSupportedCap.cochain (m + 1) (by omega) P v₀ b hρ hρr ((m - 1) + (m + 1))
    (LocalNativeBallCupCorrection.correction m hm P v₀ b hη)

def testedCochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :=
  LocalNativeSupportedCap.cochain (m + 1) (by omega) P v₀ b hρ hρr (m + (m + 1))
    (cochainCup m (m + 1) (LocalNativeBallPrimitive.testedCocycle m P v₀ b)
      (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη))

def reducedCochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :=
  LocalNativeSupportedCap.cochain (m + 1) (by omega) P v₀ b hρ hρr (m + (m + 1))
    (cochainCup m (m + 1) (LocalNativeBallPrimitive.reducedCocycle m P v₀ b)
      (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη))

private theorem cochain_cast (n : ℕ) (hn : 1 ≤ n) (P : Sphere n) (v₀ : equator P) (b : Fin 3) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) {q q' : ℕ} (h : q = q')
    (ψ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q) :
    LocalNativeSupportedCap.cochain n hn P v₀ b hρ hρr q' (cochainCast h ψ) =
      cochainCast (congrArg (n + ·) h) (LocalNativeSupportedCap.cochain n hn P v₀ b hρ hρr q ψ) := by
  subst q'
  rfl

private theorem cast_sub {X : TopCat.{0}} {a b : ℕ} (h : a = b)
    (φ ψ : singularCochainGroup (ZMod 2) X a) :
    cochainCast h (φ - ψ) = cochainCast h φ - cochainCast h ψ := by
  subst b
  rfl

private theorem cup_cast (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X q) :
    cochainCast h (cochainCup p q φ ψ) = CupOne.cup X p q n h φ ψ := by
  subst n
  simpa only [cochainCast, eqToHom_refl, Category.id_comp] using
    (CupOne.cup_comparison X p q φ ψ).symm

theorem correction_boundary (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + ((m - 1) + (m + 1)))
      (correction m hm P v₀ b hρ hρr hη) =
      cochainCast (by omega : (m + 1) + (m + (m + 1)) = ((m + 1) + ((m - 1) + (m + 1))) + 1)
        (testedCochain m P v₀ b hρ hρr hη - reducedCochain m P v₀ b hρ hρr hη) := by
  let q := (m - 1) + (m + 1)
  have hd : m + (m + 1) = q + 1 := by dsimp only [q]; omega
  let φ := cochainCup m (m + 1) (LocalNativeBallPrimitive.testedCocycle m P v₀ b)
    (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)
  let ψ := cochainCup m (m + 1) (LocalNativeBallPrimitive.reducedCocycle m P v₀ b)
    (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)
  have h₁ := cup_cast (LocalNativeBallCut.space P v₀) m (m + 1) (q + 1) hd
    (LocalNativeBallPrimitive.testedCocycle m P v₀ b) (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)
  have h₂ := cup_cast (LocalNativeBallCut.space P v₀) m (m + 1) (q + 1) hd
    (LocalNativeBallPrimitive.reducedCocycle m P v₀ b) (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)
  have hb : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) q
      (LocalNativeBallCupCorrection.correction m hm P v₀ b hη) = cochainCast hd (φ - ψ) :=
    (LocalNativeBallCupCorrection.correction_boundary m hm P v₀ b hη).trans
      ((congrArg₂ (fun a b => a - b) h₁.symm h₂.symm).trans (cast_sub hd φ ψ).symm)
  have hc := LocalNativeSupportedCap.cochain_boundary (m + 1) (by omega) P v₀ b hρ hρr q
    (LocalNativeBallCupCorrection.correction m hm P v₀ b hη)
  have he := congrArg (fun a => LocalNativeSupportedCap.cochain (m + 1) (by omega) P v₀ b hρ hρr (q + 1) a) hb
  exact hc.trans (he.trans ((cochain_cast (m + 1) (by omega) P v₀ b hρ hρr hd (φ - ψ)).trans
    (congrArg (cochainCast (congrArg ((m + 1) + ·) hd))
      (LocalNativeSupportedCap.cochain_sub (m + 1) (by omega) P v₀ b hρ hρr (m + (m + 1)) φ ψ))))

private theorem cap_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η)
    (φ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) p)
    (hφ : cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) p φ = 0) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (p + (m + 1)))
      (LocalNativeSupportedCap.cochain (m + 1) (by omega) P v₀ b hρ hρr (p + (m + 1))
        (cochainCup p (m + 1) φ (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη))) = 0 := by
  apply DegreeLoweringCochainPullback.closed
  apply cochainPullback_cocycle
  exact cochainCupZMod2_respects_cocycles p (m + 1) _ _ hφ (LocalNativeBallCupCorrection.evaluation_closed m P v₀ hη)

theorem tested_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + (m + 1)))
      (testedCochain m P v₀ b hρ hρr hη) = 0 :=
  cap_closed m m P v₀ b hρ hρr hη _ (LocalNativeBallPrimitive.tested_closed m P v₀ b)

theorem reduced_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    cochainCoboundary (ZMod 2) (LocalNativeBallCut.space P v₀) ((m + 1) + (m + (m + 1)))
      (reducedCochain m P v₀ b hρ hρr hη) = 0 :=
  cap_closed m m P v₀ b hρ hρr hη _ (LocalNativeBallPrimitive.reduced_closed m P v₀ b)

private theorem cap_outside_zero (m q : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (_hη : 0 < η) (hηr : η + r ≤ 1 / 4)
    (ψ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) q)
    (hψ : ∀ {X : TopCat.{0}} (f : X ⟶ LocalNativeBallCut.space P v₀),
      (∀ x, η ≤ ‖((f x).1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖) →
      cochainPullback f q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
      ((m + 1) + q) (LocalNativeSupportedCap.cochain (m + 1) (by omega) P v₀ b hρ hρr q ψ) = 0 := by
  apply LocalNativeSupportedCap.cochain_outside_zero
  let f := restriction (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
    ((SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ) ⁻¹'
      LocalNativeBallCut.near P v₀ b r) (LocalNativeBallCut.near P v₀ b r) (fun _ h => h)
  have hz := hψ (f ≫ LocalNativeBallOriginalSplit.nearInclusion P v₀ b r)
    (fun x => near_first_far P v₀ b hρ hρr hηr (f x) x.val.property)
  rw [pullback_comp] at hz
  exact hz

theorem correction_outside_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
      ((m + 1) + ((m - 1) + (m + 1))) (correction m hm P v₀ b hρ hρr hη) = 0 :=
  cap_outside_zero m ((m - 1) + (m + 1)) P v₀ b hρ hρr hη hηr _
    (fun f hf => LocalNativeBallCupCorrection.correction_far_zero m hm P v₀ b hη f hf)

private theorem cup_far_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η)
    (φ : singularCochainGroup (ZMod 2) (LocalNativeBallCut.space P v₀) p)
    {X : TopCat.{0}} (f : X ⟶ LocalNativeBallCut.space P v₀)
    (hf : ∀ x, η ≤ ‖((f x).1.val : Ambient (m + 1)) - (LocalNativeBallCut.center P v₀ : Ambient (m + 1))‖) :
    cochainPullback f (p + (m + 1)) (cochainCup p (m + 1) φ (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη)) = 0 := by
  rw [cochainCup_naturality, LocalNativeBallCupCorrection.evaluation_far_zero m P v₀ hη f hf, cochainCup_zero_right]

theorem tested_outside_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
      ((m + 1) + (m + (m + 1))) (testedCochain m P v₀ b hρ hρr hη) = 0 :=
  cap_outside_zero m (m + (m + 1)) P v₀ b hρ hρr hη hηr _
    (fun f hf => cup_far_zero m m P v₀ hη _ f hf)

theorem reduced_outside_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    cochainPullback (SupportedCap.subspaceMap (LocalNativeBallCut.space P v₀) (NativeBallSupportPatch.localGood P v₀)ᶜ)
      ((m + 1) + (m + (m + 1))) (reducedCochain m P v₀ b hρ hρr hη) = 0 :=
  cap_outside_zero m (m + (m + 1)) P v₀ b hρ hρr hη hηr _
    (fun f hf => cup_far_zero m m P v₀ hη _ f hf)

end
end Finsler.LocalNativeCapCorrection
