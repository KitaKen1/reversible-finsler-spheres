module

public import Finsler.Loop.NativeCutPointSwap

/-! SAME original parameter cochain on ACTUAL complementary native
cuts, with its genuine quarter-supported relative lift. Exchanging
native point coordinates straightens the original self-evaluation;
no numeric full-cap value or global cell gluing is assumed. -/
@[expose] public section
namespace Finsler.NativeWrappedQuarterSupport
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMeridianPairCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :=
  NativeMeridianPairCoordinates.intoCut P v₀ b ≫ WholeSelfCutComplement.complement n

def straightenedIntoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :=
  NativeCutPointSwap.nativeSwap P ≫ intoCut P v₀ b

theorem selfEvaluation_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    SelfCutThomCocycle.selfEvaluation n (intoCut P v₀ b z) =
      (meridian P z.2.1.2 z.2.1.1, meridian P z.1.2 z.1.1) := by
  have he := ConcreteCategory.congr_hom (WholeSelfCutComplement.selfEvaluation_exchange n)
    (NativeMeridianPairCoordinates.intoCut P v₀ b z)
  exact he.trans (congrArg Prod.swap (NativeMeridianPairCoordinates.selfEvaluation_value n P v₀ b z))

theorem straightened_selfEvaluation_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    SelfCutThomCocycle.selfEvaluation n (straightenedIntoCut P v₀ b z) =
      (meridian P z.1.2 z.1.1, meridian P z.2.1.2 z.2.1.1) :=
  selfEvaluation_value P v₀ b (NativeCutPointSwap.nativeSwap P z)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem farCarrier_of_pair (n : ℕ) (Q : Sphere n) (D : ℝ) (z : SelfCutThomCocycle.parameters n)
    (a c : Sphere n) (h : SelfCutThomCocycle.selfEvaluation n z = (a, c))
    (hf : D ≤ ‖(a : Ambient n) - (Q : Ambient n)‖ ∨ D ≤ ‖(c : Ambient n) - (Q : Ambient n)‖) :
    z ∈ LocalizedParameterCutCochain.farCarrier n Q D := by
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change H1FiberBase.point z.2 = a at hl
  change H1SelfCutNeighborhood.endpoint z = c at hr
  change D ≤ ‖(H1FiberBase.point z.2 : Ambient n) - (Q : Ambient n)‖ ∨
    D ≤ ‖(H1SelfCutNeighborhood.endpoint z : Ambient n) - (Q : Ambient n)‖
  rw [hl, hr]
  exact hf

theorem outside_farCarrier {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (z : parameters P) (hz : z ∉ NativeQuarterSupport.good P v₀) :
    intoCut P v₀ b z ∈ LocalizedParameterCutCochain.farCarrier n (NorthMeridianEvaluationPoint.target P v₀) (1 / 4) := by
  apply farCarrier_of_pair n (NorthMeridianEvaluationPoint.target P v₀) (1 / 4) (intoCut P v₀ b z)
    (meridian P z.2.1.2 z.2.1.1) (meridian P z.1.2 z.1.1) (selfEvaluation_value P v₀ b z)
  by_cases h : ‖(meridian P z.1.2 z.1.1 : Ambient n) - (NorthMeridianEvaluationPoint.target P v₀ : Ambient n)‖ < 1 / 4
  · left
    exact le_of_not_gt (fun h₂ => hz ⟨h, h₂⟩)
  · right
    exact le_of_not_gt h

def cochain (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :=
  cochainPullback (intoCut P v₀ b) ((m + 1) + (p + (m + 1)))
    (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T)

theorem closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    cochainCoboundary (ZMod 2) (parameters P) ((m + 1) + (p + (m + 1))) (cochain m p P v₀ b hρ hρr hr hη T) = 0 :=
  pullback_closed (intoCut P v₀ b) _ _ (LocalizedParameterCutCochain.closed m p _ hρ hρr hr hη T hT)

theorem outside_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    cochainPullback (SupportedCap.subspaceMap (parameters P) (NativeQuarterSupport.good P v₀)ᶜ)
      ((m + 1) + (p + (m + 1))) (cochain m p P v₀ b hρ hρr hr hη T) = 0 := by
  rw [cochain, ← pullback_comp]
  exact LocalizedParameterCutCochain.family_zero m p _ hρ hρr hr hη (by linarith : η + r ≤ (1 / 4 : ℝ)) T
    (SupportedCap.subspaceMap (parameters P) (NativeQuarterSupport.good P v₀)ᶜ ≫ intoCut P v₀ b)
    (fun z => outside_farCarrier P v₀ b z.val z.property)

def relativeCocycle (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :=
  (RelativeCupCochain.exists_lift (NativeQuarterSupport.supportPair P v₀) _ (cochain m p P v₀ b hρ hρr hr hη T)
    (outside_zero m p P v₀ b hρ hρr hr hη hr8 hη8 T)).choose

theorem relative_ambient (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.toAmbient (NativeQuarterSupport.supportPair P v₀) _
      (relativeCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T) = cochain m p P v₀ b hρ hρr hr hη T :=
  (RelativeCupCochain.exists_lift (NativeQuarterSupport.supportPair P v₀) _ (cochain m p P v₀ b hρ hρr hr hη T)
    (outside_zero m p P v₀ b hρ hρr hr hη hr8 hη8 T)).choose_spec

theorem relative_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    RelativeCupCochain.differential (NativeQuarterSupport.supportPair P v₀) _
      (relativeCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (NativeQuarterSupport.supportPair P v₀) _
  rw [RelativeCupCochain.toAmbient_differential, relative_ambient, map_zero]
  exact closed m p P v₀ b hρ hρr hr hη T hT

def supportClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  CochainClass.classOf (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀)) _
    (relativeCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
    (relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))

def nativePairSwap {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    NativeQuarterSupport.supportPair P v₀ ⟶ NativeQuarterSupport.supportPair P v₀ :=
  TopPair.ofSubsetMap (B := (NativeQuarterSupport.good P v₀)ᶜ) (B' := (NativeQuarterSupport.good P v₀)ᶜ)
    (NativeCutPointSwap.nativeSwap P) (fun z hz hg => hz ((NativeCutPointSwap.native_good P v₀ z).mp hg))

theorem nativePairSwap_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Hom.fst (nativePairSwap P v₀) = NativeCutPointSwap.nativeSwap P := by
  apply TopCat.ext
  intro z
  exact TopPair.ofSubsetMap_fst_apply (B := (NativeQuarterSupport.good P v₀)ᶜ) (B' := (NativeQuarterSupport.good P v₀)ᶜ)
    (NativeCutPointSwap.nativeSwap P) (fun x hx hg => hx ((NativeCutPointSwap.native_good P v₀ x).mp hg)) z

end
end Finsler.NativeWrappedQuarterSupport
