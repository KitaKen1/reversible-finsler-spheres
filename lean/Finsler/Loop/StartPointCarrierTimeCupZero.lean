module

public import Finsler.Loop.NativeFixedReturnRotationZero

/-! Generalize the verified original full time-cup annihilation to
ANY start-point carrier on which the actual localized sphere
evaluation cocycle is literallyzero. Keep the ORIGINAL subdivision,
supported Thom cap, tested/retained maps and whole time prism. -/
@[expose] public section
namespace Finsler.StartPointCarrierTimeCupZero
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SupportedSelfCut
open Finsler.LocalizedCutEvaluationCochain Finsler.NativeFixedReturnRotationZero
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def parameterCarrier (n : ℕ) (D : Set (BorelEvaluation.sphere n)) : Set (SelfCutThomCocycle.parameters n) :=
  {z | startPoint n z ∈ D}

def loopCarrier (n : ℕ) (D : Set (BorelEvaluation.sphere n)) : Set (Loops n) := {u | H1FiberBase.point u ∈ D}

theorem retained_zero (n : ℕ) (hn : 1 ≤ n) (Q : Sphere n) {η r : ℝ} (hη : 0 < η) (hr : r ≤ 1)
    (D : Set (BorelEvaluation.sphere n))
    (hD : cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere n) D) n
      (LocalizedSphereTopCocycle.cocycle n hn Q hη) = 0)
    {X : TopCat.{0}} (f : X ⟶ TopCat.of (neighborhood n r)) (hf : ∀ x, nearStart n r (f x) ∈ D) :
    cochainPullback f n (cochainPullback (TopCat.ofHom (retained n hr)) n (loopCocycle n hn Q hη)) = 0 := by
  let g : X ⟶ TopCat.of D := TopCat.ofHom ⟨fun x => ⟨nearStart n r (f x), hf x⟩,
    ((nearStart n r).hom.continuous.comp f.hom.continuous).subtype_mk _⟩
  have he : g ≫ SupportedCap.subspaceMap (BorelEvaluation.sphere n) D = f ≫ nearStart n r := by ext x : 1; rfl
  rw [retained_pullback, ← pullback_comp, ← he, pullback_comp, hD]
  simp only [cochainPullback, map_zero]

theorem splitCup_zero (m p : ℕ) (Q : Sphere (m + 1)) {η r : ℝ} (hη : 0 < η) (hr : r ≤ 1)
    (D : Set (BorelEvaluation.sphere (m + 1)))
    (hD : cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere (m + 1)) D) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) Q hη) = 0)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    {X : TopCat.{0}} (f : X ⟶ TopCat.of (neighborhood (m + 1) r)) (hf : ∀ x, nearStart (m + 1) r (f x) ∈ D) :
    cochainPullback f (p + (m + 1))
      (GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) = 0 := by
  rw [GeometricTimeCupCochain.splitCup, cochainCup_naturality,
    retained_zero (m + 1) (by omega) Q hη hr D hD f hf, cochainCup_zero_right]

theorem thom_split_zero (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (D : Set (BorelEvaluation.sphere (m + 1)))
    (hD : cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere (m + 1)) D) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) Q hη) = 0)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    (push (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) (parameterCarrier (m + 1) D))).f
      ((m + 1) + (p + (m + 1))) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) ≫
      GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη) = 0 := by
  let X := SelfCutThomCocycle.parameters (m + 1)
  let A := exterior (m + 1) ρ
  let B := neighborhood (m + 1) r
  let C := parameterCarrier (m + 1) D
  let f := restriction (SupportedCap.subspaceMap X C) ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)
  have hz := splitCup_zero m p Q hη hr D hD T f (fun x => x.val.property)
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero X A B C
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (cover (m + 1) hρr)
    (m + 1) (p + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) hz

private theorem push_transport {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j) :
    (push f).f i ≫ eqToHom (congrArg (chains Y).X h) =
      eqToHom (congrArg (chains X).X h) ≫ (push f).f j := by
  subst j
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

theorem original_cochain_zero (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (D : Set (BorelEvaluation.sphere (m + 1)))
    (hD : cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere (m + 1)) D) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) Q hη) = 0)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) {X : TopCat.{0}}
    (f : X ⟶ Loops (m + 1)) (hf : ∀ x, H1FiberBase.point (f x) ∈ D) :
    cochainPullback f ((m + p) + (m + 1))
      (GeometricTimeCupCochain.cochain m p hρ hρr hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) = 0 := by
  let K := (m + p) + (m + 1)
  let V := p + (m + 1)
  let C := parameterCarrier (m + 1) D
  let H := (SelfCutTimePrism.cylinder (m + 1)).comp (TopCat.Homotopy.refl f)
  have hC : ∀ z : _root_.unitInterval × X, H z ∈ C := fun z => hf z.2
  let R := HomotopyRangeRestriction.restriction H C hC
  let i := SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) C
  have hz := thom_split_zero m p Q hρ hρr hr hη D hD T
  have ht : K + 1 = (m + 1) + V := by dsimp [K, V]; omega
  have hcast : (push i).f (K + 1) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X ht) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component V ≫
      GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη) = 0 := by
    rw [← Category.assoc, ← Category.assoc, push_transport i ht]
    simpa only [Category.assoc, comp_zero] using congrArg
      (fun k => eqToHom (congrArg (chains (TopCat.of C)).X ht) ≫ k) hz
  change (push f).f K ≫ (TimeShuffleComparison.rectangle (SelfCutTimePrism.cylinder (m + 1)) K ≫
    eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X ht) ≫
    (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component V ≫
    GeometricTimeCupCochain.splitCup m p hr T (m + 1) (loopCocycle (m + 1) (by omega) Q hη)) = 0
  rw [TimeShuffleComparison.rectangle_eq_prism, ← Category.assoc, TimePrismNaturality.prism_pre]
  have hp := HomotopyRangeRestriction.include_prism H C hC K
  change (R.toSSet.chainComplexMap coeff).hom K (K + 1) ≫ (push i).f (K + 1) =
    (H.toSSet.chainComplexMap coeff).hom K (K + 1) at hp
  rw [← hp]
  simpa only [Category.assoc, comp_zero] using congrArg
    (fun k => (R.toSSet.chainComplexMap coeff).hom K (K + 1) ≫ k) hcast

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h φ) =
      CochainDegreeTransport.pre X h (cochainPullback f j φ) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem cast_family_zero (m : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (D : Set (BorelEvaluation.sphere (m + 1)))
    (hD : cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere (m + 1)) D) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) Q hη) = 0)
    {X : TopCat.{0}} (f : X ⟶ Loops (m + 1)) (hf : ∀ x, H1FiberBase.point (f x) ∈ D) :
    cochainPullback f (3 * m + 1) (castCochain m Q hη hρ hρr hr) = 0 := by
  have hz := original_cochain_zero m m Q hρ hρr hr hη D hD
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) f hf
  change cochainPullback f ((m + m) + (m + 1))
    (LocalizedThetaCutCoefficient.cochain m Q hη hρ hρr hr) = 0 at hz
  rw [castCochain, pullback_pre, hz, CochainDegreeTransport.pre, comp_zero]

theorem homotopy_prism_zero (m : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (D : Set (BorelEvaluation.sphere (m + 1)))
    (hD : cochainPullback (SupportedCap.subspaceMap (BorelEvaluation.sphere (m + 1)) D) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) Q hη) = 0)
    {X : TopCat.{0}} {f g : X ⟶ Loops (m + 1)} (H : TopCat.Homotopy f g)
    (hH : ∀ z : _root_.unitInterval × X, H1FiberBase.point (H z) ∈ D) :
    (H.toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ castCochain m Q hη hρ hρr hr = 0 := by
  have hp := HomotopyRangeRestriction.include_prism H (loopCarrier (m + 1) D) hH (3 * m)
  have hz := cast_family_zero m Q hρ hρr hr hη D hD
    (SupportedCap.subspaceMap (Loops (m + 1)) (loopCarrier (m + 1) D)) (fun x => x.property)
  change (push (SupportedCap.subspaceMap (Loops (m + 1)) (loopCarrier (m + 1) D))).f (3 * m + 1) ≫
    castCochain m Q hη hρ hρr hr = 0 at hz
  rw [← hp, Category.assoc, hz, comp_zero]

end
end Finsler.StartPointCarrierTimeCupZero
