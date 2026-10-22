module

public import Finsler.Loop.LocalizedCutEvaluationCochain
public import Finsler.Loop.SupportedCutCochainCarrierZero
public import Finsler.Loop.HomotopyRangeRestriction

/-! The ORIGINAL GLOBAL geometric time-cup COCHAIN is literally
zero on every actual H1 family whose start point lies on the fixed
meridian. This includes the ORIGINAL subdivision, Thom cap, degree
transport and whole time prism; it is stronger than split-cup zero
on a post-cap patch and assumes no cycle or closedness of T. -/
@[expose] public section
namespace Finsler.FixedMeridianTimeCupZero
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SupportedSelfCut
open Finsler.MeridianLoopFamily Finsler.LocalizedCutEvaluationCochain
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def carrier {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (SelfCutThomCocycle.parameters n) :=
  {z | ∃ t : _root_.unitInterval, startPoint n z = meridian P v₀ t}

theorem thom_split_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    (push (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) (carrier P v₀))).f ((m + 1) + (p + (m + 1))) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) ≫
      GeometricTimeCupCochain.splitCup m p hr T (m + 1)
        (loopCocycle (m + 1) (by omega) (OppositeMeridianEvaluationPoint.target v₀) hη) = 0 := by
  let X := SelfCutThomCocycle.parameters (m + 1)
  let A := exterior (m + 1) ρ
  let B := neighborhood (m + 1) r
  let C := carrier P v₀
  let f := restriction (SupportedCap.subspaceMap X C) ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)
  have hz := fixed_meridian_splitCup_zero m p P v₀ hη hη1 hr T f (by
    intro x
    exact x.val.property)
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero X A B C
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (cover (m + 1) hρr)
    (m + 1) (p + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (GeometricTimeCupCochain.splitCup m p hr T (m + 1)
      (loopCocycle (m + 1) (by omega) (OppositeMeridianEvaluationPoint.target v₀) hη)) hz

private theorem push_transport {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j) :
    (push f).f i ≫ eqToHom (congrArg (chains Y).X h) =
      eqToHom (congrArg (chains X).X h) ≫ (push f).f j := by
  subst j
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

theorem original_cochain_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) {X : TopCat.{0}}
    (f : X ⟶ Loops (m + 1))
    (hf : ∀ x, ∃ t : _root_.unitInterval, H1FiberBase.point (f x) = meridian P v₀ t) :
    cochainPullback f ((m + p) + (m + 1))
      (GeometricTimeCupCochain.cochain m p hρ hρr hr T (m + 1)
        (loopCocycle (m + 1) (by omega) (OppositeMeridianEvaluationPoint.target v₀) hη)) = 0 := by
  let K := (m + p) + (m + 1)
  let Q := p + (m + 1)
  let C := carrier P v₀
  let H := (SelfCutTimePrism.cylinder (m + 1)).comp (TopCat.Homotopy.refl f)
  have hC : ∀ z : _root_.unitInterval × X, H z ∈ C := fun z => hf z.2
  let R := HomotopyRangeRestriction.restriction H C hC
  let i := SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) C
  have hz := thom_split_zero m p P v₀ hρ hρr hr hη hη1 T
  have ht : K + 1 = (m + 1) + Q := by dsimp [K, Q]; omega
  have hcast : (push i).f (K + 1) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X ht) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component Q ≫
      GeometricTimeCupCochain.splitCup m p hr T (m + 1)
        (loopCocycle (m + 1) (by omega) (OppositeMeridianEvaluationPoint.target v₀) hη) = 0 := by
    rw [← Category.assoc, ← Category.assoc, push_transport i ht]
    simpa only [Category.assoc, comp_zero] using congrArg
      (fun k => eqToHom (congrArg (chains (TopCat.of C)).X ht) ≫ k) hz
  change (push f).f K ≫ (TimeShuffleComparison.rectangle (SelfCutTimePrism.cylinder (m + 1)) K ≫
    eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X ht) ≫
    (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component Q ≫
    GeometricTimeCupCochain.splitCup m p hr T (m + 1)
      (loopCocycle (m + 1) (by omega) (OppositeMeridianEvaluationPoint.target v₀) hη)) = 0
  rw [TimeShuffleComparison.rectangle_eq_prism, ← Category.assoc, TimePrismNaturality.prism_pre]
  have hp := HomotopyRangeRestriction.include_prism H C hC K
  change (R.toSSet.chainComplexMap coeff).hom K (K + 1) ≫ (push i).f (K + 1) =
    (H.toSSet.chainComplexMap coeff).hom K (K + 1) at hp
  rw [← hp]
  simpa only [Category.assoc, comp_zero] using congrArg
    (fun k => (R.toSSet.chainComplexMap coeff).hom K (K + 1) ≫ k) hcast

end
end Finsler.FixedMeridianTimeCupZero
