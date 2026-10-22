module

public import Finsler.Loop.LocalizedThetaCutCoefficient
public import Finsler.Loop.NativeTripleSelfEvaluation

/-! Apply the ORIGINAL full time-cup cochain zero to the SIX actual
fixed-return quarter prisms of the SAME native triple rotation.
No cycle premise is used for these prism annihilation identities. -/
@[expose] public section
namespace Finsler.NativeFixedReturnRotationZero
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily
open Finsler.MeridianTripleQuarterClocks Finsler.NativeTripleSelfEvaluation Finsler.SobolevShift
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def loopCarrier {n : ℕ} (P : Sphere n) (v₀ : equator P) : Set (Loops n) :=
  {u | ∃ t : _root_.unitInterval, H1FiberBase.point u = meridian P v₀ t}

def castCochain (m : ℕ) (Q : Sphere (m + 1)) {η ρ r : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :=
  CochainDegreeTransport.pre (Loops (m + 1)) (by omega : 3 * m + 1 = (m + m) + (m + 1))
    (LocalizedThetaCutCoefficient.cochain m Q hη hρ hρr hr)

theorem cast_closed (m : ℕ) (Q : Sphere (m + 1)) {η ρ r : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (3 * m + 1) (castCochain m Q hη hρ hρr hr) = 0 :=
  CochainDegreeTransport.closed _ _ _ (LocalizedThetaCutCoefficient.closed m Q hη hρ hρr hr)

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h φ) =
      CochainDegreeTransport.pre X h (cochainPullback f j φ) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem carrier_cochain_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    cochainPullback (SupportedCap.subspaceMap (Loops (m + 1)) (loopCarrier P v₀)) (3 * m + 1)
      (castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr) = 0 := by
  have hz := LocalizedThetaCutCoefficient.fixed_meridian_zero m P v₀ hη hη1 hρ hρr hr
    (SupportedCap.subspaceMap (Loops (m + 1)) (loopCarrier P v₀)) (fun x => x.property)
  rw [castCochain, pullback_pre, hz, CochainDegreeTransport.pre, comp_zero]

theorem homotopy_prism_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    {X : TopCat.{0}} {f g : X ⟶ Loops (m + 1)} (H : TopCat.Homotopy f g)
    (hH : ∀ z : _root_.unitInterval × X, H z ∈ loopCarrier P v₀) :
    (H.toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫
      castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr = 0 := by
  have hp := HomotopyRangeRestriction.include_prism H (loopCarrier P v₀) hH (3 * m)
  have hz := carrier_cochain_zero m P v₀ hη hη1 hρ hρr hr
  change (push (SupportedCap.subspaceMap (Loops (m + 1)) (loopCarrier P v₀))).f (3 * m + 1) ≫
    castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr = 0 at hz
  rw [← hp, Category.assoc, hz, comp_zero]

abbrev parameters {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (NativeH1TripleMeridian.parameters P)

def quarterFamily {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : Fin 4) :
    TopCat.of (_root_.unitInterval × parameters P) ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => shiftSphere (NativeH1TripleMeridian.native P v₀ z.2) (clock k q z.1), by
    have ht : Continuous (fun z : _root_.unitInterval × parameters P =>
        (⟨clock k q z.1, clock_mem k q z.1⟩ : _root_.unitInterval)) := by
      fin_cases k <;> dsimp [clock, localTime] <;> fun_prop
    have hp := ht.prodMk ((NativeH1TripleMeridian.continuous_native P v₀).comp continuous_snd)
    have hc := (H1LoopRotation.homotopy n).continuous.comp hp
    exact hc.congr (fun _ => rfl)⟩

def endpointMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : Fin 4)
    (t : _root_.unitInterval) : parameters P ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => quarterFamily P v₀ k q (t, z),
    (quarterFamily P v₀ k q).hom.continuous.comp (continuous_const.prodMk continuous_id)⟩

def quarterHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : Fin 4) :
    TopCat.Homotopy (endpointMap P v₀ k q 0) (endpointMap P v₀ k q 1) where
  toFun := quarterFamily P v₀ k q
  continuous_toFun := (quarterFamily P v₀ k q).hom.continuous
  map_zero_left _ := rfl
  map_one_left _ := rfl

def fixedQuarter (q : Fin 2) : Fin 4 := ⟨q.val + 2, by omega⟩

theorem fixed_piece_range {n : ℕ} (P : Sphere n) (v₀ v : equator P) (q : Fin 2)
    (t : _root_.unitInterval) : ∃ s : _root_.unitInterval, piece P v₀ v (fixedQuarter q) t = meridian P v₀ s := by
  fin_cases q
  · refine ⟨MeridianQuarterIncidence.southTime (unitInterval.symm t), ?_⟩
    exact (MeridianQuarterIncidence.south_meridian P v₀ (unitInterval.symm t)).symm
  · refine ⟨MeridianQuarterIncidence.northTime (unitInterval.symm t), ?_⟩
    exact (MeridianQuarterIncidence.north_meridian P v₀ (unitInterval.symm t)).symm

theorem quarter_range {n : ℕ} (P : Sphere n) (v₀ : equator P) (k : Fin 3) (q : Fin 2)
    (z : _root_.unitInterval × parameters P) : quarterHomotopy P v₀ k (fixedQuarter q) z ∈ loopCarrier P v₀ := by
  change ∃ t : _root_.unitInterval,
    H1FiberBase.point (shiftSphere (NativeH1TripleMeridian.native P v₀ z.2) (clock k (fixedQuarter q) z.1)) = meridian P v₀ t
  rw [point_shift, circle_quarter]
  exact fixed_piece_range P v₀ _ q z.1

theorem fixed_quarter_prism_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (q : Fin 2)
    {η ρ r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    ((quarterHomotopy P v₀ k (fixedQuarter q)).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫
      castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr = 0 :=
  homotopy_prism_zero m P v₀ hη hη1 hρ hρr hr _ (quarter_range P v₀ k q)

end
end Finsler.NativeFixedReturnRotationZero
