module

public import Finsler.Loop.NativeWrappedBranchValues

/-! Evaluate ACTUAL northern wrapped cells of the ORIGINAL global
cut-parameter cochain, on the SAME old triple-source double prism.
Support-preserving rescaling identifies its relative class with the
already computed ORIGINAL complementary native class. These are wrapped-cell values;
no decomposition of the entire global square is asserted. -/
@[expose] public section
namespace Finsler.NativeNorthWrappedValues
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def northCocycle (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :=
  RelativeCupCochain.pullback (NativeNorthSupportRescaling.northPair P v₀) ((m + 1) + (p + (m + 1)))
    (NativeWrappedQuarterSupport.relativeCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T)

theorem north_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    RelativeCupCochain.differential (NativePairBoundaryRelativeCut.pair P v₀) ((m + 1) + (p + (m + 1)))
      (northCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeNorthSupportRescaling.northPair P v₀))
    _ _ (NativeWrappedQuarterSupport.relative_closed m p P v₀ b hρ hρr hr hη hr8 hη8 T hT)

theorem north_toAmbient (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.toAmbient (NativePairBoundaryRelativeCut.pair P v₀) _
      (northCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T) =
      cochainPullback (NativeNorthOrderedCharts.northParameters P ≫ NativeWrappedQuarterSupport.intoCut P v₀ b)
        ((m + 1) + (p + (m + 1)))
        (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) := by
  rw [northCocycle, RelativeCupCochain.toAmbient_pullback, NativeWrappedQuarterSupport.relative_ambient, NativeNorthForwardValues.northPair_fst]
  exact (pullback_comp _ _ _ _).symm

theorem north_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) _
      (northCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
      (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _)) =
      NativeWrappedBranchValues.nativeBoundaryClass m P v₀ b hρ hρr hr hη hr8 hη8 := by
  have he := CochainClass.classOf_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeNorthSupportRescaling.northPair P v₀))
    ((m + 1) + (m + (m + 1)))
    (NativeWrappedQuarterSupport.relativeCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
    (NativeWrappedQuarterSupport.relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))
    (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))
  have hs := congrArg (fun f => f.hom (NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8))
    (NativeNorthSupportRescaling.cohomology_equal P v₀ ((m + 1) + (m + (m + 1))))
  exact he.symm.trans hs

def northPrimitive (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  RelativeCupCochain.cast (NativePairBoundaryRelativeCut.pair P v₀) (NativePairDoublePrismSource.degree m)
    (northCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))

theorem northPrimitive_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.differential (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8) = 0 :=
  NativeNorthForwardValues.cast_closed _ _ _ (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))

theorem northPrimitive_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (3 * m + 2)
      (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8) (northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8) =
      NativeWrappedBranchValues.nativePrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8 :=
  (NativeNorthForwardValues.cast_class _ _ _ (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))).trans
    (congrArg (fun a => (eqToHom (congrArg
      (fun k => (NativePairBoundaryRelativeCut.pair P v₀).singularCohomology coeff (ZMod 2) coeff k)
      (NativePairDoublePrismSource.degree m))).hom a) (north_class m P v₀ b hρ hρr hr hη hr8 hη8))

def wrappedCochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :=
  cochainPullback (NativeNorthOrderedCharts.wrapped P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b))
    (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)

theorem northPrimitive_toAmbient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.toAmbient (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8) = wrappedCochain m P v₀ b hρ hρr hr hη := by
  rw [northPrimitive, RelativeCupCochain.toAmbient_cast, north_toAmbient, NativeNorthForwardValues.cast_pullback]
  unfold wrappedCochain GlobalCutTimePrismAlignment.parameterCochain
  rw [NativeNorthWrappedChart.wrapped_intoCut, NativeNorthForwardValues.pre_eq_cast]
  rfl

def wrappedPairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) : ZMod 2 :=
  ((chains (NativePairDoublePrismSource.source P)).iCycles (3 * m) ≫
    NativePairDoublePrismSource.rawComponent P (3 * m) ≫ wrappedCochain m P v₀ b hρ hρr hr hη).hom
      (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)

theorem wrappedPairing_original (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    wrappedPairing m hm P v₀ b hρ hρr hr hη =
      NativeWrappedBranchValues.branchPairing m hm P v₀ b hρ hρr hr hη hr8 hη8 := by
  have he := NativePairDoublePrismSource.pairing P v₀ (3 * m)
    (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8)
    (northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8) (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)
  have hc := NativeThetaCoefficientSixQuarters.sourceCycle_class m hm P
  change ((chains (NativePairDoublePrismSource.source P)).homologyπ (3 * m)).hom
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = BasedMeridianProducts.tripleSource m hm P at hc
  rw [hc, northPrimitive_class, northPrimitive_toAmbient] at he
  exact he.symm

theorem wrapped_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    wrappedPairing m hm P v₀ b hρ hρr hr hη = if b = 1 then 0 else 1 :=
  (wrappedPairing_original m hm P v₀ b hρ hρr hr hη hr8 hη8).trans
    (NativeWrappedBranchValues.branch_value m hm P v₀ b hρ hρr hr hη hr8 hη8)

theorem wrapped_sum_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (∑ b : Fin 3, wrappedPairing m hm P v₀ b hρ hρr hr hη) = 0 := by
  have hs : (∑ b : Fin 3, wrappedPairing m hm P v₀ b hρ hρr hr hη) =
      ∑ b : Fin 3, NativeWrappedBranchValues.branchPairing m hm P v₀ b hρ hρr hr hη hr8 hη8 := by
    apply Finset.sum_congr rfl
    intro b _
    exact wrappedPairing_original m hm P v₀ b hρ hρr hr hη hr8 hη8
  exact hs.trans (NativeWrappedBranchValues.native_wrapped_sum_zero m hm P v₀ hρ hρr hr hη hr8 hη8)

end
end Finsler.NativeNorthWrappedValues
