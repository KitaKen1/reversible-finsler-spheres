module

public import Finsler.Loop.NativeNorthSupportRescaling
public import Finsler.Loop.GlobalCutTimePrismAlignment

/-! Evaluate ACTUAL northern forward cells of the ORIGINAL global
cut-parameter cochain, on the SAME old triple-source double prism.
Support-preserving rescaling identifies its relative class with the
already computed ORIGINAL native class. These are forward-cell values;
no decomposition of the entire global square is asserted. -/
@[expose] public section
namespace Finsler.NativeNorthForwardValues
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem northPair_fst {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopPair.Hom.fst (NativeNorthSupportRescaling.northPair P v₀) = NativeNorthOrderedCharts.northParameters P := by
  apply TopCat.ext
  intro z
  exact TopPair.ofSubsetMap_fst_apply (B := NativePairBoundaryRelativeCut.bad P v₀)
    (B' := (NativeQuarterSupport.good P v₀)ᶜ) (NativeNorthOrderedCharts.northParameters P)
    (fun x hx => (NativeNorthSupportRescaling.ambientHomotopy P).apply_zero x ▸
      NativeNorthSupportRescaling.homotopy_boundary P v₀ 0 x hx) z

def northCocycle (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :=
  RelativeCupCochain.pullback (NativeNorthSupportRescaling.northPair P v₀) ((m + 1) + (p + (m + 1)))
    (NativeQuarterSupport.relativeCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T)

theorem north_closed (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    RelativeCupCochain.differential (NativePairBoundaryRelativeCut.pair P v₀) ((m + 1) + (p + (m + 1)))
      (northCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T) = 0 :=
  CochainClass.closed_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeNorthSupportRescaling.northPair P v₀))
    _ _ (NativeQuarterSupport.relative_closed m p P v₀ b hρ hρr hr hη hr8 hη8 T hT)

theorem north_toAmbient (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) :
    RelativeCupCochain.toAmbient (NativePairBoundaryRelativeCut.pair P v₀) _
      (northCocycle m p P v₀ b hρ hρr hr hη hr8 hη8 T) =
      cochainPullback (NativeNorthOrderedCharts.northParameters P ≫ NativeMeridianPairCoordinates.intoCut P v₀ b)
        ((m + 1) + (p + (m + 1)))
        (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) := by
  rw [northCocycle, RelativeCupCochain.toAmbient_pullback, NativeQuarterSupport.relative_toAmbient, northPair_fst]
  exact (pullback_comp _ _ _ _).symm

theorem north_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) _
      (northCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
      (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _)) =
      NativePairBoundaryRelativeCut.originalPrimitiveClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) := by
  have he := CochainClass.classOf_map (RelativeCup.cx (NativeQuarterSupport.supportPair P v₀))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeNorthSupportRescaling.northPair P v₀))
    ((m + 1) + (m + (m + 1)))
    (NativeQuarterSupport.relativeCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))
    (NativeQuarterSupport.relative_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))
    (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))
  exact he.symm.trans (NativeNorthSupportRescaling.original_support_class_pullback m P v₀ b hρ hρr hr hη hr8 hη8)

theorem cast_closed (Q : TopPair.{0}) {i j : ℕ} (h : i = j)
    (ψ : RelativeCupCochain.relative Q i) (hψ : RelativeCupCochain.differential Q i ψ = 0) :
    RelativeCupCochain.differential Q j (RelativeCupCochain.cast Q h ψ) = 0 := by
  subst j
  exact hψ

theorem cast_class (Q : TopPair.{0}) {i j : ℕ} (h : i = j)
    (ψ : RelativeCupCochain.relative Q i) (hψ : RelativeCupCochain.differential Q i ψ = 0) :
    CochainClass.classOf (RelativeCup.cx Q) j (RelativeCupCochain.cast Q h ψ) (cast_closed Q h ψ hψ) =
      (eqToHom (congrArg (fun k => Q.singularCohomology coeff (ZMod 2) coeff k) h)).hom
        (CochainClass.classOf (RelativeCup.cx Q) i ψ hψ) := by
  subst j
  rfl

theorem cast_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) Y i) :
    cochainCast h (cochainPullback f i φ) = cochainPullback f j (cochainCast h φ) := by
  subst j
  rfl

theorem pre_eq_cast (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) :
    CochainDegreeTransport.pre X h φ = cochainCast h.symm φ := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]
  rfl

def northPrimitive (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  RelativeCupCochain.cast (NativePairBoundaryRelativeCut.pair P v₀) (NativePairDoublePrismSource.degree m)
    (northCocycle m m P v₀ b hρ hρr hr hη hr8 hη8 (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)))

theorem northPrimitive_closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.differential (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8) = 0 :=
  cast_closed _ _ _ (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))

theorem northPrimitive_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    CochainClass.classOf (RelativeCup.cx (NativePairBoundaryRelativeCut.pair P v₀)) (3 * m + 2)
      (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8) (northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8) =
      NativePairDoublePrismSource.primitiveClass m P v₀ b hρ hρr hr hη (by linarith) (by linarith) :=
  (cast_class _ _ _ (north_closed m m P v₀ b hρ hρr hr hη hr8 hη8 _ (classRepr_isCocycle _ m _))).trans
    (congrArg (fun a => (eqToHom (congrArg
      (fun k => (NativePairBoundaryRelativeCut.pair P v₀).singularCohomology coeff (ZMod 2) coeff k)
      (NativePairDoublePrismSource.degree m))).hom a) (north_class m P v₀ b hρ hρr hr hη hr8 hη8))

def forwardCochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :=
  cochainPullback (NativeNorthOrderedCharts.forward P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b))
    (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)

theorem northPrimitive_toAmbient (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    RelativeCupCochain.toAmbient (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
      (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8) = forwardCochain m P v₀ b hρ hρr hr hη := by
  rw [northPrimitive, RelativeCupCochain.toAmbient_cast, north_toAmbient, cast_pullback]
  unfold forwardCochain GlobalCutTimePrismAlignment.parameterCochain
  rw [NativeNorthOrderedCharts.forward_intoCut, pre_eq_cast]

def forwardPairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) : ZMod 2 :=
  ((chains (NativePairDoublePrismSource.source P)).iCycles (3 * m) ≫
    NativePairDoublePrismSource.rawComponent P (3 * m) ≫ forwardCochain m P v₀ b hρ hρr hr hη).hom
      (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)

theorem forwardPairing_original (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    forwardPairing m hm P v₀ b hρ hρr hr hη =
      NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη (by linarith) (by linarith) := by
  have he := NativePairDoublePrismSource.pairing P v₀ (3 * m)
    (northPrimitive m P v₀ b hρ hρr hr hη hr8 hη8)
    (northPrimitive_closed m P v₀ b hρ hρr hr hη hr8 hη8) (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)
  have hc := NativeThetaCoefficientSixQuarters.sourceCycle_class m hm P
  change ((chains (NativePairDoublePrismSource.source P)).homologyπ (3 * m)).hom
    (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = BasedMeridianProducts.tripleSource m hm P at hc
  rw [hc, northPrimitive_class, northPrimitive_toAmbient] at he
  exact he.symm

theorem forward_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    forwardPairing m hm P v₀ b hρ hρr hr hη = if b = 1 then 1 else 0 :=
  (forwardPairing_original m hm P v₀ b hρ hρr hr hη hr8 hη8).trans
    (NativeOriginalBranchValues.branch_value m hm P v₀ b hρ hρr hr hη hr8 hη8)

theorem forward_sum_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (∑ b : Fin 3, forwardPairing m hm P v₀ b hρ hρr hr hη) = 1 := by
  have hs : (∑ b : Fin 3, forwardPairing m hm P v₀ b hρ hρr hr hη) =
      ∑ b : Fin 3, NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη (by linarith) (by linarith) := by
    apply Finset.sum_congr rfl
    intro b _
    exact forwardPairing_original m hm P v₀ b hρ hρr hr hη hr8 hη8
  exact hs.trans (NativeOriginalBranchValues.native_branch_sum_one m hm P v₀ hρ hρr hr hη hr8 hη8)

end
end Finsler.NativeNorthForwardValues
