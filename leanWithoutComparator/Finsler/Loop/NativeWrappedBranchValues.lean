module

public import Finsler.Loop.NativeWrappedGraphClass
public import Finsler.Loop.NativeNorthForwardValues

/-! Values of the SAME ORIGINAL complementary native full cut:
1,0,1 at the SAME rho<r,r,eta<=1/8. Actual support-class descent,
existing double-prism input, true degree casts and exact fundamental
pairing are retained. This is NOT an OLD GLOBAL square-sum theorem. -/
@[expose] public section
namespace Finsler.NativeWrappedBranchValues
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport Finsler.SmallChainCarrier Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

def nativeBoundaryClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (NativeQuarterSupport.boundaryToSupport P v₀)
    ((m + 1) + (m + (m + 1)))).hom (NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8)

def nativePrimitiveClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  (eqToHom (congrArg (fun k => (NativePairBoundaryRelativeCut.pair P v₀).singularCohomology coeff (ZMod 2) coeff k)
    (NativePairDoublePrismSource.degree m))).hom (nativeBoundaryClass m P v₀ b hρ hρr hr hη hr8 hη8)

def graphPrimitiveClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  (eqToHom (congrArg (fun k => (graphPair P v₀).singularCohomology coeff (ZMod 2) coeff k)
    (NativePairDoublePrismSource.degree m))).hom (NativeWrappedGraphClass.boundaryClass m P v₀ b hρ hρr hr hη hr8 hη8)

theorem pullback_degree_cast {P Q : TopPair.{0}} (f : P ⟶ Q) {i j : ℕ} (h : i = j)
    (a : Q.singularCohomology coeff (ZMod 2) coeff i) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f j).hom
      ((eqToHom (congrArg (fun k => Q.singularCohomology coeff (ZMod 2) coeff k) h)).hom a) =
      (eqToHom (congrArg (fun k => P.singularCohomology coeff (ZMod 2) coeff k) h)).hom
        ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f i).hom a) := by
  subst j
  rfl

theorem graphPrimitiveClass_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (nativeToGraph P v₀) (3 * m + 2)).hom
      (graphPrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8) = nativePrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8 := by
  have he := pullback_degree_cast (nativeToGraph P v₀) (NativePairDoublePrismSource.degree m)
    (NativeWrappedGraphClass.boundaryClass m P v₀ b hρ hρr hr hη hr8 hη8)
  exact he.trans (congrArg (fun a =>
    (eqToHom (congrArg (fun k => (NativePairBoundaryRelativeCut.pair P v₀).singularCohomology coeff (ZMod 2) coeff k)
      (NativePairDoublePrismSource.degree m))).hom a)
        (NativeQuarterGraphDescent.graphClass_pullback P v₀ _ (NativeWrappedQuarterSupport.supportClass m P v₀ b hρ hρr hr hη hr8 hη8)))

def branchPairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) : ZMod 2 :=
  RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
    (nativePrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8) (NativePairDoublePrismSource.inputClass m hm P v₀)

def absoluteClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :=
  (relativeToPool (graphPair P v₀) (3 * m + 2)).hom (graphPrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8)

theorem branchPairing_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    branchPairing m hm P v₀ b hρ hρr hr hη hr8 hη8 =
      (kroneckerMap (graphSpace P) (3 * m + 2)).hom (absoluteClass m P v₀ b hρ hρr hr hη hr8 hη8)
        (NativeDoubleFundamentalImage.fundamentalImage m hm P) := by
  have he := pairing_transport m hm P v₀ (graphPrimitiveClass m P v₀ b hρ hρr hr hη hr8 hη8)
  have hc := congrArg (fun a => RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀)
    (3 * m + 2) a (NativePairDoublePrismSource.inputClass m hm P v₀)) (graphPrimitiveClass_pullback m P v₀ b hρ hρr hr hη hr8 hη8)
  exact (hc.symm.trans he).trans (NativeDoubleFundamentalImage.relative_pairing_fundamental m hm P v₀ _)

theorem relative_cast {Q : TopPair.{0}} {i j : ℕ} (h : i = j)
    (a : Q.singularCohomology coeff (ZMod 2) coeff i) :
    (relativeToPool Q j).hom ((eqToHom (congrArg (fun k => Q.singularCohomology coeff (ZMod 2) coeff k) h)).hom a) =
      CupUnit.absoluteCast Q.fst h ((relativeToPool Q i).hom a) := by
  subst j
  rfl

theorem absolute_cast_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (a : cohomologyZMod2 Y i) :
    CupUnit.absoluteCast X h ((cohPullback f i).hom a) = (cohPullback f j).hom (CupUnit.absoluteCast Y h a) := by
  subst j
  rfl

theorem absolute_adjacent (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) (hb : b ≠ 1) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    absoluteClass m P v₀ b hρ hρr hr hη hr8 hη8 =
      CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (NativeExplicitGraphClass.explicitClass m P v₀) :=
  (relative_cast (Q := graphPair P v₀) (NativePairDoublePrismSource.degree m)
    (NativeWrappedGraphClass.boundaryClass m P v₀ b hρ hρr hr hη hr8 hη8)).trans
    ((congrArg (CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m))
      (NativeWrappedGraphClass.absolute_uncast_adjacent m hm P v₀ b hb hρ hρr hr hη hr8 hη8)).trans
      ((absolute_cast_pullback (NativeCutPointSwap.graphSwap P) (NativePairDoublePrismSource.degree m)
        (NativeExplicitGraphClass.explicitClass m P v₀)).trans (NativeGraphPointSwapClass.actual_cast_class_swap m P v₀)))

theorem absolute_nonadjacent_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    absoluteClass m P v₀ 1 hρ hρr hr hη hr8 hη8 = 0 := by
  unfold absoluteClass graphPrimitiveClass
  rw [NativeWrappedGraphClass.boundary_nonadjacent_zero m hm P v₀ hρ hρr hr hη hr8 hη8, map_zero, map_zero]

theorem branch_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    branchPairing m hm P v₀ b hρ hρr hr hη hr8 hη8 = if b = 1 then 0 else 1 := by
  rw [branchPairing_fundamental]
  by_cases hb : b = 1
  · subst b
    rw [absolute_nonadjacent_zero m hm P v₀ hρ hρr hr hη hr8 hη8, map_zero, LinearMap.zero_apply, ite_eq_left rfl]
  · rw [absolute_adjacent m hm P v₀ b hb hρ hρr hr hη hr8 hη8, ite_eq_right hb]
    exact NativeGraphFundamentalScalar.scalar_one m hm P v₀

theorem native_wrapped_sum_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (∑ b : Fin 3, branchPairing m hm P v₀ b hρ hρr hr hη hr8 hη8) = 0 := by
  simp only [Fin.sum_univ_three, branch_value m hm P v₀ _ hρ hρr hr hη hr8 hη8]
  norm_num
  decide

end
end Finsler.NativeWrappedBranchValues
