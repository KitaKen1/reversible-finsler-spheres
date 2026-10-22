module

public import Finsler.Loop.NativeCutGraphDescent

/-! The SAME original native branch scalar equals an ACTUAL graph
relative pairing, and hence the absolute Kronecker pairing of the
ACTUALLY descended class on the EXISTING fundamental product.
Only the true degree equality is cast; no numeric value or global
Theta branch-sum identity is assumed. -/
@[expose] public section
namespace Finsler.NativeGraphBranchPairing
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

private theorem pullback_degree_cast {P Q : TopPair.{0}} (f : P ⟶ Q) {i j : ℕ} (h : i = j)
    (a : Q.singularCohomology coeff (ZMod 2) coeff i) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f j).hom
      ((eqToHom (congrArg (fun k => Q.singularCohomology coeff (ZMod 2) coeff k) h)).hom a) =
        (eqToHom (congrArg (fun k => P.singularCohomology coeff (ZMod 2) coeff k) h)).hom
          ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f i).hom a) := by
  subst j
  rfl

def primitiveClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :=
  (eqToHom (congrArg (fun k => (graphPair P v₀).singularCohomology coeff (ZMod 2) coeff k)
    (NativePairDoublePrismSource.degree m))).hom
      (NativeCutGraphDescent.originalGraphClass m P v₀ b hρ hρr hr hη hr4 hη4)

theorem primitiveClass_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) (nativeToGraph P v₀) (3 * m + 2)).hom
      (primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4) =
      NativePairDoublePrismSource.primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4 := by
  have he := pullback_degree_cast (nativeToGraph P v₀) (NativePairDoublePrismSource.degree m)
    (NativeCutGraphDescent.originalGraphClass m P v₀ b hρ hρr hr hη hr4 hη4)
  rw [NativeCutGraphDescent.originalGraphClass_pullback] at he
  exact he

theorem original_branchPairing_graph (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη hr4 hη4 =
      RelativeKronecker.comparison (graphPair P v₀) (3 * m + 2)
        (primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4) (graphInputClass m hm P v₀) := by
  have he := pairing_transport m hm P v₀ (primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4)
  have hc := congrArg (fun a => RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀)
    (3 * m + 2) a (NativePairDoublePrismSource.inputClass m hm P v₀))
      (primitiveClass_pullback m P v₀ b hρ hρr hr hη hr4 hη4)
  exact hc.symm.trans he

def absoluteClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :=
  (relativeToPool (graphPair P v₀) (3 * m + 2)).hom (primitiveClass m P v₀ b hρ hρr hr hη hr4 hη4)

theorem original_branchPairing_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr4 : r ≤ 1 / 4) (hη4 : η ≤ 1 / 4) :
    NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη hr4 hη4 =
      (kroneckerMap (graphSpace P) (3 * m + 2)).hom
        (absoluteClass m P v₀ b hρ hρr hr hη hr4 hη4) (NativeDoubleFundamentalImage.fundamentalImage m hm P) :=
  (original_branchPairing_graph m hm P v₀ b hρ hρr hr hη hr4 hη4).trans
    (NativeDoubleFundamentalImage.relative_pairing_fundamental m hm P v₀ _)

end
end Finsler.NativeGraphBranchPairing
