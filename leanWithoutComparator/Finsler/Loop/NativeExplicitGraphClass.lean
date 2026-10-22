module

public import Finsler.Loop.NativeExplicitGraphIdentification
public import Finsler.Loop.SupportedCapCochainClass

/-! Compute the ACTUAL absolute class of the explicit global graph cap,
then of the SAME ORIGINAL nonadjacent native branch. Only actual class
identities and true degree casts are used; no scalar is assigned yet. -/
@[expose] public section
namespace Finsler.NativeExplicitGraphClass
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def firstTop (m : ℕ) (P : Sphere (m + 1)) :=
  (cohPullback (NativeExplicitGraphCap.first P) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))
def secondTop (m : ℕ) (P : Sphere (m + 1)) :=
  (cohPullback (snd (BorelEvaluation.sphere (m + 1)) (NativeExplicitGraphCap.tail P)) (m + 1)).hom
    ((cohPullback (NativeExplicitGraphCap.second P) (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega)))
def remainingClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  (cohPullback (NativeExplicitGraphCap.remaining P) m).hom (LocalNativeBallPrimitive.remainingClass m P v₀)
def explicitClass (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :=
  cupZMod2 (firstTop m P + secondTop m P) (cupZMod2 (remainingClass m P v₀) (firstTop m P))

theorem remaining_cocycle_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    cocycleClass (graphSpace P) m (NativeExplicitGraphCap.remainingCocycle m P v₀)
      (NativeExplicitGraphCap.remaining_closed m P v₀) = remainingClass m P v₀ := by
  have he := cohPullback_cocycleClass (NativeExplicitGraphCap.remaining P) m
    (classRepr (TopCat.of (equator P)) m (LocalNativeBallPrimitive.remainingClass m P v₀)) (classRepr_isCocycle _ m _)
  rw [cocycleClass_classRepr] at he
  exact he.symm

theorem evaluation_cocycle_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cocycleClass (graphSpace P) (m + 1) (NativeExplicitGraphCap.evaluationCocycle m P v₀ hη)
      (NativeExplicitGraphCap.evaluation_closed m P v₀ hη) = firstTop m P := by
  have he := cohPullback_cocycleClass (NativeExplicitGraphCap.first P) (m + 1)
    (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)
    (LocalizedSphereTopCocycle.closed _ (by omega) _ hη)
  have hc : cocycleClass (BorelEvaluation.sphere (m + 1)) (m + 1)
      (LocalizedSphereTopCocycle.cocycle (m + 1) (by omega) (LocalNativeBallCut.center P v₀) hη)
      (LocalizedSphereTopCocycle.closed _ (by omega) _ hη) = SphereTopClass.topClass (m + 1) (by omega) :=
    LocalizedSphereTopCocycle.top_class _ (by omega) _ hη
  exact he.symm.trans (congrArg (cohPullback (NativeExplicitGraphCap.first P) (m + 1)).hom hc)

theorem split_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cocycleClass (graphSpace P) (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη)
      (NativeExplicitGraphCap.split_closed m P v₀ hη) = cupZMod2 (remainingClass m P v₀) (firstTop m P) := by
  have he := (cupZMod2_mk (NativeExplicitGraphCap.remainingCocycle m P v₀)
    (NativeExplicitGraphCap.remaining_closed m P v₀) (NativeExplicitGraphCap.evaluationCocycle m P v₀ hη)
    (NativeExplicitGraphCap.evaluation_closed m P v₀ hη)).symm
  rw [remaining_cocycle_class, evaluation_cocycle_class] at he
  exact he

theorem cochain_class (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) :
    cocycleClass (graphSpace P) ((m + 1) + (m + (m + 1))) (NativeExplicitGraphCap.cochain m P v₀ hρ hρr hη)
      (NativeExplicitGraphCap.cochain_closed m P v₀ hρ hρr hη) = explicitClass m P v₀ := by
  have he := SupportedCapCochainClass.supported_cap_cup (graphSpace P)
    (NativeExplicitGraphCap.exterior P ρ) (NativeExplicitGraphCap.near P r)
    (NormalizedSphereGraphCap.exterior_open (m + 1) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) ρ) (NormalizedSphereGraphCap.neighborhood_open (m + 1) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) r)
    (NormalizedSphereGraphCap.cover (m + 1) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρr) (m + 1) (m + (m + 1)) (by omega)
    (NormalizedSphereGraphCap.cocycle (m + 1) (by omega) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ)
    (NativeExplicitGraphCap.split m P v₀ hη) (NormalizedSphereGraphCap.cocycle_supported (m + 1) (by omega) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ)
    (NormalizedSphereGraphCap.cocycle_closed (m + 1) (by omega) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ) (NativeExplicitGraphCap.split_closed m P v₀ hη)
  have hd : cocycleClass (graphSpace P) (m + 1)
      (NormalizedSphereGraphCap.cocycle (m + 1) (by omega) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ)
      (NormalizedSphereGraphCap.cocycle_closed (m + 1) (by omega) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ) =
      firstTop m P + secondTop m P :=
    NormalizedSphereGraphCap.cocycle_class (m + 1) (by omega) (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P) hρ
  exact he.trans (congrArg₂ (fun a b => cupZMod2 a b) hd (split_class m P v₀ hη))

theorem support_absolute (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hη : 0 < η) (hηr : η + r ≤ 1 / 4) :
    (relativeToPool (NativeQuarterGraphDescent.graphSupportPair P v₀) ((m + 1) + (m + (m + 1)))).hom
      (NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη hηr) = explicitClass m P v₀ :=
  (RelativeCup.relativeToPool_classOf _ _ (NativeExplicitGraphCap.relativeCocycle m P v₀ hρ hρr hη hηr)
    (NativeExplicitGraphCap.relative_closed m P v₀ hρ hρr hη hηr)).trans
      ((CochainClass.classOf_congr _ _ (NativeExplicitGraphCap.relative_ambient m P v₀ hρ hρr hη hηr) _ _).trans
        (cochain_class m P v₀ hρ hρr hη))

theorem original_boundary_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeCutGraphDescent.originalGraphClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith) =
      (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
        (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) ((m + 1) + (m + (m + 1)))).hom
        (NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη (by linarith)) := by
  have he := NativeQuarterGraphCompatibility.original_graph_class_eq m P v₀ 1 hρ hρr hr hη hr8 hη8
  have hc := NativeExplicitGraphIdentification.support_class_eq m hm P v₀ hρ hρr hr hη hr8 hη8
  exact he.symm.trans (congrArg
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) _).hom hc)

private theorem pullback_id (X : TopCat.{0}) (q : ℕ) (a : cohomologyZMod2 X q) :
    (cohPullback (𝟙 X) q).hom a = a := by
  exact ConcreteCategory.congr_hom ((singularCohomologyZMod2 q).map_id (Opposite.op X)) a

theorem original_absolute_uncast (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (relativeToPool (graphPair P v₀) ((m + 1) + (m + (m + 1)))).hom
      (NativeCutGraphDescent.originalGraphClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith)) = explicitClass m P v₀ := by
  rw [original_boundary_class m hm P v₀ hρ hρr hr hη hr8 hη8]
  have he := ConcreteCategory.congr_hom (relative_to_absolute_natural (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀)
    ((m + 1) + (m + (m + 1)))) (NativeExplicitGraphCap.supportClass m P v₀ hρ hρr hη (by linarith))
  have hf : TopPair.Hom.fst (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) = 𝟙 (graphSpace P) := by
    apply TopCat.ext
    intro z
    exact TopPair.ofSubsetMap_fst_apply (𝟙 (graphSpace P)) (NativeQuarterGraphDescent.graphBoundary_outside P v₀) z
  change (relativeToPool (graphPair P v₀) _).hom
    ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀) _).hom _) =
    (cohPullback (TopPair.Hom.fst (NativeQuarterGraphDescent.graphBoundaryToSupport P v₀)) _).hom _ at he
  rw [hf] at he
  exact he.trans ((pullback_id (graphSpace P) _ _).trans (support_absolute m P v₀ hρ hρr hη (by linarith)))

private theorem relative_cast {P : TopPair.{0}} {i j : ℕ} (h : i = j)
    (a : P.singularCohomology coeff (ZMod 2) coeff i) :
    (relativeToPool P j).hom ((eqToHom (congrArg (fun k => P.singularCohomology coeff (ZMod 2) coeff k) h)).hom a) =
      CupUnit.absoluteCast P.fst h ((relativeToPool P i).hom a) := by
  subst j
  rfl

theorem original_absolute_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeGraphBranchPairing.absoluteClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith) =
      CupUnit.absoluteCast (graphSpace P) (NativePairDoublePrismSource.degree m) (explicitClass m P v₀) := by
  have he := relative_cast (P := graphPair P v₀) (NativePairDoublePrismSource.degree m)
    (NativeCutGraphDescent.originalGraphClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith))
  rw [original_absolute_uncast m hm P v₀ hρ hρr hr hη hr8 hη8] at he
  exact he

end
end Finsler.NativeExplicitGraphClass
