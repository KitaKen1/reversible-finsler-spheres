module

public import Finsler.Loop.CommonCoverLocalizedCapNaturality
public import Finsler.Loop.CylinderPrismNaturality
public import Finsler.Loop.SupportedThomTimeRefinement
public import Finsler.Loop.RegradedMappedCapTimeComparison

/-! Actual source-map naturality for supported first-Thom TIME.
Both cap lifts and the endpoint-relative common-cover comparison are
constructed from actual pullbacks. No homology injectivity is assumed. -/

@[expose] public section
namespace Finsler.CylinderSupportedThomNaturality
open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

variable {X Y : TopCat.{0}} (e : X ⟶ Y)
  (A B : Set (ClosedInterval × Y)) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × Y)) (d + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Y)) A) (d + 1) φ = 0)
  (hφ : cochainCoboundary (ZMod 2) (TopCat.of (ClosedInterval × Y)) (d + 1) φ = 0)
  (C : Set (ClosedInterval × Y))
  (hC : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Y)) C) (d + 1) φ = 0)
  (h₀ : ∀ y, ((0 : ClosedInterval), y) ∈ C) (h₁ : ∀ y, ((1 : ClosedInterval), y) ∈ C)

def nearMap : TopCat.of ((CylinderPrismNaturality.map e) ⁻¹' B) ⟶ TopCat.of B :=
  restriction (CylinderPrismNaturality.map e) _ B (fun _ hz => hz)

def sourceOperation :=
  SupportedThomTime.operation (TopCat.of (ClosedInterval × X))
    ((CylinderPrismNaturality.map e) ⁻¹' A) ((CylinderPrismNaturality.map e) ⁻¹' B)
    (hA.preimage (CylinderPrismNaturality.map e).hom.continuous)
    (hB.preimage (CylinderPrismNaturality.map e).hom.continuous)
    (by rw [← Set.preimage_union, hc, Set.preimage_univ]) d
    (cochainPullback (CylinderPrismNaturality.map e) (d + 1) φ)
    (pullback_support (CylinderPrismNaturality.map e) _ A (fun _ hz => hz) (d + 1) φ hs)
    (pullback_closed (CylinderPrismNaturality.map e) (d + 1) φ hφ)
    (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff)
    ((CylinderPrismNaturality.map e) ⁻¹' C) ((CylinderPrismNaturality.map e) ⁻¹' C)
    (pullback_support (CylinderPrismNaturality.map e) _ C (fun _ hz => hz) (d + 1) φ hC)
    (pullback_support (CylinderPrismNaturality.map e) _ C (fun _ hz => hz) (d + 1) φ hC)
    (fun x => h₀ (e x)) (fun x => h₁ (e x))

def targetOperation := SupportedThomTime.operation (TopCat.of (ClosedInterval × Y)) A B hA hB hc d φ hs hφ
  (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)
  ((AnnularTimeTrim.cylinder Y).toSSet.chainComplexMap coeff) C C hC hC h₀ h₁

theorem homology_naturality (q : ℕ) :
    (sourceOperation e A B hA hB hc d φ hs hφ C hC h₀ h₁).homology q ≫
      HomologicalComplex.homologyMap (push (nearMap e B)) q =
    HomologicalComplex.homologyMap (push e) (d + q) ≫
      (targetOperation A B hA hB hc d φ hs hφ C hC h₀ h₁).homology q := by
  let f := CylinderPrismNaturality.map e
  let Z := TopCat.of (ClosedInterval × X)
  let W := TopCat.of (ClosedInterval × Y)
  let A' := f ⁻¹' A
  let B' := f ⁻¹' B
  let U := SupportedCap.cover Z A' B'
  let V := SupportedCap.cover W A B
  let hA' := hA.preimage f.hom.continuous
  let hB' := hB.preimage f.hom.continuous
  have hc' : A' ∪ B' = Set.univ := by dsimp [A', B']; rw [← Set.preimage_union, hc, Set.preimage_univ]
  let hU := SupportedCap.cover_open Z A' B' hA' hB'
  let hcU := SupportedCap.cover_univ Z A' B' hc'
  let hV := SupportedCap.cover_open W A B hA hB
  let hcV := SupportedCap.cover_univ W A B hc
  let ξ := cochainPullback f (d + 1) φ
  let hs' := pullback_support f A' A (fun _ hz => hz) (d + 1) φ hs
  let hξ := pullback_closed f (d + 1) φ hφ
  let c := SupportedThomTimeRefinement.localized Z A' B' (d + 1) ξ hs' hξ
  let v := SupportedThomTimeRefinement.localized W A B (d + 1) φ hs hφ
  let R := smallSingularRetraction (X := Z) coeff U hU hcU
  let S := smallSingularRetraction (X := W) coeff V hV hcV
  let a := sourceOperation e A B hA hB hc d φ hs hφ C hC h₀ h₁
  let t := targetOperation A B hA hB hc d φ hs hφ C hC h₀ h₁
  have ha (j : ℕ) : a.component j = AnnularTimeTrim.prism X (d + j) ≫
      R.f (d + j + 1) ≫ DegreeLoweringSuccAlignment.align d c rfl j := by
    dsimp only [a, sourceOperation]
    rw [SupportedThomTime.component]
    change AnnularTimeTrim.prism X (d + j) ≫
      (eqToHom (congrArg (chains Z).X (show d + j + 1 = (d + 1) + j by omega)) ≫
        R.f ((d + 1) + j) ≫ c.component j) = _
    exact congrArg (fun g => AnnularTimeTrim.prism X (d + j) ≫ g)
      (RegradedTimeCoverComparison.normal R d (d + 1) rfl c j)
  have ht (j : ℕ) : t.component j = AnnularTimeTrim.prism Y (d + j) ≫
      S.f (d + j + 1) ≫ DegreeLoweringSuccAlignment.align d v rfl j := by
    dsimp only [t, targetOperation]
    rw [SupportedThomTime.component]
    change AnnularTimeTrim.prism Y (d + j) ≫
      (eqToHom (congrArg (chains W).X (show d + j + 1 = (d + 1) + j by omega)) ≫
        S.f ((d + 1) + j) ≫ v.component j) = _
    exact congrArg (fun g => AnnularTimeTrim.prism Y (d + j) ≫ g)
      (RegradedTimeCoverComparison.normal S d (d + 1) rfl v j)
  have hz (j : ℕ) : (t.pre (push e)).component j = AnnularTimeTrim.prism X (d + j) ≫
      (push f ≫ S).f (d + j + 1) ≫ DegreeLoweringSuccAlignment.align d v rfl j := by
    change (push e).f (d + j) ≫ t.component j = _
    rw [ht]
    rw [← Category.assoc ((push e).f (d + j)) (AnnularTimeTrim.prism Y (d + j)), CylinderPrismNaturality.prism]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rfl
  have hcap (j : ℕ) : (CylinderCommonCover.toSource U V f).f ((d + 1) + j) ≫
      c.component j ≫ (push (nearMap e B)).f j =
      (CylinderCommonCover.toTarget U V f).f ((d + 1) + j) ≫ v.component j :=
    CommonCoverLocalizedCapNaturality.component f A' B' A B (fun _ hz => hz) (fun _ hz => hz) (d + 1) j φ hs
  have h := RegradedMappedCapTimeComparison.homology_eq X W U V hU hcU hV hcV f
    _ _ (push (nearMap e B)) d (d + 1) rfl c v (f ⁻¹' C) ξ
    (pullback_support f _ C (fun _ hz => hz) (d + 1) φ hC)
    (push (SupportedCap.subspaceMap Z B')) (fun j => SupportedCap.subspacePush_mono Z B' j)
    (fun j => SupportedThomTimeRefinement.source Z A' B' (d + 1) j ξ hs' hξ)
    (fun x => h₀ (e x)) (fun x => h₁ (e x)) hcap a ha (t.pre (push e)) hz q
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.pre_homology] at h
  exact h

end
end Finsler.CylinderSupportedThomNaturality
