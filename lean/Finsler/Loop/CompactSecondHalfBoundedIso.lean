module

public import Finsler.Loop.CompactSecondHalfCutIso
public import Finsler.Topology.OriginalSecondHalfExtensions

/-! The native second-half cut and the original partial cut have the
same actual retained-length subspace. Construct the bounded isomorphism,
its source/output diagrams and the literal Thom/tested pullbacks there.
The target length bound is unchanged; no global extension closure or
homology inclusion injectivity is used. -/

@[expose] public section
namespace Finsler.CompactSecondHalfBoundedIso

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.CompactSecondHalfCutIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ)

def nativeRetained : TopCat.of (nativeDomain α β R hR r) ⟶ TopCat.of (SphereLoop n) :=
  nativeCut α β R hR r ≫ TopCat.ofHom (SupportedSelfCut.retained n hr)

def nativeBounded : Set (nativeDomain α β R hR r) :=
  nativeRetained α β R hR r hr ⁻¹' {γ | SobolevLength.length F γ < B}

def toOld : TopCat.of (nativeBounded α β R hR r hr F B) ⟶
    TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B) :=
  TopCat.ofHom ⟨fun z => ⟨CompactSecondHalfCutIso.toOld α β R hR r z.val, z.property⟩,
    ((CompactSecondHalfCutIso.toOld α β R hR r).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def toNative :
    TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B) ⟶
    TopCat.of (nativeBounded α β R hR r hr F B) :=
  TopCat.ofHom ⟨fun z => ⟨CompactSecondHalfCutIso.toNative α β R hR r z.val, z.property⟩,
    ((CompactSecondHalfCutIso.toNative α β R hR r).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem toOld_toNative : toOld α β R hR r hr F B ≫ toNative α β R hR r hr F B = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem toNative_toOld : toNative α β R hR r hr F B ≫ toOld α β R hR r hr F B = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def boundedIso : TopCat.of (nativeBounded α β R hR r hr F B) ≅
    TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B) where
  hom := toOld α β R hR r hr F B
  inv := toNative α β R hR r hr F B
  hom_inv_id := toOld_toNative α β R hR r hr F B
  inv_hom_id := toNative_toOld α β R hR r hr F B

def nativeSource : TopCat.of (nativeBounded α β R hR r hr F B) ⟶
    TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) :=
  SupportedCap.subspaceMap (TopCat.of (nativeDomain α β R hR r)) (nativeBounded α β R hR r hr F B) ≫
    SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (nativeDomain α β R hR r)

def nativeOutput : TopCat.of (nativeBounded α β R hR r hr F B) ⟶
    TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop n)) :=
  restriction (nativeRetained α β R hR r hr) (nativeBounded α β R hR r hr F B)
    {γ | SobolevLength.length F γ < B} (fun _ hz => hz)

def nativeEvaluation : TopCat.of (nativeBounded α β R hR r hr F B) ⟶ DiagonalCohomology.product n :=
  SupportedCap.subspaceMap (TopCat.of (nativeDomain α β R hR r)) (nativeBounded α β R hR r hr F B) ≫
    nativeCut α β R hR r ≫
      SupportedCap.subspaceMap (SelfCutThomCocycle.parameters n) (SupportedSelfCut.neighborhood n r) ≫
        SelfCutThomCocycle.selfEvaluation n

theorem source_square : toOld α β R hR r hr F B ≫
    OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B =
      nativeSource α β R hR r hr F B ≫ CompactNearJoinParameters.timeMap α β R ≫
        SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
          (OriginalSecondHalfCompactTube.tube α β R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem cut_square : toOld α β R hR r hr F B ≫
    OriginalSecondHalfBoundedFactors.domainProjection α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B ≫
        OriginalSecondHalfFamily.cutMap α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR) r =
      SupportedCap.subspaceMap (TopCat.of (nativeDomain α β R hR r)) (nativeBounded α β R hR r hr F B) ≫
        nativeCut α β R hR r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem retained_square : toOld α β R hR r hr F B ≫
    OriginalSecondHalfBoundedFactors.retained α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B = nativeOutput α β R hR r hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem evaluation_square : toOld α β R hR r hr F B ≫
    OriginalSecondHalfBoundedFactors.evaluation α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B = nativeEvaluation α β R hR r hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem thom_pullback (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (toOld α β R hR r hr F B ≫
      OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B) n
      (SupportedSelfCutAdequacy.extension (OriginalSecondHalfCompactTube.tube α β R)
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR)) PUnit.unit n (AnnularSelfCut.cocycle n hn h)) =
      cochainPullback (nativeEvaluation α β R hR r hr F B) n (AnnularThomCocycle.ambient n hn h) := by
  rw [pullback_comp, OriginalSecondHalfExtensions.thom_extension_pullback,
    ← pullback_comp, evaluation_square]

theorem tested_pullback (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (toOld α β R hR r hr F B ≫
      OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B) p
      (SelfCutParameterFamily.testedExtension (OriginalSecondHalfCompactTube.tube α β R)
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
          (OriginalSecondHalfCompactTube.near α β R hR))
        (fun _ => r) (fun _ => hr) PUnit.unit p T) =
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (nativeDomain α β R hR r))
        (nativeBounded α β R hR r hr F B) ≫ nativeCut α β R hR r) p
          (NormalizedSelfCut.testedCocycle n p hr T) := by
  rw [pullback_comp, OriginalSecondHalfExtensions.tested_extension_pullback,
    ← pullback_comp, cut_square]

end
end Finsler.CompactSecondHalfBoundedIso
