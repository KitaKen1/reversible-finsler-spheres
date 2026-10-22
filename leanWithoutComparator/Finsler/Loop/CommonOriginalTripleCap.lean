module

public import Finsler.Loop.NativeCommonTripleCap
public import Finsler.Loop.FullSecondHalfExtensionDiagrams
public import Finsler.Loop.CompactSecondHalfBoundedIso
public import Finsler.Loop.DegreeLoweringRegrade

/-! Put the actual common-cover bounded native three-stage cap in the
original bounded cut target. Its source is the literal original three
successive caps with genuine proper-tube zero extensions. -/

@[expose] public section
namespace Finsler.CommonOriginalTripleCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.RelativeCapAssociativity Finsler.ThreeCapBlockVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem cap_cast (X : TopCat.{0}) (a q N : ℕ) (h : a + q = N)
    (φ : singularCochainGroup (ZMod 2) X a) :
    eqToHom (congrArg (chains X).X h.symm) ≫ absoluteChain X a q (a + q) rfl φ =
      absoluteChain X a q N h φ := by
  subst N
  simp only [eqToHom_refl, Category.id_comp]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ)

def toOld : TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
    (CompactNearJoinParameters.inputs α β R hR) hr F B) ⟶
    TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B) :=
  CompactSecondHalfBoundedIso.toOld α β R hR r hr F B

theorem source_square : toOld α β R hR r hr F B ≫
    OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B =
      FullSecondHalfNativeLift.nativeSource (CompactNearJoinParameters.inputs α β R hR) hr F B ≫
        JoinTimeCommonRefinement.source α β R := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem retained_square : toOld α β R hR r hr F B ≫
    OriginalSecondHalfBoundedFactors.retained α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B =
      FullSecondHalfNativeTimeOperation.retainedOutput (CompactNearJoinParameters.inputs α β R hR) hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (η σ κ : ℝ) (hn : 1 ≤ n) (hκ : 0 < κ) (p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X (n + (p + q)) ⟶
      (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
        (CompactNearJoinParameters.inputs α β R hR) hr F B))).X q)
  (hc : ∀ q, c (q + 1) ≫ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded
      (CompactNearJoinParameters.inputs α β R hR) hr F B))).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        (n + (p + (q + 1))) (n + (p + q)) ≫ c q)

def operation : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ))
    (chains (TopCat.of (OriginalSecondHalfBoundedFactors.bounded α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR) r hr F B))) (n + n + p) :=
  (DegreeLoweringRegrade.regrade
    (NativeCommonTripleCap.operation α β R η σ κ hn hκ _ p c hc) (n + n + p) (Nat.add_assoc n n p)).post
      (push (toOld α β R hR r hr F B))

theorem component (q : ℕ) : (operation α β R hR r hr F B η σ κ hn hκ p c hc).component q =
    eqToHom (congrArg
      (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ)).X
      (show n + n + p + q = n + (n + (p + q)) by omega)) ≫
        (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component (n + (p + q)) ≫
          c q ≫ (push (toOld α β R hR r hr F B)).f q := by
  dsimp only [operation, DegreeLoweringHomology.Map.post]
  rw [DegreeLoweringRegrade.regrade_component, NativeCommonTripleCap.component]
  simp only [Category.assoc]
  rw [← Category.assoc ((OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component ((n + p) + q))
      (eqToHom (congrArg
        (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
          (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X
        (Nat.add_assoc n p q)))
      (c q ≫ (push (toOld α β R hR r hr F B)).f q),
    DegreeLoweringRegrade.component_transport (OriginalNativeCommonCover.cap α β R η σ κ hn hκ)
      ((n + p) + q) (n + (p + q)) (Nat.add_assoc n p q)]
  simp only [← Category.assoc, eqToHom_trans]

theorem source {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hi : ∀ q, c q ≫ (push (FullSecondHalfNativeLift.nativeSource
      (CompactNearJoinParameters.inputs α β R hR) hr F B)).f q =
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫
          PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) n p q
            (FullSecondHalfNativeTimeOperation.thom (CompactNearJoinParameters.inputs α β R hR) hn h)
            (FullSecondHalfNativeTimeOperation.tested (CompactNearJoinParameters.inputs α β R hR) hr p T)) (q : ℕ) :
    (operation α β R hR r hr F B η σ κ hn hκ p c hc).component q ≫
      (push (OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B)).f q =
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ)).f (n + n + p + q) ≫
        threeCap (TopCat.of (P × (ClosedInterval × Q))) n n p q (CompactJoinCocycle.timeCocycle α β hn hκ)
          (SupportedSelfCutAdequacy.extension (OriginalSecondHalfCompactTube.tube α β R)
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
              (OriginalSecondHalfCompactTube.near α β R hR)) PUnit.unit n (AnnularSelfCut.cocycle n hn h))
          (testedExtension (OriginalSecondHalfCompactTube.tube α β R)
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
              (OriginalSecondHalfCompactTube.near α β R hR)) (fun _ => r) (fun _ => hr) PUnit.unit p T) := by
  let X : TopCat.{0} := TopCat.of (P × (ClosedInterval × Q))
  let Y : TopCat.{0} := TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)
  let U := SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η
  let V := OriginalNativeCommonCover.cover α β R η σ κ
  let j := JoinTimeCommonRefinement.source α β R
  let φ := SupportedSelfCutAdequacy.extension (OriginalSecondHalfCompactTube.tube α β R)
    (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR)) PUnit.unit n (AnnularSelfCut.cocycle n hn h)
  let ψ := testedExtension (OriginalSecondHalfCompactTube.tube α β R)
    (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
      (OriginalSecondHalfCompactTube.near α β R hR)) (fun _ => r) (fun _ => hr) PUnit.unit p T
  have he : c q ≫ (push (toOld α β R hR r hr F B ≫
      OriginalSecondHalfBoundedFactors.source α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR) r hr F B)).f q =
      (inclusion Y U ≫ push j).f (n + (p + q)) ≫ PartialDoubleCap.cap X n p q φ ψ := by
    rw [source_square, push_comp, HomologicalComplex.comp_f, ← Category.assoc, hi q]
    rw [Category.assoc,
      ← FullSecondHalfExtensionDiagrams.thom_pullback α β R hR hn h,
      ← FullSecondHalfExtensionDiagrams.tested_pullback α β R hR hr p T,
      PartialDoubleCap.cap_natural]
    rfl
  rw [component]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f (push (toOld α β R hR r hr F B)), ← push_comp, he]
  rw [← Category.assoc ((OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component (n + (p + q)))
      ((inclusion Y U ≫ push j).f (n + (p + q))) (PartialDoubleCap.cap X n p q φ ψ),
    OriginalNativeCommonCover.cap_source]
  have ht := transport_f (inclusion X V) (n + n + p + q) (n + (n + (p + q))) (by omega)
  have ht' := congrArg
    (fun z : (small X V).X (n + n + p + q) ⟶ (chains X).X (n + (n + (p + q))) =>
      z ≫ absoluteChain X n (n + (p + q)) (n + (n + (p + q))) rfl
        (CompactJoinCocycle.timeCocycle α β hn hκ) ≫ PartialDoubleCap.cap X n p q φ ψ) ht
  calc
    _ = ((inclusion X V).f (n + n + p + q) ≫
        eqToHom (congrArg (chains X).X (show n + n + p + q = n + (n + (p + q)) by omega))) ≫
          absoluteChain X n (n + (p + q)) (n + (n + (p + q))) rfl
            (CompactJoinCocycle.timeCocycle α β hn hκ) ≫ PartialDoubleCap.cap X n p q φ ψ := by
      simpa only [Category.assoc] using ht'
    _ = (inclusion X V).f (n + n + p + q) ≫
        (eqToHom (congrArg (chains X).X (show n + n + p + q = n + (n + (p + q)) by omega)) ≫
          absoluteChain X n (n + (p + q)) (n + (n + (p + q))) rfl
            (CompactJoinCocycle.timeCocycle α β hn hκ)) ≫ PartialDoubleCap.cap X n p q φ ψ := by
      simp only [Category.assoc]
    _ = (inclusion X V).f (n + n + p + q) ≫
        absoluteChain X n (n + (p + q)) (n + n + p + q) (by omega)
          (CompactJoinCocycle.timeCocycle α β hn hκ) ≫ PartialDoubleCap.cap X n p q φ ψ := by
      rw [cap_cast X n (n + (p + q)) (n + n + p + q) (by omega)]
    _ = _ := rfl

end
end Finsler.CommonOriginalTripleCap
