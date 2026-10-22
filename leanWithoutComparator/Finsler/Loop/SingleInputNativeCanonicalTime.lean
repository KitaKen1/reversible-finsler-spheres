module

public import Finsler.Loop.SingleInputBoundedAnnularSource
public import Finsler.Loop.RegradedMappedCapTimeComparison
public import Finsler.Loop.CapSourceDegreeTransport
public import Finsler.Loop.SingleCutCanonicalAnyRadius

/-! An actual independently presented native full time with the real
annular cap source is the actual canonical D_T in the SAME short output.
Only real common-cover chain equalities are used before time descent. -/

@[expose] public section
namespace Finsler.SingleInputNativeCanonicalTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)
  (hρr : ρ < r) (hm : 1 ≤ m)


include hσ hradius hsmall hfirst hm in
theorem homology_eq (Z : TopCat.{0}) {ι : Type*} (V : ι → Set Z)
    (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)
    (f : ambient α ⟶ Z) (g : Z ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hfg : f ≫ g = AnnularSelfCut.familyMap α)
    (v : DegreeLoweringHomology.Map (small Z V) (chains (TopCat.of (SelfCutOscillation.short F (a - L + 3 * ε)))) ((m + 1) + p))
    (hv : ∀ q, v.component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε)))).f q =
      (inclusion Z V).f (((m + 1) + p) + q) ≫ (push g).f (((m + 1) + p) + q) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show ((m + 1) + p) + q = (m + p) + q + 1 by omega)) ≫ AnnularCutComparison.cut m p h hρr hr.le T hT q)
    (z : DegreeLoweringHomology.Map (chains (TopCat.of P)) (chains (TopCat.of (SelfCutOscillation.short F (a - L + 3 * ε)))) (m + p))
    (hz : ∀ q, z.component q = AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      (push f ≫ TauCeti.smallSingularRetraction (X := Z) coeff V hV hcV).f ((m + p) + q + 1) ≫
        DegreeLoweringSuccAlignment.align (m + p) v (by omega) q) (q : ℕ) :
    z.homology q = ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
      (push (CompactInputShortMaps.family α F a hA))).homology q := by
  let U := OriginalFirstHalfFactorwiseCover.first (P := P) σ
  let E := small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)
  let c := FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall
    firstIndex hfirst hshortT hA false
  let j := SingleInputBoundedAnnularSource.retainedChain α r hr κ F ε a L
  let w := FirstInputSelfCutBoundedTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA false
  let out := push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε)))
  have hs (t : ℕ) : c.component t ≫ j.f t ≫ out.f t =
      (inclusion (ambient α) U).f (((m + 1) + p) + t) ≫
      (push (AnnularSelfCut.familyMap α)).f (((m + 1) + p) + t) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show ((m + 1) + p) + t = (m + p) + t + 1 by omega)) ≫
      AnnularCutComparison.cut m p h hρr hr.le T hT t := by
    apply CapSourceDegreeTransport.rebase
      (inclusion (ambient α) U ≫ push (AnnularSelfCut.familyMap α))
      ((m + 1) + (p + t)) (((m + 1) + p) + t) ((m + p) + t + 1) (by omega) (by omega) (by omega)
      (c.component t ≫ j.f t ≫ out.f t) (AnnularCutComparison.cut m p h hρr hr.le T hT t)
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      SingleInputBoundedAnnularSource.annular_component α r hr κ h p T hT F ε a L σ hε hradius hsmall
        firstIndex hfirst hshortT hA hρr t
  have hcap (t : ℕ) :
      (CylinderCommonCover.toSource (X := ambient α) (Y := Z) U V f).f (((m + 1) + p) + t) ≫ c.component t ≫ j.f t =
      (CylinderCommonCover.toTarget (X := ambient α) (Y := Z) U V f).f (((m + 1) + p) + t) ≫ v.component t := by
    have : Mono (out.f t) := SupportedCap.subspacePush_mono _ _ t
    apply (cancel_mono (out.f t)).mp
    simp only [Category.assoc]
    rw [hs, hv]
    have hMs := congrArg (fun k => k.f (((m + 1) + p) + t))
      (CylinderCommonCover.toSource_inclusion (X := ambient α) (Y := Z) U V f)
    have hMt := congrArg (fun k => k.f (((m + 1) + p) + t))
      (CylinderCommonCover.toTarget_inclusion (X := ambient α) (Y := Z) U V f)
    simp only [HomologicalComplex.comp_f] at hMs hMt
    simp only [← Category.assoc]
    rw [hMs, hMt]
    simp only [Category.assoc, ← push_comp, ← HomologicalComplex.comp_f, hfg]
  have hw (t : ℕ) : w.component t = AnnularTimeTrim.prism (TopCat.of P) ((m + p) + t) ≫
      (TauCeti.smallSingularRetraction (X := ambient α) coeff U
        (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f ((m + p) + t + 1) ≫
      DegreeLoweringSuccAlignment.align (m + p) c (by omega) t := by
    rw [FirstInputSelfCutBoundedTime.component_normal]
    exact congrArg (fun k => AnnularTimeTrim.prism (TopCat.of P) ((m + p) + t) ≫ k)
      (RegradedTimeCoverComparison.normal
        (TauCeti.smallSingularRetraction (X := ambient α) coeff U
          (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ))
        (m + p) ((m + 1) + p) (by omega) c t)
  have he := RegradedMappedCapTimeComparison.homology_eq (TopCat.of P) Z U V
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ) hV hcV
    f E _ j (m + p) ((m + 1) + p) (by omega) c v (inner α δ)
    (FirstInputSelfCutTime.cochain α r hr h p T false) (FirstInputSelfCutTime.inner_zero α r hr h p T false)
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedOperations.operation_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA false)
    (fun x => show SupportedSelfCut.distance (m + 1) (0, α x) ≤ δ from (UniformSelfCutCollar.distance_zero α x).le.trans h.1.le)
    (fun x => show SupportedSelfCut.distance (m + 1) (1, α x) ≤ δ from (UniformSelfCutCollar.distance_one α x).le.trans h.1.le)
    hcap w hw z hz q
  exact he.symm.trans (SingleCutCanonicalAnyRadius.retained_canonical_DT α r hr κ h p T hT F ε a L σ hσ hε hradius
    hsmall firstIndex hfirst hshortT hA hρr hm false q)

end
end Finsler.SingleInputNativeCanonicalTime
