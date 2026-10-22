module

public import Finsler.Loop.GlobalTimeCupCohomology
public import Finsler.Loop.CylinderPrismNaturality
public import Finsler.Loop.FilteredGlobalThomTime

/-! The ACTUAL geometric time-cup cochain vanishes literally on
constant loops, in every input/output degree. Its time cylinder stays
on the actual diagonal, where the normalized Thom cochain is zero;
the genuine small-chain cap preserves that carrier. -/

@[expose] public section
namespace Finsler.GlobalTimeCupConstantsVanish
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev inclusion (n : ℕ) := SupportedCap.subspaceMap (Loops n) (consts n)

theorem cylinder_diagonal (n : ℕ) (z : ClosedInterval × (consts n)) :
    CylinderPrismNaturality.map (inclusion n) z ∈ FilteredGlobalThomTime.endpointCarrier n := by
  change BorelEvaluation.eval n z.2.val = sphereRepresentative z.2.val z.1
  obtain ⟨P, hP⟩ := z.2.property
  rw [← hP, BorelEvaluation.eval_constant, sphereRepresentative_constantSphereLoop]

theorem thom_zero (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ) :
    (push (CylinderPrismNaturality.map (inclusion (m + 1)))).f ((m + 1) + q) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component q = 0 :=
  SelfCutEndpoints.cut_map_zero (exterior (m + 1) ρ) (neighborhood (m + 1) r)
    (FilteredGlobalThomTime.endpointCarrier (m + 1))
    (exterior_open (m + 1) ρ) (neighborhood_open (m + 1) r) (cover (m + 1) hρr)
    (m + 1) q (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (FilteredGlobalThomTime.cocycle_endpoint m hρ)
    (CylinderPrismNaturality.map (inclusion (m + 1))) (cylinder_diagonal (m + 1))

theorem time_zero (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ) :
    (push (inclusion (m + 1))).f (m + q) ≫
      (GlobalThomTime.operation m hρ hρr).component q = 0 := by
  change (push (inclusion (m + 1))).f (m + q) ≫
    (AnnularTimeTrim.prism (Loops (m + 1)) (m + q) ≫ GlobalThomTime.aligned m hρ hρr q) = 0
  rw [← Category.assoc, CylinderPrismNaturality.prism, Category.assoc]
  have hz := DegreeLoweringSuccAlignment.pre_zero m
    (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr) rfl
    (push (CylinderPrismNaturality.map (inclusion (m + 1)))) q (thom_zero m hρ hρr q)
  change _ ≫ ((push (CylinderPrismNaturality.map (inclusion (m + 1)))).f (m + q + 1) ≫
    GlobalThomTime.aligned m hρ hρr q) = 0
  change (push (CylinderPrismNaturality.map (inclusion (m + 1)))).f (m + q + 1) ≫
    GlobalThomTime.aligned m hρ hρr q = 0 at hz
  exact (congrArg (fun k => AnnularTimeTrim.prism (TopCat.of (consts (m + 1))) (m + q) ≫ k) hz).trans comp_zero

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h φ) =
      CochainDegreeTransport.pre X h (cochainPullback f j φ) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem cochain_zero (m p : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p) (q : ℕ)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q) :
    cochainPullback (inclusion (m + 1)) ((m + p) + q)
      (GeometricTimeCupCochain.cochain m p hρ hρr hr T q B) = 0 := by
  rw [← GlobalTimeCupCohomology.cochain_compare m hρ hρr hr p q T B, pullback_pre]
  have hz : cochainPullback (inclusion (m + 1)) (m + (p + q))
      (DegreeLoweringCochainPullback.cochain (GlobalThomTime.operation m hρ hρr) (p + q)
        (GeometricTimeCupCochain.splitCup m p hr T q B)) = 0 := by
    change (push (inclusion (m + 1))).f (m + (p + q)) ≫
      ((GlobalThomTime.operation m hρ hρr).component (p + q) ≫ _) = 0
    rw [← Category.assoc, time_zero, zero_comp]
  rw [hz]
  simp only [CochainDegreeTransport.pre, comp_zero]

theorem product_restriction_zero (m p q : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    (cohPullback (inclusion (m + 1)) ((m + p) + q)).hom
      (GlobalTimeCupCohomology.product m hρ hρr hr p q a b) = 0 := by
  obtain ⟨T, hT, rfl⟩ := cocycleClass_surjective _ p a
  obtain ⟨B, hB, rfl⟩ := cocycleClass_surjective _ q b
  rw [GlobalTimeCupCohomology.product_cocycle, cohPullback_cocycleClass]
  have hz := cochain_zero m p hρ hρr hr T q B
  have hzero : cochainCoboundary (ZMod 2) (TopCat.of (consts (m + 1))) ((m + p) + q) 0 = 0 := by
    simp [cochainCoboundary]
  exact (cocycleClass_congr _ _ hz _ hzero).trans (cocycleClass_zero _ _ hzero)

end
end Finsler.GlobalTimeCupConstantsVanish
