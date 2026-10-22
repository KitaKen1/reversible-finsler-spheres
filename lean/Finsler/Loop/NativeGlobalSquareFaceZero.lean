module

public import Finsler.Loop.NativeGlobalTimeSquare
public import Finsler.Loop.GlobalCutTimePrismAlignment
public import Finsler.Topology.SelfCutEndpoints

/-! Literal ORIGINAL pre-time cochain zero on the cut-end face union,
and on the northern-rotation-end face union. These are actual carrier
proofs with the ORIGINAL cap/subdivision; a relative lift on the union
of ALL FOUR faces is deliberately not inferred from separate zeros. -/
@[expose] public section
namespace Finsler.NativeGlobalSquareFaceZero
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def cutEnds (n : ℕ) : Set (SelfCutThomCocycle.parameters n) := {z | z.1 = 0 ∨ z.1 = 1}

theorem thom_cutEnds_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters n) (cutEnds n)) n
      (NormalizedSelfCut.cocycle n hn hρ) = 0 := by
  rw [NormalizedSelfCut.cocycle, ← pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_diagonal hn hρ
  intro z
  change H1FiberBase.point z.val.2 = sphereRepresentative z.val.2 z.val.1
  rcases z.property with h | h
  · rw [h]
    rfl
  · rw [h]
    exact (sphereRepresentative_endpoints z.val.2).symm

theorem parameter_cutEnds_family_zero (m p : ℕ) (Q : Sphere (m + 1)) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1)) (hf : ∀ x, f x ∈ cutEnds (m + 1)) :
    cochainPullback f ((m + 1) + (p + (m + 1))) (LocalizedParameterCutCochain.cochain m p Q hρ hρr hr hη T) = 0 := by
  have hz := SelfCutEndpoints.cut_map_zero (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (cutEnds (m + 1)) (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.cover (m + 1) hρr) (m + 1) (p + (m + 1)) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ) (thom_cutEnds_zero (m + 1) (by omega) hρ) f hf
  change (push f).f _ ≫ ((NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) ≫ _) = 0
  have hz' : (push f).f ((m + 1) + (p + (m + 1))) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + (m + 1)) = 0 := hz
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ GeometricTimeCupCochain.splitCup m p hr T (m + 1)
      (LocalizedCutEvaluationCochain.loopCocycle (m + 1) (by omega) Q hη)) hz').trans zero_comp)

theorem parameter_start_family_zero (m p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, H1FiberBase.point (f x).2 ∈ NorthMeridianEvaluationPoint.excluded P v₀) :
    cochainPullback f ((m + 1) + (p + (m + 1)))
      (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0 := by
  let C := StartPointCarrierTimeCupZero.parameterCarrier (m + 1) (NorthMeridianEvaluationPoint.excluded P v₀)
  let g : X ⟶ TopCat.of C := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) C := by
    apply TopCat.ext
    intro x
    rfl
  have hz := StartPointCarrierTimeCupZero.thom_split_zero m p (NorthMeridianEvaluationPoint.target P v₀)
    hρ hρr hr hη (NorthMeridianEvaluationPoint.excluded P v₀)
    (NorthRotationPrismLocalization.cocycle_excluded_zero m P v₀ hη hη2) T
  change cochainPullback (SupportedCap.subspaceMap (SelfCutThomCocycle.parameters (m + 1)) C) _
    (LocalizedParameterCutCochain.cochain m p (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη T) = 0 at hz
  rw [he, pullback_comp, hz]
  exact map_zero _

def cutFaces {n : ℕ} (P : Sphere n) : Set (NativeGlobalTimeSquare.squareDomain P) := {z | z.1 = 0 ∨ z.1 = 1}
def rotationFaces {n : ℕ} (P : Sphere n) : Set (NativeGlobalTimeSquare.squareDomain P) := {z | z.2.1 = 0 ∨ z.2.1 = 1}

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h φ) =
      CochainDegreeTransport.pre X h (cochainPullback f j φ) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem cut_faces_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (SupportedCap.subspaceMap (NativeGlobalTimeSquare.squareDomain P) (cutFaces P) ≫
      NativeGlobalTimeSquare.intoCut P v₀ k) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) = 0 := by
  have hz := parameter_cutEnds_family_zero m m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))
    (SupportedCap.subspaceMap (NativeGlobalTimeSquare.squareDomain P) (cutFaces P) ≫ NativeGlobalTimeSquare.intoCut P v₀ k)
    (fun x => x.property)
  rw [GlobalCutTimePrismAlignment.parameterCochain, pullback_pre, hz, CochainDegreeTransport.pre, comp_zero]

theorem rotation_faces_zero (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (NativeGlobalTimeSquare.squareDomain P) (rotationFaces P) ≫
      NativeGlobalTimeSquare.intoCut P v₀ k) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) = 0 := by
  let f := SupportedCap.subspaceMap (NativeGlobalTimeSquare.squareDomain P) (rotationFaces P) ≫ NativeGlobalTimeSquare.intoCut P v₀ k
  have hf : ∀ x, H1FiberBase.point (f x).2 ∈ NorthMeridianEvaluationPoint.excluded P v₀ := by
    intro x
    change H1FiberBase.point (NativeFixedReturnRotationZero.quarterFamily P v₀ k 0 (x.val.2.1, x.val.2.2)) ∈ _
    rcases x.property with h | h
    · rw [h]
      exact NorthRotationPrismLocalization.north_start_excluded P v₀ k x.val.2.2
    · rw [h]
      exact NorthRotationPrismLocalization.north_finish_excluded P v₀ k x.val.2.2
  have hz := parameter_start_family_zero m m P v₀ hρ hρr hr hη hη2
    (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) f hf
  rw [GlobalCutTimePrismAlignment.parameterCochain, pullback_pre, hz, CochainDegreeTransport.pre, comp_zero]

end
end Finsler.NativeGlobalSquareFaceZero
