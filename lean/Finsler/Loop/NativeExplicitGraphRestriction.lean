module

public import Finsler.Loop.NativeExplicitGraphCap
public import Finsler.Topology.SupportedCapRepresentative

/-! Exact restriction of the explicit global graph data to the actual
ball product. The ORIGINAL native self-evaluation and graph evaluation
agree, so the actual Thom cochains, covers and remaining/evaluation
cocycles agree. Nothing is assigned by a slice multiplicity convention. -/
@[expose] public section
namespace Finsler.NativeExplicitGraphRestriction
open CategoryTheory CartesianMonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem distance_eq {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : LocalNativeBallCut.space P v₀) :
    SupportedSelfCut.distance n (LocalNativeBallCut.cutParameters P v₀ b z) =
      NormalizedSphereGraphCap.distance n (NativeExplicitGraphCap.tail P) (NativeExplicitGraphCap.second P)
        (LocalNativeBallCut.toGraph P v₀ z) := by
  have he := LocalNativeBallCut.self_evaluation P v₀ b z
  have hl := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  change H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z).2 = z.1.val at hl
  change H1SelfCutNeighborhood.endpoint (LocalNativeBallCut.cutParameters P v₀ b z) = z.2.1.val at hr
  change ‖(H1SelfCutNeighborhood.endpoint (LocalNativeBallCut.cutParameters P v₀ b z) : Ambient n) -
    (H1FiberBase.point (LocalNativeBallCut.cutParameters P v₀ b z).2 : Ambient n)‖ = ‖(z.2.1.val : Ambient n) - z.1.val‖
  rw [hl, hr]

theorem maps_exterior {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (ρ : ℝ) :
    Set.MapsTo (LocalNativeBallCut.toGraph P v₀) (LocalNativeSupportedCap.exterior P v₀ b ρ)
      (NativeExplicitGraphCap.exterior P ρ) := by
  intro z hz
  change ρ < NormalizedSphereGraphCap.distance n _ _ _
  rw [← distance_eq P v₀ b z]
  exact hz

theorem maps_near {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (r : ℝ) :
    Set.MapsTo (LocalNativeBallCut.toGraph P v₀) (LocalNativeBallCut.near P v₀ b r) (NativeExplicitGraphCap.near P r) := by
  intro z hz
  change NormalizedSphereGraphCap.distance n _ _ _ < r
  rw [← distance_eq P v₀ b z]
  exact hz

theorem evaluation_square {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    LocalNativeBallCut.toGraph P v₀ ≫ NormalizedSphereGraphCap.evaluation n (NativeExplicitGraphCap.tail P)
      (NativeExplicitGraphCap.second P) =
      LocalNativeBallCut.cutParameters P v₀ b ≫ SelfCutThomCocycle.selfEvaluation n := by
  apply TopCat.ext
  intro z
  exact (LocalNativeBallCut.self_evaluation P v₀ b z).symm

theorem cocycle_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (LocalNativeBallCut.toGraph P v₀) (m + 1)
      (NormalizedSphereGraphCap.cocycle (m + 1) (by omega) (NativeExplicitGraphCap.tail P)
        (NativeExplicitGraphCap.second P) hρ) = LocalNativeSupportedCap.cocycle (m + 1) (by omega) P v₀ b hρ := by
  rw [NormalizedSphereGraphCap.cocycle, ← pullback_comp, evaluation_square, pullback_comp]
  rfl

theorem remaining_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    LocalNativeBallCut.toGraph P v₀ ≫ NativeExplicitGraphCap.remaining P =
      SmallBallProductReduction.remaining (LocalNativeBallCut.center P v₀) (TopCat.of (equator P)) := by
  apply TopCat.ext
  intro z
  rfl

theorem first_square {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    LocalNativeBallCut.toGraph P v₀ ≫ NativeExplicitGraphCap.first P = LocalNativeBallCupCorrection.firstPoint P v₀ := by
  apply TopCat.ext
  intro z
  rfl

theorem remaining_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) :
    cochainPullback (LocalNativeBallCut.toGraph P v₀) m (NativeExplicitGraphCap.remainingCocycle m P v₀) =
      LocalNativeBallPrimitive.remainingCocycle m P v₀ := by
  rw [NativeExplicitGraphCap.remainingCocycle, ← pullback_comp, remaining_square]
  rfl

theorem first_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cochainPullback (LocalNativeBallCut.toGraph P v₀) (m + 1) (NativeExplicitGraphCap.evaluationCocycle m P v₀ hη) =
      LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη := by
  rw [NativeExplicitGraphCap.evaluationCocycle, ← pullback_comp, first_square]
  rfl

theorem split_pullback (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {η : ℝ} (hη : 0 < η) :
    cochainPullback (LocalNativeBallCut.toGraph P v₀) (m + (m + 1)) (NativeExplicitGraphCap.split m P v₀ hη) =
      cochainCup m (m + 1) (LocalNativeBallPrimitive.reducedCocycle m P v₀ 1)
        (LocalNativeBallCupCorrection.evaluationCocycle m P v₀ hη) := by
  rw [NativeExplicitGraphCap.split, cochainCup_naturality, remaining_pullback, first_pullback]
  rfl

end
end Finsler.NativeExplicitGraphRestriction
