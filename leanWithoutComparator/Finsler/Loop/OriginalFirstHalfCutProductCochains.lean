module

public import Finsler.Loop.OriginalFirstHalfCutOutputJoinData
public import Finsler.Loop.OriginalFirstHalfGammaCaps
public import Finsler.Loop.SmallCapSubspaceLift

/-! Actual closed Thom/tested gamma and normalized retained-output
join cochains on the full original proper cut x Q domain. Their
pullbacks are literal restrictions of the original cylinder cochains. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutProductCochains

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut
open Finsler.OriginalFirstHalfCutOutputJoinData Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ)

abbrev space : TopCat.{0} := TopCat.of (CompactRotatedCutData.source α r × Q)

def cutDomain : Set (ambient α β) := {z | distance (m + 1) (z.1, α z.2.1) ≤ r}

def cutHomeo : space α r (Q := Q) ≃ₜ cutDomain α β r where
  toFun z := ⟨(z.1.val.1, (z.1.val.2, z.2)), z.1.property⟩
  invFun z := (⟨(z.val.1, z.val.2.1), z.property⟩, z.val.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def cutIso : space α r (Q := Q) ≅ TopCat.of (cutDomain α β r) := TopCat.isoOfHomeo (cutHomeo α β r)

theorem source_eq : SmallCapSubspaceLift.source (ambient α β) (space α r (Q := Q))
    (cutDomain α β r) (cutIso α β r) = originalTime α r (Q := Q) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def projection : space α r (Q := Q) ⟶ TopCat.of (CompactRotatedCutData.source α r) :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

theorem first_input_square : originalTime α r (Q := Q) ≫ firstInput α β =
    projection α r (Q := Q) ≫ SupportedCap.subspaceMap (TopCat.of (ClosedInterval × P))
      (CompactRotatedCutData.source α r) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def thom : singularCochainGroup (ZMod 2) (space α r (Q := Q)) (m + 1) :=
  cochainPullback (projection α r (Q := Q) ≫ FirstInputRotationOriginalFactors.originalEvaluation α r) (m + 1)
    (AnnularSelfCut.cocycle (m + 1) (by omega) h)

def tested : singularCochainGroup (ZMod 2) (space α r (Q := Q)) p :=
  cochainPullback (projection α r (Q := Q) ≫ FirstInputRotationOriginalFactors.originalTester α r hr) p T

def gamma : singularCochainGroup (ZMod 2) (space α r (Q := Q)) ((m + 1) + p) :=
  cochainCup (m + 1) p (thom α r h (Q := Q)) (tested α r hr p T (Q := Q))

theorem source_thom : cochainPullback (originalTime α r (Q := Q)) (m + 1)
    (OriginalFirstHalfGammaCaps.thom α β h) = thom α r h (Q := Q) := by
  rw [OriginalFirstHalfGammaCaps.thom, ← pullback_comp, first_input_square, pullback_comp,
    FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle,
    ← pullback_comp, ← pullback_comp]
  rfl

theorem source_tested : cochainPullback (originalTime α r (Q := Q)) p
    (OriginalFirstHalfGammaCaps.tested α β r hr p T) = tested α r hr p T (Q := Q) := by
  rw [OriginalFirstHalfGammaCaps.tested, ← pullback_comp, first_input_square, pullback_comp,
    FirstInputRotationZeroTimeFactors.originalTested, TubeCochainExtension.restriction, ← pullback_comp]
  rfl

theorem source_gamma : cochainPullback (originalTime α r (Q := Q)) ((m + 1) + p)
    (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T) = gamma α r hr h p T (Q := Q) := by
  rw [OriginalFirstHalfGammaCaps.gamma_cup, cochainCup_naturality, source_thom, source_tested]
  rfl

theorem gamma_closed (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    cochainCoboundary (ZMod 2) (space α r (Q := Q)) ((m + 1) + p) (gamma α r hr h p T (Q := Q)) = 0 :=
  cochainCupZMod2_respects_cocycles (m + 1) p _ _
    (pullback_closed _ _ _ (AnnularSelfCut.cocycle_closed (m + 1) (by omega) h)) (pullback_closed _ p T hT)

theorem source_join {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (originalTime α r (Q := Q)) (m + 1) (join α β hκ) =
      CompactJoinCocycle.cocycle (kept α r hr) β (by omega) hκ := by
  rw [OriginalFirstHalfCutOutputJoinData.normalized_join_pullback, join, ← pullback_comp]
  rfl

end
end Finsler.OriginalFirstHalfCutProductCochains
