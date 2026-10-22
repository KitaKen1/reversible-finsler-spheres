module

public import Finsler.Loop.OriginalFirstHalfZeroGammaCap
public import Finsler.Loop.CapCupNested
public import Finsler.Loop.NestedCapUnpack
public import Finsler.Topology.CutDomainTimePrism

/-! The genuine original zero-cylinder gamma cap descends through
the entire cut-time interval in its identical bounded proper target. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfZeroGammaTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.SupportedSelfCut Finsler.OriginalFirstHalfZeroCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def thom := cochainPullback (OriginalFirstHalfCupOneCochains.nearSource α β R) (m + 1)
  (OriginalFirstHalfGammaCaps.thom α β h)

def tested := cochainPullback (OriginalFirstHalfCupOneCochains.nearSource α β R) p
  (OriginalFirstHalfGammaCaps.tested α β r hr p T)

def inner : Set (space α β R) :=
  OriginalFirstHalfCupOneCochains.nearSource α β R ⁻¹' OriginalFirstHalfCupOneCochains.inner α β δ

theorem gamma_cup : OriginalFirstHalfZeroGammaCochains.gamma α β R r hr h p T =
    cochainCup (m + 1) p (thom α β R h) (tested α β R r hr p T) := by
  rw [OriginalFirstHalfZeroGammaCochains.gamma, OriginalFirstHalfGammaCaps.gamma_cup, cochainCup_naturality]
  rfl

theorem thom_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (space α β R) (inner α β R (δ := δ))) (m + 1)
      (thom α β R h) = 0 := by
  rw [thom, OriginalFirstHalfGammaCaps.thom, FirstInputRotationZeroTimeFactors.originalThom,
    AnnularSelfCut.familyCocycle,
    ← pullback_comp (OriginalFirstHalfCupOneCochains.firstInput α β) (AnnularSelfCut.familyMap α),
    ← pullback_comp (OriginalFirstHalfCupOneCochains.nearSource α β R)
      (OriginalFirstHalfCupOneCochains.firstInput α β ≫ AnnularSelfCut.familyMap α)]
  apply pullback_support
    (OriginalFirstHalfCupOneCochains.nearSource α β R ≫ OriginalFirstHalfCupOneCochains.firstInput α β ≫
      AnnularSelfCut.familyMap α) (inner α β R (δ := δ))
    {z | distance (m + 1) z ≤ δ} _ (m + 1) (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSelfCut.cocycle_small_zero (m + 1) (by omega) h)
  intro z hz
  exact hz

variable (F : ReversibleMetric (m + 1)) (B η : ℝ) (hη : 0 < η) (hρr : ρ < r)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η ((m + 1) + p)
    (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def component := NestedCapUnpack.component (m + 1) p
  (OriginalFirstHalfZeroGammaCap.operation α β R r hR hr h p T F B η good hT)

theorem component_comm (q : ℕ) :
    component α β R r hR hr h p T F B η good hT (q + 1) ≫
      (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))).d (q + 1) q =
    (small (space α β R) (cover α β R r η ρ)).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫
      component α β R r hR hr h p T F B η good hT q :=
  NestedCapUnpack.comm (m + 1) p _ q

theorem component_source (q : ℕ) :
    component α β R r hR hr h p T F B η good hT q ≫
      (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B)).f q =
    (inclusion (space α β R) (cover α β R r η ρ)).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap (space α β R) (m + 1) p q (thom α β R h) (tested α β R r hr p T) := by
  apply NestedCapUnpack.inclusion (m + 1) p _ _ _ _ q
  intro t
  have hc := OriginalFirstHalfZeroGammaCap.component_source α β R r hR hr h p T F B η good t
  rw [gamma_cup, CapCupNested.flat_nested, ← Category.assoc,
    ← transport_f (inclusion (space α β R) (cover α β R r η ρ))
      (((m + 1) + p) + t) ((m + 1) + (p + t)) (Nat.add_assoc (m + 1) p t), Category.assoc] at hc
  exact hc

def operation : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) (m + p) :=
  CutDomainTimePrism.operation (TopCat.of (CompactNearJoinParameters.tube α β R))
    (cover α β R r η ρ) (cover_open α β R r η ρ) (cover_univ α β R r hη hρr)
    (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) m p
    (component α β R r hR hr h p T F B η good hT)
    (inner α β R (δ := δ)) (thom α β R h) (tested α β R r hr p T) (thom_inner_zero α β R h)
    (push (OriginalFirstHalfZeroSupportedCap.sourceBounded α β R r hR hr F B))
    (OriginalFirstHalfZeroSupportedCap.sourceBounded_mono α β R r hR hr F B)
    (component_source α β R r hR hr h p T F B η good hT)
    (component_comm α β R r hR hr h p T F B η good hT)
    (fun z => show distance (m + 1) (0, α z.val.1) ≤ δ from
      (UniformSelfCutCollar.distance_zero α z.val.1).le.trans h.1.le)
    (fun z => show distance (m + 1) (1, α z.val.1) ≤ δ from
      (UniformSelfCutCollar.distance_one α z.val.1).le.trans h.1.le)

theorem component_normal (q : ℕ) :
    (operation α β R r hR hr h p T F B η hη hρr good hT).component q =
    AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      ClosedCapDegreeTransport.align m p
        (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R))
          (cover α β R r η ρ) (cover_open α β R r η ρ) (cover_univ α β R r hη hρr)
          (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B))) m p
          (component α β R r hR hr h p T F B η good hT)) q := rfl

end
end Finsler.OriginalFirstHalfZeroGammaTime
