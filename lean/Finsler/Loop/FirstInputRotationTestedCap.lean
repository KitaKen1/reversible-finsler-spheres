module

public import Finsler.Loop.FirstInputRotationFilteredCap
public import Finsler.Topology.CapOutputSupport

/-! The actual tested cap alone has the uniform fixed-output bound.
It can follow a Thom cap already localized into the proper small cut
domain, without introducing an ambient tested zero extension. -/

@[expose] public section
namespace Finsler.FirstInputRotationTestedCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationFilteredCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric n) (B η : ℝ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)

def Adequate : Prop :=
  ∀ q (σ : ((space α β R r).smallSingularSubcomplex (rectangle α β R r η) : SSet) _⦋p + q⦌),
    (TopCat.toSSet.obj (space α β R r)).ιChainComplex σ.val ≫
      absoluteChain (space α β R r) p q (p + q) rfl (tested α β R r hR hr p T) ≠ 0 →
      ∀ z ∈ Set.range ((space α β R r).toSSetObjEquiv _ σ.val),
        outputMap α β R r hR hr z ∈ JoinedFilteredCap.sublevel F B

def operation (hgood : Adequate α β R r hR hr F B η p T)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    DegreeLoweringHomology.Map (small (space α β R r) (rectangle α β R r η))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) p :=
  CapOutputSupport.operation (rectangle α β R r η) (outputMap α β R r hR hr)
    (JoinedFilteredCap.sublevel F B) p (tested α β R r hR hr p T) hgood
    (tested_closed α β R r hR hr p T hT)

theorem component_inclusion (hgood : Adequate α β R r hR hr F B η p T)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    (operation α β R r hR hr F B η p T hgood hT).component q ≫
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (space α β R r) (rectangle α β R r η)).f (p + q) ≫
        absoluteChain (space α β R r) p q (p + q) rfl (tested α β R r hR hr p T) ≫
          (push (outputMap α β R r hR hr)).f q :=
  CapOutputSupport.component_inclusion (rectangle α β R r η) (outputMap α β R r hR hr)
    (JoinedFilteredCap.sublevel F B) p (tested α β R r hR hr p T) hgood q

theorem exists_uniform [CompactSpace P] [CompactSpace Q] {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ κ > 0, κ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < κ →
      ∃ η > 0, η ≤ b ∧ ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        Adequate α β R r hR hr F (A - L + 5 * ε) η p T := by
  obtain ⟨κ, hκ, hκ1, hscale⟩ :=
    FirstInputRotationAdequacy.exists_uniform_scale α β r hr F hε hb hradius
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro R hR hRκ
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRκ
  refine ⟨η, hη, hηb, ?_⟩
  intro p L A T hshort hA q σ hc
  let X := space α β R r
  obtain ⟨center, hcenter⟩ := (TopCat.mem_smallSingularSubcomplex_iff X
    (rectangle α β R r η) σ.val).mp σ.property
  have hface := SequentialCapWitness.cap_nonzero_front X p q (tested α β R r hR hr p T) σ.val hc
  have hrange := SequentialCapWitness.simplex_map_range X (SimplexCategory.subinterval 0 p (by omega)) σ.val
  exact had center.1 center.2 (Set.range (X.toSSetObjEquiv _ σ.val)) hcenter
    p L A T hshort (fun z _ => hA z.2.val.2)
    (SequentialCapWitness.front X p q σ.val) hrange hface

end
end Finsler.FirstInputRotationTestedCap
