module

public import Finsler.Loop.FirstInputRotationSupportedAdequacy
public import Finsler.Loop.FirstInputRotationFilteredCap
public import Finsler.Topology.SequentialCapWitness

/-! Uniform actual bounded cap lifts for every cochain restricting to
zero on the short-tester domain. The source scale precedes all cochains
and degrees, including the whole cup-one primitive and its coboundary. -/

@[expose] public section
namespace Finsler.FirstInputRotationSupportedCap

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
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric n) (B η : ℝ) (d : ℕ)
  (ξ : singularCochainGroup (ZMod 2) (space α β R r) d)

def Adequate : Prop :=
  ∀ q (σ : ((space α β R r).smallSingularSubcomplex (rectangle α β R r η) : SSet) _⦋d + q⦌),
    (TopCat.toSSet.obj (space α β R r)).ιChainComplex σ.val ≫
      absoluteChain (space α β R r) d q (d + q) rfl ξ ≠ 0 →
      ∀ z ∈ Set.range ((space α β R r).toSSetObjEquiv _ σ.val),
        z ∈ domain α β R r hR hr F B

def component (good : Adequate α β R r hR hr F B η d ξ) (q : ℕ) :
    (small (space α β R r) (rectangle α β R r η)).X (d + q) ⟶
      (chains (TopCat.of (domain α β R r hR hr F B))).X q :=
  CapOutputSupport.component (rectangle α β R r η) (𝟙 (space α β R r))
    (domain α β R r hR hr F B) d ξ good q

theorem component_source (good : Adequate α β R r hR hr F B η d ξ) (q : ℕ) :
    component α β R r hR hr F B η d ξ good q ≫ (push (source α β R r hR hr F B)).f q =
      (inclusion (space α β R r) (rectangle α β R r η)).f (d + q) ≫
        absoluteChain (space α β R r) d q (d + q) rfl ξ := by
  have he := CapOutputSupport.component_inclusion (rectangle α β R r η) (𝟙 (space α β R r))
    (domain α β R r hR hr F B) d ξ good q
  have hid : push (𝟙 (space α β R r)) = 𝟙 (chains (space α β R r)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (space α β R r))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.id_f] at he
  exact he.trans (congrArg
    (fun g => (inclusion (space α β R r) (rectangle α β R r η)).f (d + q) ≫ g)
    (Category.comp_id (absoluteChain (space α β R r) d q (d + q) rfl ξ)))

theorem exists_uniform [CompactSpace P] [CompactSpace Q] {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ κ > 0, κ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < κ →
      ∃ η > 0, η ≤ b ∧ ∀ (d : ℕ) (L A : ℝ)
        (ξ : singularCochainGroup (ZMod 2) (space α β R r) d),
        cochainPullback (SupportedCap.subspaceMap (space α β R r)
          {z | SobolevLength.length F (testedMap α β R r hR hr z) < L}) d ξ = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        Adequate α β R r hR hr F (A - L + 5 * ε) η d ξ := by
  obtain ⟨κ, hκ, hκ1, hscale⟩ :=
    FirstInputRotationSupportedAdequacy.exists_uniform_scale α β r hr F hε hb hradius
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro R hR hRκ
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRκ
  refine ⟨η, hη, hηb, ?_⟩
  intro d L A ξ hξ hA q σ hc
  obtain ⟨center, hcenter⟩ := (TopCat.mem_smallSingularSubcomplex_iff (space α β R r)
    (rectangle α β R r η) σ.val).mp σ.property
  have hface := SequentialCapWitness.cap_nonzero_front (space α β R r) d q ξ σ.val hc
  have hrange := SequentialCapWitness.simplex_map_range (space α β R r)
    (SimplexCategory.subinterval 0 d (by omega)) σ.val
  exact had center.1 center.2 (Set.range ((space α β R r).toSSetObjEquiv _ σ.val)) hcenter
    d L A ξ hξ (fun z _ => hA z.2.val.2) (SequentialCapWitness.front (space α β R r) d q σ.val)
      hrange hface

end
end Finsler.FirstInputRotationSupportedCap
