module

public import Finsler.Loop.EmbeddedCapOutputSupport
public import Finsler.Loop.FirstInputRotationAmbientCap
public import Finsler.Loop.FirstInputRotationSupportedCap

/-! Lift an arbitrary supported ambient cap into the actual bounded
proper cut domain. Far zero forces the whole parent into one genuine
proper rectangle, where the proved proper parent bound applies. -/

@[expose] public section
namespace Finsler.FirstInputRotationAmbientSupportedCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputRotationAmbientCover Finsler.FirstInputRotationCochains
open Finsler.FirstInputRotationFilteredCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric n) (B η ρ : ℝ) (d : ℕ)
  (ξ : singularCochainGroup (ZMod 2) (ambient α β R) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) d ξ = 0)
  (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η d
    (cochainPullback (FirstInputRotationAmbientCover.source α β R r) d ξ))

include hfar in
theorem far_coboundary_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) (d + 1)
      (cochainCoboundary (ZMod 2) (ambient α β R) d ξ) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)).op).comm d (d + 1)) ξ
  change cochainCoboundary (ZMod 2) (TopCat.of (far α β R ρ)) d
    (cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) d ξ) = _ at he
  rw [hfar] at he
  exact he.symm.trans (map_zero _)

include hfar good in
theorem parent_bound (q : ℕ)
    (σ : ((ambient α β R).smallSingularSubcomplex (cover α β R r η ρ) : SSet) _⦋d + q⦌)
    (hc : (TopCat.toSSet.obj (ambient α β R)).ιChainComplex σ.val ≫
      absoluteChain (ambient α β R) d q (d + q) rfl ξ ≠ 0) :
    Set.range ((ambient α β R).toSSetObjEquiv _ σ.val) ⊆
      FirstInputRotationAmbientCover.source α β R r '' domain α β R r hR hr F B := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β R)
    (cover α β R r η ρ) σ.val).mp σ.property
  cases i with
  | none => exact (hc (SupportedCap.cap_zero_on_simplex _ _ d q (d + q) rfl ξ hfar σ.val hi)).elim
  | some i =>
    obtain ⟨τ, hτ, hτrange⟩ := EmbeddedCapOutputSupport.exists_parent (ambient α β R)
      (space α β R r) (proper α β R r) (properIso α β R r)
      (rectangle α β R r η i) (d + q) σ.val (hi.trans (near_image α β R r η ρ i))
    change (TopCat.toSSet.map (FirstInputRotationAmbientCover.source α β R r)).app
      (Opposite.op ⦋d + q⦌) τ = σ.val at hτ
    have hsmall : τ ∈ ((space α β R r).smallSingularSubcomplex (rectangle α β R r η)).obj (Opposite.op ⦋d + q⦌) :=
      (TopCat.mem_smallSingularSubcomplex_iff _ _ τ).mpr ⟨i, hτrange⟩
    have hnz : (TopCat.toSSet.obj (space α β R r)).ιChainComplex τ ≫
        absoluteChain (space α β R r) d q (d + q) rfl
          (cochainPullback (FirstInputRotationAmbientCover.source α β R r) d ξ) ≠ 0 := by
      intro hz
      have hn := CapOutputSupport.cap_push_simplex (FirstInputRotationAmbientCover.source α β R r) d q ξ τ
      rw [hτ, hz, zero_comp] at hn
      exact hc hn.symm
    have hb := good q ⟨τ, hsmall⟩ hnz
    rintro _ ⟨t, rfl⟩
    refine ⟨(space α β R r).toSSetObjEquiv _ τ t, hb _ ⟨t, rfl⟩, ?_⟩
    have he := congrArg (fun s => (ambient α β R).toSSetObjEquiv _ s t) hτ
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
    exact he

def component (q : ℕ) :
    (small (ambient α β R) (cover α β R r η ρ)).X (d + q) ⟶
      (chains (TopCat.of (domain α β R r hR hr F B))).X q :=
  EmbeddedCapOutputSupport.component (ambient α β R) (space α β R r) (proper α β R r)
    (properIso α β R r) (domain α β R r hR hr F B) (cover α β R r η ρ) d ξ
    (parent_bound α β R r hR hr F B η ρ d ξ hfar good) q

theorem component_source (q : ℕ) :
    component α β R r hR hr F B η ρ d ξ hfar good q ≫
      (push (FirstInputRotationAmbientCap.source α β R r hR hr F B)).f q =
    (inclusion (ambient α β R) (cover α β R r η ρ)).f (d + q) ≫
      absoluteChain (ambient α β R) d q (d + q) rfl ξ :=
  EmbeddedCapOutputSupport.component_source (ambient α β R) (space α β R r) (proper α β R r)
    (properIso α β R r) (domain α β R r hR hr F B) (cover α β R r η ρ) d ξ
    (parent_bound α β R r hR hr F B η ρ d ξ hfar good) q

end
end Finsler.FirstInputRotationAmbientSupportedCap
