module

public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Loop.FarDiagonalCutComparison

/-! Every degree of actual cochain supported off the far set has the
same whole-parent near carrier on the original rectangle cover.
Nonclosed primitive cochains therefore have real cap lifts into that
closed carrier as well. -/

@[expose] public section
namespace Finsler.CompactFarCarrierCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (κ R : ℝ) (hκR : 2 * κ ≤ R)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q))
    (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
      (fun x => basepoint (α x)) (fun y => basepoint (β y)) κ)) d φ = 0)

include hκR hfar in
theorem parent_near (q : ℕ)
    (σ : ((TopCat.of (P × Q)).smallSingularSubcomplex (CompactJoinCapLocalization.cover α β κ) : SSet) _⦋d + q⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ.val ≫
      absoluteChain (TopCat.of (P × Q)) d q (d + q) rfl φ ≠ 0) :
    Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ.val) ⊆ CompactNearJoinParameters.tube α β R := by
  obtain ⟨⟨x, y⟩, hs⟩ := (TopCat.mem_smallSingularSubcomplex_iff (TopCat.of (P × Q))
    (CompactJoinCapLocalization.cover α β κ) σ.val).mp σ.property
  rcases PairDistanceCover.near_far_rectangle (fun x => basepoint (α x)) (fun y => basepoint (β y)) κ x y with hf | hn
  · have hwhole : Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ.val) ⊆
        NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
          (fun x => basepoint (α x)) (fun y => basepoint (β y)) κ := by
      intro z hz
      exact hf z.1 (hs hz).1 z.2 (hs hz).2
    exact (hσ (SupportedCap.cap_zero_on_simplex (TopCat.of (P × Q)) _ d q (d + q) rfl φ hfar σ.val hwhole)).elim
  · intro z hz
    exact (hn z.1 (hs hz).1 z.2 (hs hz).2).le.trans hκR

def component (q : ℕ) := CapOutputSupport.component (CompactJoinCapLocalization.cover α β κ) (𝟙 (TopCat.of (P × Q)))
  (CompactNearJoinParameters.tube α β R) d φ (fun q σ hn z hz => parent_near α β κ R hκR d φ hfar q σ hn hz) q

theorem source (q : ℕ) : component α β κ R hκR d φ hfar q ≫
    (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R))).f q =
    (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (d + q) ≫
      absoluteChain (TopCat.of (P × Q)) d q (d + q) rfl φ := by
  have he := CapOutputSupport.component_inclusion (CompactJoinCapLocalization.cover α β κ) (𝟙 (TopCat.of (P × Q)))
    (CompactNearJoinParameters.tube α β R) d φ (fun q σ hn z hz => parent_near α β κ R hκR d φ hfar q σ hn hz) q
  rw [FarDiagonalCutComparison.push_identity, HomologicalComplex.id_f] at he
  exact he.trans (congrArg (fun z => (inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)).f (d + q) ≫ z)
    (Category.comp_id (absoluteChain (TopCat.of (P × Q)) d q (d + q) rfl φ)))

def operation (hc : cochainCoboundary (ZMod 2) (TopCat.of (P × Q)) d φ = 0) :=
  CapOutputSupport.operation (CompactJoinCapLocalization.cover α β κ) (𝟙 (TopCat.of (P × Q)))
    (CompactNearJoinParameters.tube α β R) d φ (fun q σ hn z hz => parent_near α β κ R hκR d φ hfar q σ hn hz) hc

end
end Finsler.CompactFarCarrierCap
