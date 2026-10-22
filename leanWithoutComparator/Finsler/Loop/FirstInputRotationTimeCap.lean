module

public import Finsler.Loop.FirstInputRotationCutCylinder
public import Finsler.Loop.NestedCapUnpack
public import Finsler.Topology.NestedCapRefinement

/-! The actual bounded rotating cap on the cut-time-first cylinder,
with its genuine nested degree convention and chain-monic source.
The target remains the original bounded proper cut domain. -/

@[expose] public section
namespace Finsler.FirstInputRotationTimeCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCutCylinder
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (F : ReversibleMetric n) (B η : ℝ)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)

abbrev target : TopCat.{0} := TopCat.of (FirstInputRotationFilteredCap.domain α β R r hR hr F B)

def oldRaw (q : ℕ) :
    (small (FirstInputRotationAmbientCover.ambient α β R)
      (FirstInputRotationAmbientCover.cover α β R r η ρ)).X (n + (p + q)) ⟶
        (chains (target α β R r hR hr F B)).X q :=
  NestedCapUnpack.component n p
    (FirstInputRotationAmbientCap.operation α β R r hR hr p T hn h F B η hgood hT) q

theorem oldRaw_comm (q : ℕ) :
    oldRaw α β R r hR hr p T hn h F B η hgood hT (q + 1) ≫
        (chains (target α β R r hR hr F B)).d (q + 1) q =
      (small (FirstInputRotationAmbientCover.ambient α β R)
        (FirstInputRotationAmbientCover.cover α β R r η ρ)).d
          (n + (p + (q + 1))) (n + (p + q)) ≫
            oldRaw α β R r hR hr p T hn h F B η hgood hT q :=
  NestedCapUnpack.comm n p _ q

theorem oldRaw_source (q : ℕ) :
    oldRaw α β R r hR hr p T hn h F B η hgood hT q ≫
        (push (FirstInputRotationAmbientCap.source α β R r hR hr F B)).f q =
      (inclusion (FirstInputRotationAmbientCover.ambient α β R)
        (FirstInputRotationAmbientCover.cover α β R r η ρ)).f (n + (p + q)) ≫
          PartialDoubleCap.cap (FirstInputRotationAmbientCover.ambient α β R) n p q
            (FirstInputRotationAmbientCover.ambientThom α β R hR hn h)
            (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T) :=
  NestedCapUnpack.inclusion n p
    (FirstInputRotationAmbientCap.operation α β R r hR hr p T hn h F B η hgood hT)
    (push (FirstInputRotationAmbientCap.source α β R r hR hr F B)) _
    (FirstInputRotationAmbientCap.component_source α β R r hR hr p T hn h F B η hgood hT) q

def component (q : ℕ) :
    (small (cylinder α β R) (cover α β R r η ρ)).X (n + (p + q)) ⟶
      (chains (target α β R r hR hr F B)).X q :=
  NestedCapRefinement.pre n p (smallReorder α β R r η ρ)
    (oldRaw α β R r hR hr p T hn h F B η hgood hT) q

theorem component_comm (q : ℕ) :
    component α β R r hR hr p T hn h F B η hgood hT (q + 1) ≫
        (chains (target α β R r hR hr F B)).d (q + 1) q =
      (small (cylinder α β R) (cover α β R r η ρ)).d
        (n + (p + (q + 1))) (n + (p + q)) ≫
          component α β R r hR hr p T hn h F B η hgood hT q :=
  NestedCapRefinement.pre_comm n p _ _ (oldRaw_comm α β R r hR hr p T hn h F B η hgood hT) q

def source : target α β R r hR hr F B ⟶ cylinder α β R :=
  FirstInputRotationAmbientCap.source α β R r hR hr F B ≫ restore α β R

theorem source_reorder : source α β R r hR hr F B ≫ reorder α β R =
    FirstInputRotationAmbientCap.source α β R r hR hr F B := by
  rw [source, Category.assoc, restore_reorder, Category.comp_id]

theorem reorder_mono (q : ℕ) : Mono ((push (reorder α β R)).f q) := by
  haveI : Mono (reorder α β R) := by dsimp only [reorder]; infer_instance
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (reorder α β R)).app (Opposite.op ⦋q⦌))))

theorem source_mono (q : ℕ) : Mono ((push (source α β R r hR hr F B)).f q) := by
  haveI : Mono ((push (FirstInputRotationAmbientCap.source α β R r hR hr F B)).f q) :=
    FirstInputRotationAmbientCap.source_mono α β R r hR hr F B q
  haveI : Mono (restore α β R) := by dsimp only [restore]; infer_instance
  haveI : Mono ((push (restore α β R)).f q) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      ((TopCat.toSSet.map (restore α β R)).app (Opposite.op ⦋q⦌))))
  rw [source, push_comp, HomologicalComplex.comp_f]
  infer_instance

theorem component_source (q : ℕ) :
    component α β R r hR hr p T hn h F B η hgood hT q ≫
        (push (source α β R r hR hr F B)).f q =
      (inclusion (cylinder α β R) (cover α β R r η ρ)).f (n + (p + q)) ≫
        PartialDoubleCap.cap (cylinder α β R) n p q (thom α β R hR hn h)
          (tested α β R r hR hr p T) := by
  haveI := reorder_mono α β R q
  apply (cancel_mono ((push (reorder α β R)).f q)).mp
  have hj := congrArg (fun f => (push f).f q) (source_reorder α β R r hR hr F B)
  simp only [push_comp, HomologicalComplex.comp_f] at hj
  have hi := congrArg (fun f => f.f (n + (p + q))) (smallReorder_inclusion α β R r η ρ)
  simp only [HomologicalComplex.comp_f] at hi
  have hncap := PartialDoubleCap.cap_natural (reorder α β R) n p q
    (FirstInputRotationAmbientCover.ambientThom α β R hR hn h)
    (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T)
  dsimp only [component, NestedCapRefinement.pre]
  simp only [Category.assoc]
  rw [hj, oldRaw_source]
  simpa only [thom, tested, Category.assoc] using
    (congrArg (fun f => f ≫ PartialDoubleCap.cap (FirstInputRotationAmbientCover.ambient α β R)
      n p q (FirstInputRotationAmbientCover.ambientThom α β R hR hn h)
        (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T)) hi).trans
      (congrArg (fun f => (inclusion (cylinder α β R) (cover α β R r η ρ)).f (n + (p + q)) ≫ f) hncap.symm)

end
end Finsler.FirstInputRotationTimeCap
