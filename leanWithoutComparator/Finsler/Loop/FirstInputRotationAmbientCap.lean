module

public import Finsler.Loop.FirstInputRotationAmbientCover
public import Finsler.Loop.FirstInputRotationTestedDomainCap
public import Finsler.Loop.DegreeLoweringComposition
public import Finsler.Topology.TubeCochainExtension

/-! A genuinely closed bounded two-stage cap on the entire ambient
rotation/cut cylinder. The Thom cap first localizes into the proper
small cut domain; the actual tested cap then lands in its bounded part.
The source formula uses the literal tested zero extension, without
asserting that extension is globally closed. -/

@[expose] public section
namespace Finsler.FirstInputRotationAmbientCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationFilteredCap
open Finsler.FirstInputRotationAmbientCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)

def ambientTested : singularCochainGroup (ZMod 2) (ambient α β R) p :=
  TubeCochainExtension.extend (ambient α β R) (proper α β R r) p
    (cochainPullback (properIso α β R r).inv p (tested α β R r hR hr p T))

theorem tested_restriction :
    cochainPullback (FirstInputRotationAmbientCover.source α β R r) p
      (ambientTested α β R r hR hr p T) = tested α β R r hR hr p T := by
  rw [ambientTested, FirstInputRotationAmbientCover.source, SmallCapSubspaceLift.source,
    pullback_comp, TubeCochainExtension.restriction, ← pullback_comp, Iso.hom_inv_id]
  exact congrArg (fun f => (f.f p).hom (tested α β R r hR hr p T))
    (singularCochainComplexZMod2.map_id (Opposite.op (space α β R r)))

variable (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (F : ReversibleMetric n) (B η : ℝ)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)

def operation : DegreeLoweringHomology.Map
    (small (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ))
    (chains (TopCat.of (domain α β R r hR hr F B))) (n + p) :=
  DegreeLoweringComposition.compose (cap α β R r hR η hn h)
    (FirstInputRotationTestedDomainCap.operation α β R r hR hr F B η p T hgood hT)

def source : TopCat.of (domain α β R r hR hr F B) ⟶ ambient α β R :=
  FirstInputRotationFilteredCap.source α β R r hR hr F B ≫ FirstInputRotationAmbientCover.source α β R r

theorem source_mono (q : ℕ) : Mono ((push (source α β R r hR hr F B)).f q) := by
  haveI : Mono (SupportedCap.subspaceMap (ambient α β R) (proper α β R r)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (FirstInputRotationAmbientCover.source α β R r) := by
    dsimp only [FirstInputRotationAmbientCover.source, SmallCapSubspaceLift.source]
    infer_instance
  haveI : Mono (FirstInputRotationFilteredCap.source α β R r hR hr F B) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (source α β R r hR hr F B) := by dsimp only [source]; infer_instance
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (source α β R r hR hr F B)).app (Opposite.op ⦋q⦌))))

theorem component_source (q : ℕ) :
    (operation α β R r hR hr p T hn h F B η hgood hT).component q ≫
        (push (source α β R r hR hr F B)).f q =
      eqToHom (congrArg (small (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ)).X
        (Nat.add_assoc n p q)) ≫
        (inclusion (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ)).f (n + (p + q)) ≫
          PartialDoubleCap.cap (ambient α β R) n p q (ambientThom α β R hR hn h)
            (ambientTested α β R r hR hr p T) := by
  let a := cap α β R r hR η hn h
  let b := FirstInputRotationTestedDomainCap.operation α β R r hR hr F B η p T hgood hT
  let j := FirstInputRotationAmbientCover.source α β R r
  have hb := FirstInputRotationTestedDomainCap.component_inclusion α β R r hR hr F B η p T hgood hT q
  have ha := cap_source α β R r hR η hn h (p + q)
  simp only [HomologicalComplex.comp_f] at ha
  have ht := RelativeCapBoundary.absolute_chain_natural j p q (p + q) rfl
    (ambientTested α β R r hR hr p T)
  rw [tested_restriction] at ht
  change absoluteChain (space α β R r) p q (p + q) rfl (tested α β R r hR hr p T) ≫
    (push j).f q = (push j).f (p + q) ≫
      absoluteChain (ambient α β R) p q (p + q) rfl (ambientTested α β R r hR hr p T) at ht
  change ((DegreeLoweringComposition.compose a b).component q) ≫ _ = _
  rw [DegreeLoweringComposition.component, source, push_comp, HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [← Category.assoc (b.component q), hb]
  simp only [Category.assoc]
  rw [ht]
  have hs := congrArg (fun g => g ≫
    absoluteChain (ambient α β R) p q (p + q) rfl (ambientTested α β R r hR hr p T)) ha
  simpa only [PartialDoubleCap.cap, Category.assoc] using
    congrArg (fun g => eqToHom (congrArg
      (small (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ)).X
      (Nat.add_assoc n p q)) ≫ g) hs

def retainedOperation : DegreeLoweringHomology.Map
    (small (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ))
    (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (n + p) :=
  (operation α β R r hR hr p T hn h F B η hgood hT).post
    (push (retained α β R r hR hr F B))

end
end Finsler.FirstInputRotationAmbientCap
