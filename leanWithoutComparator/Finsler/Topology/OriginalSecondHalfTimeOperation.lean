module

public import Finsler.Topology.OriginalSecondHalfEndpointZero
public import Finsler.Topology.ThreeCapRetractionZero
public import Finsler.Topology.OriginalSecondHalfCapUniqueness
public import Finsler.Topology.ClosedCapDegreeTransport
public import Finsler.Topology.AnnularTimeTrim
public import Finsler.Topology.TimePrismDescent

/-! The original second-half auxiliary time operation, already valued
in its actual bounded cut domain. Both actual time endpoints vanish
after source approximation and before the retained map. Therefore the
genuine time prism descends to a closed degree-lowering operation. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfTimeOperation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem transport_f {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg C.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_d (C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)
    (i i' j j' : ℕ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg C.X hi) ≫ C.d i' j' = C.d i j ≫ eqToHom (congrArg C.X hj) := by
  subst i'; subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]

def reorder : TopCat.of (ClosedInterval × (P × Q)) ⟶ TopCat.of (P × (ClosedInterval × Q)) :=
  TopCat.ofHom ⟨fun z => (z.2.1, (z.1, z.2.2)),
    (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))⟩

theorem slice_reorder (t : ClosedInterval) :
    AnnularTimeTrim.slice (TopCat.of (P × Q)) t ≫ reorder =
      OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t := by
  ext z : 1
  rfl

def prism : Homotopy
    (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 0))
    (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 1)) := by
  have H := ((AnnularTimeTrim.cylinder (TopCat.of (P × Q))).toSSet.chainComplexMap coeff).compRight
    (push (reorder (P := P) (Q := Q)))
  change Homotopy
    (push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) ≫ push (reorder (P := P) (Q := Q)))
    (push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1) ≫ push (reorder (P := P) (Q := Q))) at H
  simpa only [← push_comp, slice_reorder] using H

variable {s : ℕ} (α : C(P, SphereLoop (s + 1))) (β : C(Q, SphereLoop (s + 1)))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (s + 1)) (B : ℝ)
  {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q)))
  (hW : ∀ v, IsOpen (W v)) (hcW : ⋃ v, W v = Set.univ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (a p : ℕ)
  (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (s + 1))) p)
  (u : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) W)
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + (s + 1) + p))
  (hu : ∀ q, u.component q ≫ (push (source α β K hK r hr F B)).f q =
    (inclusion (TopCat.of (P × (ClosedInterval × Q))) W).f (a + (s + 1) + p + q) ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a (s + 1) p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
          (AnnularSelfCut.cocycle (s + 1) (by omega) h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T))

def nested (q : ℕ) : (chains (TopCat.of (P × (ClosedInterval × Q)))).X
    (((a + s) + 1) + (p + q)) ⟶ (chains (TopCat.of (bounded α β K hK r hr F B))).X q :=
  eqToHom (congrArg (chains (TopCat.of (P × (ClosedInterval × Q)))).X
    (show ((a + s) + 1) + (p + q) = a + (s + 1) + p + q by omega)) ≫
    (u.pre (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff W hW hcW)).component q

theorem nested_comm (q : ℕ) :
    nested α β K hK r hr F B W hW hcW a p u (q + 1) ≫
      (chains (TopCat.of (bounded α β K hK r hr F B))).d (q + 1) q =
    (chains (TopCat.of (P × (ClosedInterval × Q)))).d
      (((a + s) + 1) + (p + (q + 1))) (((a + s) + 1) + (p + q)) ≫
      nested α β K hK r hr F B W hW hcW a p u q := by
  dsimp only [nested]
  rw [Category.assoc,
    (u.pre (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff W hW hcW)).comm,
    ← Category.assoc, transport_d, Category.assoc]
  all_goals omega

include hu in
theorem endpoint_zero (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime (s + 1) t) (s + 1)
      (AnnularSelfCut.cocycle (s + 1) (by omega) h) = 0) (q : ℕ) :
    (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t)).f ((a + s + p) + q + 1) ≫
      ClosedCapDegreeTransport.align (a + s) p (nested α β K hK r hr F B W hW hcW a p u) q = 0 := by
  haveI := OriginalSecondHalfCapUniqueness.source_mono α β K hK r hr F B q
  have hz := ThreeCapRetractionZero.after_retraction
    (X := TopCat.of (P × (ClosedInterval × Q))) W hW hcW
    (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t)
    (OriginalSecondHalfEndpointZero.region (P := P) (Q := Q) t)
    (OriginalSecondHalfEndpointZero.face_region t) a (s + 1) p q J
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
      (AnnularSelfCut.cocycle (s + 1) (by omega) h))
    (SelfCutParameterFamily.testedExtension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
      (fun _ => r) (fun _ => hr) PUnit.unit p T)
    (OriginalSecondHalfEndpointZero.thom_region α β K hK (by omega) h t ht)
    u (push (source α β K hK r hr F B)) (hu q)
  have hz' : (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t)).f
      (((a + s) + 1) + (p + q)) ≫ nested α β K hK r hr F B W hW hcW a p u q = 0 := by
    dsimp only [nested]
    rw [← Category.assoc, ← transport_f
      (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t))
      (((a + s) + 1) + (p + q)) (a + (s + 1) + p + q) (by omega), Category.assoc]
    have hz'' : (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t)).f
        (a + (s + 1) + p + q) ≫
        (u.pre (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff W hW hcW)).component q = 0 := by
      simpa only [DegreeLoweringHomology.Map.pre, HomologicalComplex.comp_f, Category.assoc] using hz
    rw [hz'', comp_zero]
  dsimp only [ClosedCapDegreeTransport.align]
  rw [← Category.assoc, ← transport_f
    (push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t))
    ((a + s + p) + q + 1) (((a + s) + 1) + (p + q)) (by omega), Category.assoc,
    hz', comp_zero]

def operation : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + s + p) :=
  TimePrismDescent.operation (prism (P := P) (Q := Q)) (a + s + p)
    (ClosedCapDegreeTransport.align (a + s) p (nested α β K hK r hr F B W hW hcW a p u))
    (ClosedCapDegreeTransport.align_comm (a + s) p
      (nested α β K hK r hr F B W hW hcW a p u)
      (nested_comm α β K hK r hr F B W hW hcW a p u))
    (endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu 0
      (AnnularSupportedCut.time_zero (s + 1) (by omega) h))
    (endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu 1
      (AnnularSupportedCut.time_one (s + 1) (by omega) h))

def output : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  (operation α β K hK r hr F B W hW hcW h a p J T u hu).post
    (push (retained α β K hK r hr F B))

end
end Finsler.OriginalSecondHalfTimeOperation
