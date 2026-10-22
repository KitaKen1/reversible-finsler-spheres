module

public import Finsler.Topology.SingularTimeModelComparison
public import Finsler.Topology.OriginalSecondHalfFullTensorOperation
import all Finsler.Topology.OriginalSecondHalfTimeOperation
import all Finsler.Topology.OriginalSecondHalfTensorTimeOperation
import all Finsler.Topology.OriginalSecondHalfFullTensorOperation

/-! Compare the original full product-time operation after the genuine
cross with the actual unrefined second-input tensor-time operation.
The constructed double prism, postcomposed with the genuine closed
bounded cap, fills their difference in the same retained-length target.
No time-model comparison, filling or target injectivity is assumed. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfTimeModelComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000


variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]

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



def retainedCap (q : ℕ) :
    (chains (TopCat.of (P × (ClosedInterval × Q)))).X ((a + s + p) + q + 1) ⟶
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).X q :=
  ClosedCapDegreeTransport.align (a + s) p
    (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B W hW hcW a p u) q ≫
    (push (retained α β K hK r hr F B)).f q

theorem retainedCap_comm (q : ℕ) :
    retainedCap α β K hK r hr F B W hW hcW a p u (q + 1) ≫
      (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).d (q + 1) q =
    (chains (TopCat.of (P × (ClosedInterval × Q)))).d
      ((a + s + p) + q + 2) ((a + s + p) + q + 1) ≫ retainedCap α β K hK r hr F B W hW hcW a p u q := by
  dsimp only [retainedCap]
  rw [Category.assoc, (push (retained α β K hK r hr F B)).comm, ← Category.assoc,
    ClosedCapDegreeTransport.align_comm (a + s) p
      (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B W hW hcW a p u)
      (OriginalSecondHalfTimeOperation.nested_comm α β K hK r hr F B W hW hcW a p u), Category.assoc]

def productOutput : DegreeLoweringHomology.Map
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  (OriginalSecondHalfTimeOperation.output α β K hK r hr F B W hW hcW h a p J T u hu).pre
    (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))

theorem homology_eq (q : ℕ) :
    (productOutput α β K hK r hr F B W hW hcW h a p J T u hu).homology q = (OriginalSecondHalfFullTensorOperation.output α β K hK r hr F B W hW hcW h a p J T u hu).homology q := by
  apply SingularTimeModelComparison.homology_eq (TopCat.of P) (TopCat.of Q) (a + s + p)
    (retainedCap α β K hK r hr F B W hW hcW a p u) (retainedCap_comm α β K hK r hr F B W hW hcW a p u)
    (productOutput α β K hK r hr F B W hW hcW h a p J T u hu) (OriginalSecondHalfFullTensorOperation.output α β K hK r hr F B W hW hcW h a p J T u hu) _ _ q
  · intro q'
    rw [SingularTimeCylinderMaps.product_original]
    simp only [productOutput, DegreeLoweringHomology.Map.pre, OriginalSecondHalfTimeOperation.output,
      DegreeLoweringHomology.Map.post, OriginalSecondHalfTimeOperation.operation,
      TimePrismDescent.operation, TimePrismDescent.component, retainedCap, Category.assoc]
  · intro q'
    simp only [OriginalSecondHalfFullTensorOperation.output, OriginalSecondHalfFullTensorOperation.operation,
      DegreeLoweringHomology.Map.post, TimePrismDescent.operation, TimePrismDescent.component,
      OriginalSecondHalfTensorTimeOperation.cap, retainedCap, Category.assoc]

end
end Finsler.OriginalSecondHalfTimeModelComparison
