module

public import Finsler.Topology.OriginalSecondHalfTimeOperation
import all Finsler.Topology.OriginalSecondHalfTimeOperation
public import Finsler.Topology.TensorTimePrismComparison
public import Finsler.Topology.SmallCrossNaturality

/-! The genuine second-input tensor-time prism, capped by the original
bounded operation. Cross naturality identifies its endpoint diagrams
with the actual constant-time faces. Their proved vanishing makes this
a closed degree-lowering operation in the same bounded cut domain. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfTensorTimeOperation

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

theorem slice_cross (t : ClosedInterval) :
    (𝟙 (chains (TopCat.of P)) ⊗ₘ push (AnnularTimeTrim.slice (TopCat.of Q) t)) ≫
      SmallRectangleCross.ambient (TopCat.of P) (TopCat.of (ClosedInterval × Q)) =
    SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t) := by
  have hf : (𝟙 (TopCat.of P) ⊗ₘ AnnularTimeTrim.slice (TopCat.of Q) t) =
      OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hid : push (𝟙 (TopCat.of P)) = 𝟙 (chains (TopCat.of P)) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (TopCat.of P))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simpa only [hf, hid] using
    SmallCrossNaturality.ambient_naturality (𝟙 (TopCat.of P)) (AnnularTimeTrim.slice (TopCat.of Q) t)

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


def cap (q : ℕ) :
    (chains (TopCat.of P) ⊗ chains (TopCat.of (ClosedInterval × Q))).X ((a + s + p) + q + 1) ⟶
      (chains (TopCat.of (bounded α β K hK r hr F B))).X q :=
  (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of (ClosedInterval × Q))).f
    ((a + s + p) + q + 1) ≫
    ClosedCapDegreeTransport.align (a + s) p
      (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B W hW hcW a p u) q

theorem cap_comm (q : ℕ) :
    cap α β K hK r hr F B W hW hcW a p u (q + 1) ≫
      (chains (TopCat.of (bounded α β K hK r hr F B))).d (q + 1) q =
    (chains (TopCat.of P) ⊗ chains (TopCat.of (ClosedInterval × Q))).d
      ((a + s + p) + q + 2) ((a + s + p) + q + 1) ≫
      cap α β K hK r hr F B W hW hcW a p u q := by
  dsimp only [cap]
  rw [Category.assoc,
    ClosedCapDegreeTransport.align_comm (a + s) p
      (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B W hW hcW a p u)
      (OriginalSecondHalfTimeOperation.nested_comm α β K hK r hr F B W hW hcW a p u),
    ← Category.assoc]
  have hd := (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of (ClosedInterval × Q))).comm
    ((a + s + p) + q + 2) ((a + s + p) + q + 1)
  change ((SmallRectangleCross.ambient (TopCat.of P) (TopCat.of (ClosedInterval × Q))).f
    ((a + s + p) + q + 2) ≫
    (chains (TopCat.of P ⊗ TopCat.of (ClosedInterval × Q))).d
      ((a + s + p) + q + 2) ((a + s + p) + q + 1)) ≫ _ = _
  simpa only [Nat.add_assoc, Category.assoc] using congrArg
    (fun f => f ≫ ClosedCapDegreeTransport.align (a + s) p
      (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B W hW hcW a p u) q) hd

include hu in
theorem endpoint_zero {ι' κ' : Type*} (U : ι' → Set P) (V : κ' → Set Q)
    (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime (s + 1) t) (s + 1)
      (AnnularSelfCut.cocycle (s + 1) (by omega) h) = 0) (q : ℕ) :
    (inclusion (TopCat.of P) U ⊗ₘ
      (inclusion (TopCat.of Q) V ≫ push (AnnularTimeTrim.slice (TopCat.of Q) t))).f
      ((a + s + p) + q + 1) ≫ cap α β K hK r hr F B W hW hcW a p u q = 0 := by
  have hi : (inclusion (TopCat.of P) U ⊗ₘ inclusion (TopCat.of Q) V) ≫
      (𝟙 (chains (TopCat.of P)) ⊗ₘ push (AnnularTimeTrim.slice (TopCat.of Q) t)) =
      inclusion (TopCat.of P) U ⊗ₘ
        (inclusion (TopCat.of Q) V ≫ push (AnnularTimeTrim.slice (TopCat.of Q) t)) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hf : (inclusion (TopCat.of P) U ⊗ₘ
      (inclusion (TopCat.of Q) V ≫ push (AnnularTimeTrim.slice (TopCat.of Q) t))) ≫
      SmallRectangleCross.ambient (TopCat.of P) (TopCat.of (ClosedInterval × Q)) =
      (inclusion (TopCat.of P) U ⊗ₘ inclusion (TopCat.of Q) V) ≫
        SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫
        push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t) := by
    rw [← hi, Category.assoc, slice_cross]
  dsimp only [cap]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, hf]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [OriginalSecondHalfTimeOperation.endpoint_zero α β K hK r hr F B W hW hcW
    h a p J T u hu t ht q, comp_zero, comp_zero]

variable {ι' κ' : Type*} (U : ι' → Set P) (V : κ' → Set (ClosedInterval × Q))

def operation : DegreeLoweringHomology.Map
    (small (TopCat.of P) U ⊗
      small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + s + p) :=
  TimePrismDescent.operation (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V)
    (a + s + p) (cap α β K hK r hr F B W hW hcW a p u)
    (cap_comm α β K hK r hr F B W hW hcW a p u)
    (endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu
      U (CommonPrismRefinement.endpointCover (TopCat.of Q) V) 0
      (AnnularSupportedCut.time_zero (s + 1) (by omega) h))
    (endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu
      U (CommonPrismRefinement.endpointCover (TopCat.of Q) V) 1
      (AnnularSupportedCut.time_one (s + 1) (by omega) h))

def output : DegreeLoweringHomology.Map
    (small (TopCat.of P) U ⊗
      small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  (operation α β K hK r hr F B W hW hcW h a p J T u hu U V).post
    (push (retained α β K hK r hr F B))

end
end Finsler.OriginalSecondHalfTensorTimeOperation
