module

public import Finsler.Topology.RectangleCarrierFactor
public import Finsler.Topology.FilteredOriginalJoin

/-! An actual rectangle comparison, after cap, lives in the genuine
bounded near-pair subspace when its whole parent rectangle satisfies the
stated bounds. The original-join homotopy is then inside the length cut. -/

@[expose] public section
namespace Finsler.JoinRectangleComparison

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.H1FiberBase Finsler.JoinDirectionComparison Finsler.VariableJoinContinuity
open Finsler.SobolevLength Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity
open scoped Topology Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def loopSpace (n : ℕ) : TopCat.{0} := TopCat.of (SphereLoop n)
def pairSpace (n : ℕ) : TopCat.{0} := loopSpace n ⊗ loopSpace n

variable {n : ℕ} (F : ReversibleMetric n) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
  {ε : ℝ} (hε : 0 < ε)

def flatDomain : Set (pairSpace n) := {z |
  dist (basepoint z.1) (basepoint z.2) < FilteredOriginalJoin.radius F p q hp hq hε ∧
    length F z.1 ≤ p ∧ length F z.2 ≤ q}

def toDomain : C(flatDomain F p q hp hq hε, FilteredOriginalJoin.domain F p q hp hq hε) := by
  have hnear (z : flatDomain F p q hp hq hε) : z.val ∈ nearPairs n :=
    z.property.1.trans_le (FilteredOriginalJoin.radius_spec F p q hp hq hε).2.1
  refine ⟨fun z => ⟨⟨z.val, hnear z⟩, z.property⟩, ?_⟩
  have h : Continuous (fun z : flatDomain F p q hp hq hε => (⟨z.val, hnear z⟩ : nearPairs n)) :=
    continuous_subtype_val.subtype_mk _
  exact h.subtype_mk _

def homotopy (a : Splits) :
    ((FilteredOriginalJoin.atTime F p q hp hq hε a 0).comp (toDomain F p q hp hq hε)).Homotopy
      ((FilteredOriginalJoin.atTime F p q hp hq hε a 1).comp (toDomain F p q hp hq hε)) :=
  (FilteredOriginalJoin.homotopy F p q hp hq hε a).compContinuousMap (toDomain F p q hp hq hε)

variable {ι κ : Type*} (U : ι → Set (loopSpace n)) (V : κ → Set (loopSpace n))
  (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
  (i j : ℕ) (σ : TopCat.toSSet.obj (loopSpace n) _⦋i⦌)
  (τ : TopCat.toSSet.obj (loopSpace n) _⦋j⦌)
  (hrect : ∀ u ∈ Set.range ((loopSpace n).toSSetObjEquiv _ σ),
    ∀ v ∈ Set.range ((loopSpace n).toSSetObjEquiv _ τ),
      dist (basepoint u) (basepoint v) < FilteredOriginalJoin.radius F p q hp hq hε ∧
        length F u ≤ p ∧ length F v ≤ q)

include hrect in
theorem cap_factor (k r : ℕ) (h : k + r = i + j + 1)
    (φ : singularCochainGroup (ZMod 2) (pairSpace n) k) :
    ∃ d : coeff ⟶ (chains (TopCat.of (flatDomain F p q hp hq hε))).X r,
      d ≫ (push (SupportedCap.subspaceMap (pairSpace n) (flatDomain F p q hp hq hε))).f r =
        RectangleCarrierFactor.prism U V hU hcoverU hV hcoverV i j σ τ ≫
          absoluteChain (pairSpace n) k r (i + j + 1) h φ := by
  have hf : ∀ u ∈ Set.range ((loopSpace n).toSSetObjEquiv _ σ),
      ∀ v ∈ Set.range ((loopSpace n).toSSetObjEquiv _ τ),
      (𝟙 (pairSpace n)) (u, v) ∈ flatDomain F p q hp hq hε := hrect
  have ht := RectangleCarrierFactor.cap_push_factor U V hU hcoverU hV hcoverV i j σ τ
    (𝟙 (pairSpace n)) (flatDomain F p q hp hq hε) hf k r h φ
  have hid : push (𝟙 (pairSpace n)) = 𝟙 (chains (pairSpace n)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (pairSpace n))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  obtain ⟨d, hd⟩ := ht
  refine ⟨d, ?_⟩
  change d ≫ (push (SupportedCap.subspaceMap (pairSpace n) (flatDomain F p q hp hq hε))).f r =
    RectangleCarrierFactor.prism U V hU hcoverU hV hcoverV i j σ τ ≫
      absoluteChain (pairSpace n) k r (i + j + 1) h φ ≫ (push (𝟙 (pairSpace n))).f r at hd
  rw [hid, HomologicalComplex.id_f] at hd
  exact hd.trans (congrArg (fun z =>
    RectangleCarrierFactor.prism U V hU hcoverU hV hcoverV i j σ τ ≫ z)
    (Category.comp_id (absoluteChain (pairSpace n) k r (i + j + 1) h φ)))

end
end Finsler.JoinRectangleComparison
