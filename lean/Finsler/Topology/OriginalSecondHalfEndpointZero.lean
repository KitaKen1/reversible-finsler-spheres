module

public import Finsler.Topology.TubeExtensionPullback
public import Finsler.Topology.OriginalSecondHalfFamily
public import Finsler.Topology.ThreeCapFunctoriality
public import Finsler.Topology.SupportedSelfCutAdequacy
public import Finsler.Topology.AnnularSupportedCut

/-! Both original second-half time faces kill the literal annular
zero extension, even for a genuinely partial compact outer tube. The
actual three successive caps consequently vanish on those faces. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfEndpointZero

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.ThreeCapBlockVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}

def face (t : ClosedInterval) : TopCat.of (P × Q) ⟶ TopCat.of (P × (ClosedInterval × Q)) :=
  TopCat.ofHom ⟨fun z => (z.1, (t, z.2)), continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩

def region (t : ClosedInterval) : Set (P × (ClosedInterval × Q)) := {z | z.2.1 = t}

theorem face_region (t : ClosedInterval) :
    Set.range (face (P := P) (Q := Q) t) ⊆ region (P := P) (Q := Q) t := by
  rintro _ ⟨z, rfl⟩
  rfl

variable (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)

theorem thom_face (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime n t) n (AnnularSelfCut.cocycle n hn h) = 0) :
    cochainPullback (face (P := P) (Q := Q) t) n
      (SupportedSelfCutAdequacy.extension K
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
        (AnnularSelfCut.cocycle n hn h)) = 0 := by
  let f := face (P := P) (Q := Q) t
  let g := restriction f (f ⁻¹' K) K (fun _ hz => hz)
  let b : TopCat.of (f ⁻¹' K) ⟶ TopCat.of (SphereLoop n) :=
    TopCat.ofHom ⟨fun z => β z.val.2,
      β.continuous.comp (continuous_snd.comp continuous_subtype_val)⟩
  have he : g ≫ OriginalSecondHalfFamily.projection K ≫ OriginalSecondHalfFamily.native β =
      b ≫ SelfCutThomCocycle.atTime n t := by
    ext z : 1
    rfl
  unfold SupportedSelfCutAdequacy.extension
  apply TubeExtensionPullback.pullback_zero
  change cochainPullback g n
    (cochainPullback (OriginalSecondHalfFamily.family α β K hK) n (AnnularSelfCut.cocycle n hn h)) = 0
  rw [OriginalSecondHalfFamily.annular_thom_factor, ← pullback_comp, he, pullback_comp, ht]
  exact map_zero _

theorem thom_zero : cochainPullback (face (P := P) (Q := Q) 0) n
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
      (AnnularSelfCut.cocycle n hn h)) = 0 :=
  thom_face α β K hK hn h 0 (AnnularSupportedCut.time_zero n hn h)

theorem thom_one : cochainPullback (face (P := P) (Q := Q) 1) n
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
      (AnnularSelfCut.cocycle n hn h)) = 0 :=
  thom_face α β K hK hn h 1 (AnnularSupportedCut.time_one n hn h)

theorem thom_region (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime n t) n (AnnularSelfCut.cocycle n hn h) = 0) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (region (P := P) (Q := Q) t)) n
      (SupportedSelfCutAdequacy.extension K
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
        (AnnularSelfCut.cocycle n hn h)) = 0 := by
  let b : TopCat.of (region (P := P) (Q := Q) t) ⟶ TopCat.of (P × Q) :=
    TopCat.ofHom ⟨fun z => (z.val.1, z.val.2.2),
      (continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))⟩
  have he : b ≫ face t = SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (region (P := P) (Q := Q) t) := by
    ext z : 1
    exact Prod.ext rfl (Prod.ext z.property.symm rfl)
  rw [← he, pullback_comp, thom_face α β K hK hn h t ht]
  exact map_zero _

theorem cap_face_zero (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime n t) n (AnnularSelfCut.cocycle n hn h) = 0)
    (a p q : ℕ) (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) p) :
    (push (face (P := P) (Q := Q) t)).f (a + n + p + q) ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
          (AnnularSelfCut.cocycle n hn h)) ψ = 0 := by
  have he := ThreeCapFunctoriality.natural (face (P := P) (Q := Q) t) a n p q J
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
      (AnnularSelfCut.cocycle n hn h)) ψ
  rw [thom_face α β K hK hn h t ht] at he
  have hz : threeCap (TopCat.of (P × Q)) a n p q
      (cochainPullback (face (P := P) (Q := Q) t) a J) 0
      (cochainPullback (face (P := P) (Q := Q) t) p ψ) = 0 := by
    simp only [threeCap, map_zero, comp_zero, zero_comp]
  rw [hz, zero_comp] at he
  exact he.symm

end
end Finsler.OriginalSecondHalfEndpointZero
