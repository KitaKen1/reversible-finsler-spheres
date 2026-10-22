module

public import Finsler.Topology.SupportedCapAnnihilation
public import Finsler.Topology.NormalizedSelfCut

/-! Literal endpoint cancellation for the actual supported self-cut,
including the small-chain approximation used by the Thom operation. -/

@[expose] public section
namespace Finsler.SelfCutEndpoints

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem cut_map_zero {X Y : TopCat.{0}} (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p)
    (hAφ : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
    (hCφ : cochainPullback (SupportedCap.subspaceMap X C) p φ = 0)
    (f : Y ⟶ X) (hf : ∀ y, f y ∈ C) :
    (SupportedCapNaturality.push f).f (p + q) ≫
      SupportedCap.cut X A B hA hB hcover p q (p + q) rfl φ hAφ = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  rw [← Category.assoc, SupportedCapNaturality.push, SSet.ι_chainComplexMap_f, comp_zero]
  apply SupportedCapAnnihilation.cut_zero_of_supported X A B C hA hB hcover p q φ hAφ hCφ
  have hs : (TopCat.toSSet.map f).app (Opposite.op ⦋p + q⦌) σ ∈
      (X.smallSingularSubcomplex (fun _ : Unit => C)).obj (Opposite.op ⦋p + q⦌) := by
    apply (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => C) _).mpr
    refine ⟨(), ?_⟩
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨z, rfl⟩
    exact hf _
  exact TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff)
    (U := fun _ : Unit => C) ⟨_, hs⟩

def timeSlice (n : ℕ) (t : ClosedInterval) : Set (parameters n) := {z | z.1 = t}

def sliceProjection (n : ℕ) (t : ClosedInterval) :
    TopCat.of (timeSlice n t) ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

theorem slice_factor (n : ℕ) (t : ClosedInterval) :
    SupportedCap.subspaceMap (parameters n) (timeSlice n t) =
      sliceProjection n t ≫ atTime n t := by
  ext z : 1
  exact Prod.ext z.property rfl

theorem slice_cocycle_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    (t : ClosedInterval)
    (ht : cochainPullback (atTime n t) n (NormalizedSelfCut.cocycle n hn hρ) = 0) :
    cochainPullback (SupportedCap.subspaceMap (parameters n) (timeSlice n t)) n
      (NormalizedSelfCut.cocycle n hn hρ) = 0 := by
  rw [slice_factor, SupportedCapNaturality.pullback_comp, ht]
  simp [cochainPullback]

theorem thom_atTime_zero (n q : ℕ) (hn : 1 ≤ n) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (t : ClosedInterval)
    (ht : cochainPullback (atTime n t) n (NormalizedSelfCut.cocycle n hn hρ) = 0) :
    (SupportedCapNaturality.push (atTime n t)).f (n + q) ≫
      (NormalizedSelfCut.operation n hn hρ hρr).component q = 0 := by
  exact cut_map_zero (exterior n ρ) (neighborhood n r) (timeSlice n t)
    (exterior_open n ρ) (neighborhood_open n r) (cover n hρr) n q
    (NormalizedSelfCut.cocycle n hn hρ) (NormalizedSelfCut.cocycle_supported n hn hρ)
    (slice_cocycle_zero n hn hρ t ht) (atTime n t) (fun _ => rfl)

theorem chainCut_atTime_zero (n p q : ℕ) (hn : 1 ≤ n) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (t : ClosedInterval)
    (ht : cochainPullback (atTime n t) n (NormalizedSelfCut.cocycle n hn hρ) = 0) :
    (SupportedCapNaturality.push (atTime n t)).f (n + (p + q)) ≫
      NormalizedSelfCut.chainCut n p hn hρ hρr hr T hT q = 0 := by
  rw [NormalizedSelfCut.chainCut, ← Category.assoc, thom_atTime_zero n (p + q) hn hρ hρr t ht,
    zero_comp]

theorem chainCut_time_zero (n p q : ℕ) (hn : 1 ≤ n) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    (SupportedCapNaturality.push (atTime n 0)).f (n + (p + q)) ≫
      NormalizedSelfCut.chainCut n p hn hρ hρr hr T hT q = 0 :=
  chainCut_atTime_zero n p q hn hρ hρr hr T hT 0 (NormalizedSelfCut.time_zero n hn hρ)

theorem chainCut_time_one (n p q : ℕ) (hn : 1 ≤ n) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    (SupportedCapNaturality.push (atTime n 1)).f (n + (p + q)) ≫
      NormalizedSelfCut.chainCut n p hn hρ hρr hr T hT q = 0 :=
  chainCut_atTime_zero n p q hn hρ hρr hr T hT 1 (NormalizedSelfCut.time_one n hn hρ)

end
end Finsler.SelfCutEndpoints
