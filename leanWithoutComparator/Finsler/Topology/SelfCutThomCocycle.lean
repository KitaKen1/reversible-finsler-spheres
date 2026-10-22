module

public import Finsler.Topology.DiagonalAvoidanceCocycle
public import Finsler.Analysis.H1SelfCutNeighborhood
public import Finsler.Topology.SupportedCapNaturality

/-! Pull the actual far-and-diagonal relative cochain to the genuine H1
self-evaluation. Its time-end pullbacks vanish as cochains, not only in
cohomology. Normalization and the final supported D_T remain separate. -/

@[expose] public section
namespace Finsler.SelfCutThomCocycle

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.BorelEvaluation Finsler.DiagonalCohomology
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem pullback_zero_of_range {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    {X : TopCat.{0}} (f : X ⟶ product n)
    (hf : ∀ x, f x ∈ DiagonalAvoidanceCocycle.avoid n ρ) :
    cochainPullback f n (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ) = 0 := by
  let g : X ⟶ TopCat.of (⋃ i, DiagonalAvoidanceCocycle.parts n ρ i) :=
    TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ DiagonalAvoidanceCocycle.inclusion n ρ := by
    ext x : 1
    rfl
  rw [he, SupportedCapNaturality.pullback_comp]
  have hz := DiagonalAvoidanceCocycle.ambient_supported n hn hρ
  exact (congrArg (cochainPullback g n) hz).trans (by simp [cochainPullback])

theorem pullback_zero_of_diagonal {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    {X : TopCat.{0}} (f : X ⟶ product n) (hf : ∀ x, (f x).1 = (f x).2) :
    cochainPullback f n (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ) = 0 := by
  apply pullback_zero_of_range hn hρ f
  intro x
  exact mem_iUnion.mpr ⟨true, hf x⟩

theorem pullback_zero_of_far {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    {X : TopCat.{0}} (f : X ⟶ product n)
    (hf : ∀ x, ρ ≤ ‖((f x).2 : Ambient n) - (f x).1‖) :
    cochainPullback f n (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ) = 0 := by
  apply pullback_zero_of_range hn hρ f
  intro x
  exact mem_iUnion.mpr ⟨false, hf x⟩

def parameters (n : ℕ) : TopCat.{0} := TopCat.of (ClosedInterval × SphereLoop n)

def selfEvaluation (n : ℕ) : parameters n ⟶ product n :=
  TopCat.ofHom ⟨fun z => (point z.2, endpoint z),
    (continuous_point.comp continuous_snd).prodMk continuous_endpoint⟩

def timeEvaluation (n : ℕ) (t : ClosedInterval) : TopCat.of (SphereLoop n) ⟶ product n :=
  TopCat.ofHom ⟨fun u => (point u, sphereRepresentative u t),
    continuous_point.prodMk (continuous_endpoint.comp
      (continuous_const.prodMk continuous_id))⟩

def atTime (n : ℕ) (t : ClosedInterval) : TopCat.of (SphereLoop n) ⟶ parameters n :=
  TopCat.ofHom ⟨fun u => (t, u), continuous_const.prodMk continuous_id⟩

theorem time_factor (n : ℕ) (t : ClosedInterval) :
    atTime n t ≫ selfEvaluation n = timeEvaluation n t := by
  ext x : 1
  rfl

def cocycle (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (parameters n) n :=
  cochainPullback (selfEvaluation n) n (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ)

theorem cocycle_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (parameters n) n (cocycle n hn hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (product n))
    (singularCochainComplexZMod2.map (selfEvaluation n).op) n
    (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ)
    (DiagonalAvoidanceCocycle.ambient_closed n hn hρ)

theorem time_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (atTime n 0) n (cocycle n hn hρ) = 0 := by
  change cochainPullback (atTime n 0) n
    (cochainPullback (selfEvaluation n) n _) = 0
  rw [← SupportedCapNaturality.pullback_comp, time_factor]
  exact pullback_zero_of_diagonal hn hρ (timeEvaluation n 0) (fun _ => rfl)

theorem time_one (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (atTime n 1) n (cocycle n hn hρ) = 0 := by
  change cochainPullback (atTime n 1) n
    (cochainPullback (selfEvaluation n) n _) = 0
  rw [← SupportedCapNaturality.pullback_comp, time_factor]
  exact pullback_zero_of_diagonal hn hρ (timeEvaluation n 1)
    (fun u => (sphereRepresentative_endpoints u).symm)

end
end Finsler.SelfCutThomCocycle
