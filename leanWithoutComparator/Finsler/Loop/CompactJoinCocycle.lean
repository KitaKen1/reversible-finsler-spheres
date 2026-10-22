module

public import Finsler.Topology.JoinThomCocycle
public import Finsler.Topology.OriginalSecondHalfFamily

/-! The genuine normalized diagonal join cochain for arbitrary compact
parameter families, before imposing any input length threshold. Its
time pullback has the actual far support required by the original
second-half bounded operation and represents the genuine diagonal class. -/

@[expose] public section
namespace Finsler.CompactJoinCocycle

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.CompactH1Alignment Finsler.CochainComparison Finsler.SupportedCapNaturality
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))

def evaluation : TopCat.of (P × Q) ⟶ DiagonalCohomology.product n :=
  TopCat.ofHom ⟨fun z => (point (α z.1), point (β z.2)),
    (continuous_point.comp (α.continuous.comp continuous_fst)).prodMk
      (continuous_point.comp (β.continuous.comp continuous_snd))⟩

def timeProjection : TopCat.of (P × (ClosedInterval × Q)) ⟶ TopCat.of (P × Q) :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.2), continuous_fst.prodMk (continuous_snd.comp continuous_snd)⟩

def cocycle (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) n :=
  cochainPullback (evaluation α β) n (NormalizedDiagonalCocycle.ambient n hn hρ)

def timeCocycle (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) n :=
  cochainPullback (timeProjection (P := P) (Q := Q)) n (cocycle α β hn hρ)

theorem cocycle_closed (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (TopCat.of (P × Q)) n (cocycle α β hn hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (evaluation α β).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)

theorem timeCocycle_closed (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) n
      (timeCocycle α β hn hρ) = 0 :=
  CochainClass.closed_map (cochainCxZMod2 (TopCat.of (P × Q)))
    (singularCochainComplexZMod2.map (timeProjection (P := P) (Q := Q)).op) n
    (cocycle α β hn hρ) (cocycle_closed α β hn hρ)

theorem timeCocycle_pullback (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    timeCocycle α β hn hρ = cochainPullback
      (timeProjection (P := P) (Q := Q) ≫ evaluation α β) n
        (NormalizedDiagonalCocycle.ambient n hn hρ) := by
  rw [timeCocycle, cocycle, pullback_comp]

theorem cocycle_normalized (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (TopCat.of (P × Q)))
      (cocycle α β hn hρ) := by
  have he : cocycle α β hn hρ = SingularNormalization.normalize (TopCat.of (P × Q)) n
      (cochainPullback (evaluation α β) n (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ)) :=
    SingularNormalization.normalize_natural (evaluation α β) n _
  rw [he]
  exact SingularNormalization.normalize_degeneracies _ n _

theorem timeCocycle_normalized (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    DoldKan.DegeneraciesVanish
      (X := SingularNormalization.linearization (TopCat.of (P × (ClosedInterval × Q))))
      (timeCocycle α β hn hρ) := by
  rw [timeCocycle_pullback]
  have he : cochainPullback (timeProjection (P := P) (Q := Q) ≫ evaluation α β) n
      (NormalizedDiagonalCocycle.ambient n hn hρ) =
      SingularNormalization.normalize (TopCat.of (P × (ClosedInterval × Q))) n
        (cochainPullback (timeProjection (P := P) (Q := Q) ≫ evaluation α β) n
          (DiagonalAvoidanceCocycle.ambientCocycle n hn hρ)) :=
    SingularNormalization.normalize_natural _ n _
  rw [he]
  exact SingularNormalization.normalize_degeneracies _ n _

theorem cocycle_far_zero (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q))
      (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
        (fun x => basepoint (α x)) (fun y => basepoint (β y)) ρ)) n
      (cocycle α β hn hρ) = 0 := by
  rw [cocycle, ← pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ
  intro z
  change ρ ≤ ‖basepoint (β z.val.2) - basepoint (α z.val.1)‖
  have hz := z.property
  change ρ ≤ dist (basepoint (α z.val.1)) (basepoint (β z.val.2)) at hz
  simpa only [dist_eq_norm, norm_sub_rev] using hz

theorem timeCocycle_far_zero (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
      (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
        (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρ)) n
      (timeCocycle α β hn hρ) = 0 :=
  pullback_support (timeProjection (P := P) (Q := Q))
    (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρ)
    (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
      (fun x => basepoint (α x)) (fun y => basepoint (β y)) ρ)
    (fun _ hz => hz) n (cocycle α β hn hρ) (cocycle_far_zero α β hn hρ)

theorem cocycle_class (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (cochainCxZMod2 (TopCat.of (P × Q))) n
      (cocycle α β hn hρ) (cocycle_closed α β hn hρ) =
      (cohPullback (evaluation α β) n).hom (DiagonalCohomology.ambientClass n hn) := by
  rw [← NormalizedDiagonalCocycle.ambient_class n hn hρ]
  exact (CochainClass.classOf_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (evaluation α β).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)
    (cocycle_closed α β hn hρ)).symm

theorem timeCocycle_class (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (cochainCxZMod2 (TopCat.of (P × (ClosedInterval × Q)))) n
      (timeCocycle α β hn hρ) (timeCocycle_closed α β hn hρ) =
      (cohPullback (timeProjection (P := P) (Q := Q) ≫ evaluation α β) n).hom
        (DiagonalCohomology.ambientClass n hn) := by
  have hz := timeCocycle_closed α β hn hρ
  rw [timeCocycle_pullback] at hz
  rw [← NormalizedDiagonalCocycle.ambient_class n hn hρ]
  refine (CochainClass.classOf_congr
    (cochainCxZMod2 (TopCat.of (P × (ClosedInterval × Q)))) n
    (timeCocycle_pullback α β hn hρ) (timeCocycle_closed α β hn hρ) hz).trans ?_
  exact (CochainClass.classOf_map (cochainCxZMod2 (DiagonalCohomology.product n))
    (singularCochainComplexZMod2.map (timeProjection (P := P) (Q := Q) ≫ evaluation α β).op) n
    (NormalizedDiagonalCocycle.ambient n hn hρ) (NormalizedDiagonalCocycle.ambient_closed n hn hρ)
    hz).symm

end
end Finsler.CompactJoinCocycle
