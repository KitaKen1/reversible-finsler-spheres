module

public import Finsler.Loop.OrthogonalSphereEscape
public import Finsler.Topology.CochainClassExact
public import Finsler.Topology.RelativeCupCochain

/-! The real orthogonal escape gives a TRUE relative null pullback
of the original normalized far-relative Thom class. Construct the
actual pair homotopy, prove the escaped relative cocycle literally
zero, and obtain a genuine relative cochain primitive. No absolute
cohomology vanishing is substituted for this relative conclusion. -/
@[expose] public section
namespace Finsler.OrthogonalRelativeThomZero
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelEvaluation Finsler.CochainComparison
open Finsler.OrthogonalSphereEscape
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {n : ℕ} {X : TopCat.{0}} (f g w : X ⟶ sphere n)
  (hgw : ∀ x, ⟪(g x : Ambient n), (w x : Ambient n)⟫ = 0)
  (hfw : ∀ x, ⟪(f x : Ambient n), (w x : Ambient n)⟫ = 0)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)

def exterior : Set X := {x | ρ ≤ ‖(g x : Ambient n) - f x‖}
abbrev source : TopPair.{0} := TopPair.ofSubset (exterior f g (ρ := ρ))

def pairMap : source f g (ρ := ρ) ⟶ FarDiagonalCohomology.farPair n ρ :=
  TopPair.ofSubsetMap (B := exterior f g (ρ := ρ)) (B' := DiagonalAvoidanceCocycle.far n ρ)
    (OrthogonalSphereEscape.pair f g) (fun _ hx => hx)

include hfw hρ1 in
theorem escaped_far (x : X) : OrthogonalSphereEscape.escaped f w x ∈ DiagonalAvoidanceCocycle.far n ρ :=
  OrthogonalSphereEscape.orthogonal_far (f x) (w x) (hfw x) hρ1

def escapedPair : source f g (ρ := ρ) ⟶ FarDiagonalCohomology.farPair n ρ :=
  TopPair.ofSubsetMap (B := exterior f g (ρ := ρ)) (B' := DiagonalAvoidanceCocycle.far n ρ)
    (OrthogonalSphereEscape.escaped f w) (fun x _ => escaped_far f w hfw hρ1 x)

include hfw hρ hρ1 in
theorem homotopy_faces (s : ClosedInterval) (x : X) (hx : x ∈ exterior f g (ρ := ρ)) :
    (OrthogonalSphereEscape.homotopy f g w hgw) (s, x) ∈ DiagonalAvoidanceCocycle.far n ρ :=
  OrthogonalSphereEscape.homotopy_far f g w hgw hfw hρ.le hρ1 s x hx

def pairHomotopy : TopPair.Homotopy (pairMap f g (ρ := ρ)) (escapedPair f g w hfw hρ1) :=
  TopPair.ofSubsetHomotopy (OrthogonalSphereEscape.homotopy f g w hgw)
    (homotopy_faces f g w hgw hfw hρ hρ1)

theorem escaped_fst : TopPair.Hom.fst (escapedPair f g w hfw hρ1) = OrthogonalSphereEscape.escaped f w := by
  apply TopCat.ext
  intro x
  exact TopPair.ofSubsetMap_fst_apply (B := exterior f g (ρ := ρ))
    (B' := DiagonalAvoidanceCocycle.far n ρ) (OrthogonalSphereEscape.escaped f w)
    (fun x _ => escaped_far f w hfw hρ1 x) x

theorem escaped_cochain_zero (hn : 1 ≤ n) :
    RelativeCupCochain.pullback (escapedPair f g w hfw hρ1) n
      (NormalizedDiagonalCocycle.relativeCocycle n hn hρ) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (source f g (ρ := ρ)) n
  rw [RelativeCupCochain.toAmbient_pullback, NormalizedDiagonalCocycle.relative_toAmbient,
    escaped_fst, map_zero]
  exact NormalizedDiagonalCocycle.pullback_zero_of_far hn hρ (OrthogonalSphereEscape.escaped f w)
    (fun x => escaped_far f w hfw hρ1 x)

theorem escaped_class_zero (hn : 1 ≤ n) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (escapedPair f g w hfw hρ1) n).hom (NormalizedDiagonalCocycle.relativeClass n hn hρ) = 0 := by
  have hc := CochainClass.classOf_map (RelativeCup.cx (FarDiagonalCohomology.farPair n ρ))
    (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (escapedPair f g w hfw hρ1))
    n (NormalizedDiagonalCocycle.relativeCocycle n hn hρ) (NormalizedDiagonalCocycle.relative_closed n hn hρ)
    (CochainClass.closed_map (RelativeCup.cx (FarDiagonalCohomology.farPair n ρ))
      (TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) (escapedPair f g w hfw hρ1))
      n (NormalizedDiagonalCocycle.relativeCocycle n hn hρ) (NormalizedDiagonalCocycle.relative_closed n hn hρ))
  have he := escaped_cochain_zero f g w hfw hρ hρ1 hn
  exact hc.trans ((CochainClass.classOf_congr (RelativeCup.cx (source f g (ρ := ρ))) n he _ _).trans
    (CochainClass.classOf_zero (RelativeCup.cx (source f g (ρ := ρ))) n (map_zero _)))

include w hgw hfw hρ1 in
theorem thom_pullback_zero (hn : 1 ≤ n) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff)
      (pairMap f g (ρ := ρ)) n).hom (NormalizedDiagonalCocycle.relativeClass n hn hρ) = 0 := by
  have he := (pairHomotopy f g w hgw hfw hρ hρ1).congr_singularCohomologyMap coeff (ZMod 2) coeff n
  exact (ConcreteCategory.congr_hom he (NormalizedDiagonalCocycle.relativeClass n hn hρ)).trans
    (escaped_class_zero f g w hfw hρ hρ1 hn)

end
end Finsler.OrthogonalRelativeThomZero
