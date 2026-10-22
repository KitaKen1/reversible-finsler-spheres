module

public import Finsler.Topology.SingularNormalization
public import Finsler.Topology.FarThomRepresentative
public import Finsler.Topology.SelfCutThomCocycle

/-! An actual normalized diagonal Thom cocycle vanishing on both far set
and diagonal. It has the specified class in the actual far-relative group. -/

@[expose] public section
namespace Finsler.NormalizedDiagonalCocycle

open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalCohomology Finsler.DiagonalAvoidanceCocycle
open Finsler.FarDiagonalCohomology
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def ambient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    singularCochainGroup (ZMod 2) (product n) n :=
  SingularNormalization.normalize (product n) n (ambientCocycle n hn hρ)

theorem ambient_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainCoboundary (ZMod 2) (product n) n (ambient n hn hρ) = 0 :=
  SingularNormalization.normalize_closed _ n _ (DiagonalAvoidanceCocycle.ambient_closed n hn hρ)

theorem ambient_normalized (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (product n))
      (ambient n hn hρ) := SingularNormalization.normalize_degeneracies _ n _

theorem avoidance_supported (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (inclusion n ρ) n (ambient n hn hρ) = 0 :=
  SingularNormalization.normalize_supported _ n _ (ambient_supported n hn hρ)

theorem far_supported (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (farPair n ρ).map n (ambient n hn hρ) = 0 := by
  apply SingularNormalization.normalize_supported
  have h := RelativeCupCochain.restriction_toAmbient (farPair n ρ) n
    (FarThomRepresentative.endpointVanishing n hn hρ)
  rw [FarThomRepresentative.endpointVanishing_toAmbient] at h
  exact h

theorem ambient_class (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    CochainClass.classOf (cochainCxZMod2 (product n)) n (ambient n hn hρ)
      (ambient_closed n hn hρ) = ambientClass n hn :=
  (SingularNormalization.normalize_class_pos (product n) n hn (ambientCocycle n hn hρ)
    (DiagonalAvoidanceCocycle.ambient_closed n hn hρ)).trans (ambient_cocycle_class n hn hρ)

def relativeCocycle (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.relative (farPair n ρ) n :=
  (RelativeCupCochain.exists_lift (farPair n ρ) n (ambient n hn hρ)
    (far_supported n hn hρ)).choose

theorem relative_toAmbient (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.toAmbient (farPair n ρ) n (relativeCocycle n hn hρ) = ambient n hn hρ :=
  (RelativeCupCochain.exists_lift (farPair n ρ) n (ambient n hn hρ)
    (far_supported n hn hρ)).choose_spec

theorem relative_closed (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    RelativeCupCochain.differential (farPair n ρ) n (relativeCocycle n hn hρ) = 0 := by
  apply RelativeCupCochain.toAmbient_injective (farPair n ρ) (n + 1)
  rw [RelativeCupCochain.toAmbient_differential, relative_toAmbient, map_zero]
  exact ambient_closed n hn hρ

def relativeClass (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (farPair n ρ).singularCohomology coeff (ZMod 2) coeff n :=
  CochainClass.classOf (RelativeCup.cx (farPair n ρ)) n (relativeCocycle n hn hρ)
    (relative_closed n hn hρ)

theorem relativeClass_image (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) :
    (relativeToPool (farPair n ρ) n).hom (relativeClass n hn hρ) = ambientClass n hn := by
  have he := RelativeCup.relativeToPool_classOf (farPair n ρ) n (relativeCocycle n hn hρ)
    (relative_closed n hn hρ)
  calc
    _ = CochainClass.classOf (cochainCxZMod2 (product n)) n
        (RelativeCupCochain.toAmbient (farPair n ρ) n (relativeCocycle n hn hρ))
        (RelativeCup.toAmbient_closed (farPair n ρ) n (relativeCocycle n hn hρ)
          (relative_closed n hn hρ)) := he
    _ = CochainClass.classOf (cochainCxZMod2 (product n)) n (ambient n hn hρ)
        (ambient_closed n hn hρ) := CochainClass.classOf_congr _ n
          (relative_toAmbient n hn hρ) _ _
    _ = _ := ambient_class n hn hρ

theorem relativeClass_specified (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2) :
    relativeClass n (by omega) hρ = thomClass n (by omega) hρ := by
  apply relativeToPool_injective n hn hρ hρ2
  exact (relativeClass_image n (by omega) hρ).trans (thomClass_image n (by omega) hρ).symm

theorem pullback_zero_of_diagonal {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    {X : TopCat.{0}} (f : X ⟶ product n) (hf : ∀ x, (f x).1 = (f x).2) :
    cochainPullback f n (ambient n hn hρ) = 0 :=
  SingularNormalization.normalize_supported f n _
    (SelfCutThomCocycle.pullback_zero_of_diagonal hn hρ f hf)

theorem pullback_zero_of_far {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ)
    {X : TopCat.{0}} (f : X ⟶ product n)
    (hf : ∀ x, ρ ≤ ‖((f x).2 : Ambient n) - (f x).1‖) :
    cochainPullback f n (ambient n hn hρ) = 0 :=
  SingularNormalization.normalize_supported f n _
    (SelfCutThomCocycle.pullback_zero_of_far hn hρ f hf)

end
end Finsler.NormalizedDiagonalCocycle
