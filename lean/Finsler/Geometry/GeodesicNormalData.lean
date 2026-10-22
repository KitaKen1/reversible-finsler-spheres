module

public import Finsler.Geometry.CircleFrameField

/-! The actual sampled normal Hessians have fixed negative and positive indices. This exposes
both frame families and their nondegeneracy without choosing a closing holonomy. -/

@[expose] public section

namespace Finsler.GeodesicNormalData

open Module QuadraticForm QuadraticMap Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonHessian Finsler.PolygonDescent
open Finsler.PolygonLoop
open Finsler.PolygonIterate Finsler.AmbientSymmetry Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.AmbientRotation Finsler.PolygonIterateReduction
open Finsler.NormalFamily Finsler.GeodesicFrames Finsler.CircleFrameField
open Finsler.FramePath Finsler.FrameIndex Finsler.FormSemicontinuity
open scoped ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {F : ReversibleMetric n}

/-- The two maximal definite families and nondegenerate normal forms along the actual circle.
The gcd condition identifies the nullities; no parity condition or prime assumption is needed. -/
theorem exists_normal_families (g : Finsler.Geodesics.ClosedGeodesic F) (s m : ℕ)
    [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      (∀ a, amb (rootFamily g s N a) ∈ smoothSet m (s * (2 * N)) F) ∧
      Family (formB m (s * (2 * N)) F (rootFamily g s N))
        ((iterData g).I (s * m) - (iterData g).I s) ∧
      Family (fun a => -formB m (s * (2 * N)) F (rootFamily g s N) a)
        (finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
          ((iterData g).I (s * m) - (iterData g).I s)) ∧
      ∀ a, LinearMap.ker (formB m (s * (2 * N)) F (rootFamily g s N) a) = ⊥ := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_ambientMinEnergy_contDiffAt F
  obtain ⟨N₀, hN₀⟩ := (iterData g).data δ hδpos
  refine ⟨N₀, fun N hN _ => ?_⟩
  have hfacts : ∀ a : ℝ, SampleData g (iterData g).I (iterData g).ν (iterData g).L δ N a :=
    fun a => hN₀ N hN a
  have hq : ∀ a : ℝ, ShortPolygon δ (rootFamily g s N a) := fun a =>
    shortPolygon_iterate s (2 * N) (hfacts a).1
  have hne : ∀ (a : ℝ) i, rootFamily g s N a (i + 1) ≠ rootFamily g s N a i := fun a =>
    iterate_ne s (2 * N) (hfacts a).2.1
  have hc : ∀ a : ℝ, PolyCritical F (s * (2 * N)) (rootFamily g s N a) := fun a =>
    polyCritical_iterate s F hδ (hfacts a).1 (hfacts a).2.1 (hfacts a).2.2.1
  have hnull : ∀ a : ℝ, nullity F (iterate m (s * (2 * N)) (rootFamily g s N a)) =
      nullity F (rootFamily g s N a) := fun a => by
    have h1 := ((hfacts a).2.2.2.2 s m).1
    have h2 := ((hfacts a).2.2.2.1 s).1
    unfold rootFamily
    rw [h1, h2, hgcd]
  have hidx0 : ∀ (a : ℝ)
      (hs : (hessian F (iterate m (s * (2 * N)) (rootFamily g s N a))).toLinearMap.IsSymmetric)
      (hs₀ : (hessian F (rootFamily g s N a)).toLinearMap.IsSymmetric),
      index F (iterate m (s * (2 * N)) (rootFamily g s N a)) hs = (iterData g).I (s * m) ∧
        index F (rootFamily g s N a) hs₀ = (iterData g).I s := fun a hs hs₀ =>
    ⟨((hfacts a).2.2.2.2 s m).2 hs, ((hfacts a).2.2.2.1 s).2 hs₀⟩
  have hle : (iterData g).I s ≤ (iterData g).I (s * m) := by
    have hs := hessian_isSymmetric F hδ (shortPolygon_iterate m (s * (2 * N)) (hq 0))
      (iterate_ne m (s * (2 * N)) (hne 0))
    have hs₀ := hessian_isSymmetric F hδ (hq 0) (hne 0)
    have h := index_iterate_eq_add m (s * (2 * N)) F hδ
      (shortPolygon_iterate m (s * (2 * N)) (hq 0)) (iterate_ne m (s * (2 * N)) (hne 0)) (hq 0)
      (hne 0) (polyCritical_iterate m F hδ (hq 0) (hne 0) (hc 0)) (hc 0) zero_le_one hs hs₀
    rw [(hidx0 0 hs hs₀).1, (hidx0 0 hs hs₀).2] at h
    omega
  have hidx : ∀ (a : ℝ)
      (hs : (hessian F (iterate m (s * (2 * N)) (rootFamily g s N a))).toLinearMap.IsSymmetric)
      (hs₀ : (hessian F (rootFamily g s N a)).toLinearMap.IsSymmetric),
      index F (iterate m (s * (2 * N)) (rootFamily g s N a)) hs =
        index F (rootFamily g s N a) hs₀ +
          ((iterData g).I (s * m) - (iterData g).I s) := fun a hs hs₀ => by
    rw [(hidx0 a hs hs₀).1, (hidx0 a hs hs₀).2]
    omega
  have hB := formB_continuous m (s * (2 * N)) F hδ (rootFamily_continuous g s N) hq hne
  have hsym := formB_symm m (s * (2 * N)) F hδ hq hne
  have hb := sigNeg_formB m (s * (2 * N)) F hδ hq hne hc hidx
  have hk := ker_formB m (s * (2 * N)) F hδ hq hne hc hnull
  have hb' : ∀ a, sigNeg (LinearMap.BilinMap.toQuadraticMap
      (-formB m (s * (2 * N)) F (rootFamily g s N) a)) =
        finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
          ((iterData g).I (s * m) - (iterData g).I s) := by
    intro a
    have h := sigPos_add_sigNeg_add_ker (hsym a)
    rw [hk a, finrank_bot, add_zero, hb a] at h
    rw [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg]
    omega
  refine ⟨?_, family_of_sigNeg hB hsym hb,
    family_of_sigNeg hB.neg (fun a v w => by
      change -(formB m (s * (2 * N)) F (rootFamily g s N) a v w) =
        -(formB m (s * (2 * N)) F (rootFamily g s N) a w v)
      rw [hsym a v w]) hb', hk⟩
  intro a
  exact pen_contDiffAt_three F hδ (shortPolygon_iterate m (s * (2 * N)) (hq a))
    (iterate_ne m (s * (2 * N)) (hne a)) 1

end

end Finsler.GeodesicNormalData
