module

public import Finsler.Topology.RevLabel
public import Finsler.Geometry.AmbientRotation

/-! obtain reversal invariance of polygon index and nullity
from the existing ambient penalized Hessian comparison.  -/

@[expose] public section

namespace Finsler.PolygonReverseIndex

open Module QuadraticMap Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonHessian
open Finsler.PolygonDescent Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.AmbientHessian
open Finsler.AmbientNormalNondeg Finsler.AmbientNullity Finsler.AmbientRotation Finsler.PolygonDescentK
open Finsler.RevLabel Finsler.MilnorEquivariance
open scoped ContDiff
noncomputable section
set_option maxSynthPendingDepth 3

variable {n N : ℕ} [NeZero N]

def revE : (ZMod N → Ambient n) ≃ₗ[ℝ] (ZMod N → Ambient n) where
  toFun := revA N
  invFun := revA N
  left_inv := revA_revA N
  right_inv := revA_revA N
  map_add' := map_add _
  map_smul' := map_smul _

omit [NeZero N] in
theorem short_reverse {δ : ℝ} {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    ShortPolygon δ (reversePolygon q) := by
  intro i
  have he : -(i + 1) + 1 = -i := by abel
  have h := hq (-(i + 1))
  rw [he] at h
  change ‖(q (-(i + 1)) : Ambient n) - q (-i)‖ < δ
  rw [norm_sub_rev]
  exact h

omit [NeZero N] in
theorem reverse_ne {q : ZMod N → Sphere n} (hne : ∀ i, q (i + 1) ≠ q i) (i : ZMod N) :
    reversePolygon q (i + 1) ≠ reversePolygon q i := by
  have he : -(i + 1) + 1 = -i := by abel
  have h := hne (-(i + 1))
  rw [he] at h
  exact h.symm

theorem polyCritical_reverse (F : ReversibleMetric n) {q : ZMod N → Sphere n}
    (hc : PolyCritical F N q) : PolyCritical F N (reversePolygon q) := by
  intro c c' hc0 hcn hcd
  have hc0' : (fun t : ℝ => revA N (c t)) 0 = amb q := by
    change revA N (c 0) = amb q
    rw [hc0]
    change revA N (amb (reversePolygon q)) = amb q
    rw [amb_reversePolygon, revA_revA]
  have hcn' : ∀ t i, ‖(fun t : ℝ => revA N (c t)) t i‖ = 1 := fun t i => hcn t (-i)
  have hcd' := (revA (n := n) N).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcd
  have h := hc _ _ hc0' hcn' hcd'
  have he : (fun t => polyEnergy F N (c t)) = fun t => polyEnergy F N (revA N (c t)) := by
    funext t
    have h1 := pen_revA F 0 (c t)
    rw [pen_zero] at h1
    rw [← polyEnergyN_eq F N (hcn t), ← h1]
    exact polyEnergyN_eq F N (hcn' t)
  rw [he]
  exact h

theorem sndDeriv_pen_rev (F : ReversibleMetric n) (lam : ℝ)
    {Q : ZMod N → Ambient n} (hf : ContDiffAt ℝ 2 (pen F N lam) (revA N Q))
    (v w : ZMod N → Ambient n) :
    fderiv ℝ (fderiv ℝ (pen F N lam)) (revA N Q) (revA N v) (revA N w) =
      fderiv ℝ (fderiv ℝ (pen F N lam)) Q v w := by
  have h := Finsler.AmbientNormalIndex.sndDeriv_comp_linear (revA (n := n) N) hf v w
  have he : pen F N lam ∘ revA (n := n) N = pen F N lam := funext fun x => pen_revA F lam x
  rw [he] at h
  exact h.symm

theorem sigNeg_sndQuad_rev (F : ReversibleMetric n) (lam : ℝ)
    {Q : ZMod N → Ambient n} (hf : ContDiffAt ℝ 2 (pen F N lam) (revA N Q)) :
    sigNeg (sndQuad (pen F N lam) (revA N Q)) = sigNeg (sndQuad (pen F N lam) Q) := by
  have he : QuadraticMap.Equivalent (sndQuad (pen F N lam) Q)
      (sndQuad (pen F N lam) (revA N Q)) :=
    ⟨⟨revE, fun v => sndDeriv_pen_rev F lam hf v v⟩⟩
  exact he.sigNeg_eq.symm

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
  (hc : PolyCritical F N q)

include hδ hq hne hc

theorem index_reverse (hs : (hessian F q).toLinearMap.IsSymmetric)
    (hs' : (hessian F (reversePolygon q)).toLinearMap.IsSymmetric) :
    index F (reversePolygon q) hs' = index F q hs := by
  rw [← sigNeg_sndQuad_pen F hδ (short_reverse hq) (reverse_ne hne)
      (polyCritical_reverse F hc) (lam := 1) zero_le_one hs',
    ← sigNeg_sndQuad_pen F hδ hq hne hc (lam := 1) zero_le_one hs, amb_reversePolygon]
  exact sigNeg_sndQuad_rev F 1 (by
    rw [← amb_reversePolygon]
    exact pen_contDiffAt_two F hδ (short_reverse hq) (reverse_ne hne) 1)

theorem nullity_reverse : nullity F (reversePolygon q) = nullity F q := by
  rw [← finrank_ker_sndDeriv_pen F hδ (short_reverse hq) (reverse_ne hne)
      (polyCritical_reverse F hc) one_pos,
    ← finrank_ker_sndDeriv_pen F hδ hq hne hc one_pos]
  refine finrank_ker_congr revE fun v w => ?_
  rw [amb_reversePolygon]
  exact sndDeriv_pen_rev F 1 (by
    rw [← amb_reversePolygon]
    exact pen_contDiffAt_two F hδ (short_reverse hq) (reverse_ne hne) 1) v w

end

end Finsler.PolygonReverseIndex
