module

public import Finsler.Loop.CanonicalTimeCupFilteredPairing
public import Finsler.Topology.NormalizedRelativeRepresentative
public import Finsler.Loop.LengthFilteredLoopRotation

/-! Genuine strict-length support addition for the EXISTING geometric
GH/time-cup product. Actual vanishing of both input classes below L
and M forces their actual product to vanish below any R<L+M.
Use the actual filtered cut and arbitrary small positive epsilon;
no GH filtration axiom is supplied. -/
@[expose] public section
namespace Finsler.CanonicalGHLengthSupport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem restriction_zero_mono {n : ℕ} (F : ReversibleMetric n) (p : ℕ)
    (a : cohomologyZMod2 (Loops n) p) {b c : ℝ} (hbc : b ≤ c)
    (hc : (cohPullback (LengthFilteredLoopRotation.full F c) p).hom a = 0) :
    (cohPullback (LengthFilteredLoopRotation.full F b) p).hom a = 0 := by
  have hmap : LengthFilteredLoopRotation.cut F hbc ≫ LengthFilteredLoopRotation.full F c =
      LengthFilteredLoopRotation.full F b := by ext u : 1; rfl
  calc
    _ = (cohPullback (LengthFilteredLoopRotation.cut F hbc) p).hom
        ((cohPullback (LengthFilteredLoopRotation.full F c) p).hom a) := by
      rw [← Cup.pullback_comp, hmap]
    _ = 0 := by rw [hc, map_zero]

theorem product_restriction_zero {m : ℕ} (hm : 1 ≤ m) (F : ReversibleMetric (m + 1))
    (p q : ℕ) (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q) {L M R : ℝ}
    (ha : (cohPullback (LengthFilteredLoopRotation.full F L) p).hom a = 0)
    (hb : (cohPullback (LengthFilteredLoopRotation.full F M) q).hom b = 0)
    (hR : R < L + M) :
    (cohPullback (LengthFilteredLoopRotation.full F R) ((m + p) + q)).hom
      (CanonicalGlobalTimeCup.product m p q a b) = 0 := by
  let ε := (L + M - R) / 6
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hout : R - L + 3 * ε ≤ M := by dsimp [ε]; linarith
  let T := NormalizedRelativeRepresentative.raw (Loops (m + 1)) (SelfCutOscillation.short F L) p a ha
  have hT := NormalizedRelativeRepresentative.raw_closed (Loops (m + 1))
    (SelfCutOscillation.short F L) p a ha
  have hs := NormalizedRelativeRepresentative.raw_supported (Loops (m + 1))
    (SelfCutOscillation.short F L) p a ha
  have hc : cocycleClass (Loops (m + 1)) p T hT = a :=
    NormalizedRelativeRepresentative.raw_class (Loops (m + 1)) (SelfCutOscillation.short F L) p a ha
  have hb' := restriction_zero_mono F q b hout hb
  apply (kroneckerMap_bijective (lengthSpace F R) ((m + p) + q)).1
  apply LinearMap.ext
  intro z
  simp only [map_zero, LinearMap.zero_apply]
  have hp := CanonicalTimeCupFilteredPairing.pairing m hm p F hε T hT hs q
    (classRepr _ q b) (classRepr_isCocycle _ q b) z
  rw [hc, cocycleClass_classRepr] at hp
  let w := ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hs (a := R)).homology q).hom z
  have hn := congrArg (fun φ : homologyDualZMod2 (lengthSpace F (R - L + 3 * ε)) q => φ w)
    (kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F (R - L + 3 * ε)) q b)
  change (kroneckerMap (lengthSpace F (R - L + 3 * ε)) q).hom
      ((cohPullback (LengthFilteredLoopRotation.full F (R - L + 3 * ε)) q).hom b) w =
    (kroneckerMap (Loops (m + 1)) q).hom b
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (R - L + 3 * ε)) q).hom w) at hn
  rw [hb', map_zero, LinearMap.zero_apply] at hn
  exact hp.trans hn.symm

end
end Finsler.CanonicalGHLengthSupport
