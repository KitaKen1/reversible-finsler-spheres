module

public import Finsler.Geometry.PolygonReverseIndex
public import Finsler.Topology.CircleRoot

/-! positive-iterate indices and actual nullities are independent
of geodesic orientation. The chosen periods and index at zero are not identified. -/

@[expose] public section

namespace Finsler.GeodesicReverseData

open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.PolygonDescent
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonSmooth Finsler.PolygonHessian
open Finsler.PolygonIterateReduction Finsler.PolygonIterate Finsler.PolygonCritical Finsler.SmoothSobolev Finsler.SobolevReverse
open Finsler.MilnorEquivariance Finsler.GeodesicIteration Finsler.GeodesicFrames
open Finsler.AmbientRotation Finsler.PolygonReverseIndex Finsler.CircleRoot
open scoped ContDiff
noncomputable section
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 600000

variable {n : ℕ} {F : ReversibleMetric n}

theorem reverse_iterate (m N : ℕ) [NeZero m] (q : ZMod N → Sphere n) :
    reversePolygon (iterate m N q) = iterate m N (reversePolygon q) := by
  funext i
  change q (red m N (-i)) = q (-(red m N i))
  rw [map_neg]

theorem sample_reverse_geodesic (g : ClosedGeodesic F) (N : ℕ) [NeZero N] :
    samplePoly N (ofSmooth (reverseGeodesic g).loop) = reversePolygon (samplePoly N (ofSmooth g.loop)) := by
  change samplePoly N (ofSmooth (Finsler.Loops.reverse g.loop)) = _
  rw [← reverseSphere_ofSmooth, samplePoly_reverse]

theorem iteration_reverse (g : ClosedGeodesic F) (m : ℕ) [NeZero m] :
    (iterData (reverseGeodesic g)).I m = (iterData g).I m ∧
      (iterData (reverseGeodesic g)).ν (Nat.gcd m (iterData (reverseGeodesic g)).L) =
        (iterData g).ν (Nat.gcd m (iterData g).L) := by
  obtain ⟨δ, hδpos, hδ⟩ := Finsler.EnergySphereSmooth.exists_ambientMinEnergy_contDiffAt F
  obtain ⟨Ng, hg⟩ := (iterData g).data δ hδpos
  obtain ⟨Nr, hr⟩ := (iterData (reverseGeodesic g)).data δ hδpos
  let N := Ng + Nr + 1
  have : NeZero N := ⟨by dsimp [N]; omega⟩
  have hg₀ := hg N (by dsimp [N]; omega) 0
  have hr₀ := hr N (by dsimp [N]; omega) 0
  let q := iterate m (2 * N) (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop 0)))
  let qr := iterate m (2 * N)
    (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift (reverseGeodesic g).loop 0)))
  have hqr : qr = reversePolygon q := by
    dsimp only [q, qr]
    rw [Finsler.GeodesicIteration.shift_zero, Finsler.GeodesicIteration.shift_zero,
      sample_reverse_geodesic, reverse_iterate]
  have hq : ShortPolygon δ q := shortPolygon_iterate m (2 * N) hg₀.1
  have hne : ∀ i, q (i + 1) ≠ q i := iterate_ne m (2 * N) hg₀.2.1
  have hc : PolyCritical F (m * (2 * N)) q := polyCritical_iterate m F hδ hg₀.1 hg₀.2.1 hg₀.2.2.1
  have hs := hessian_isSymmetric F hδ hq hne
  have hsr := hessian_isSymmetric F hδ (shortPolygon_iterate m (2 * N) hr₀.1)
    (iterate_ne m (2 * N) hr₀.2.1)
  have hi := (hg₀.2.2.2.1 m).2 hs
  have hir := (hr₀.2.2.2.1 m).2 hsr
  have hν := (hg₀.2.2.2.1 m).1
  have hνr := (hr₀.2.2.2.1 m).1
  change index F qr hsr = _ at hir
  change nullity F qr = _ at hνr
  rw [hqr] at hνr
  let hsRev := hessian_isSymmetric F hδ (short_reverse hq) (reverse_ne hne)
  have hpair : (⟨qr, hsr⟩ : {p : ZMod (m * (2 * N)) → Sphere n //
      (hessian F p).toLinearMap.IsSymmetric}) = ⟨reversePolygon q, hsRev⟩ := Subtype.ext hqr
  have hiEq := congrArg (fun p : {p : ZMod (m * (2 * N)) → Sphere n //
      (hessian F p).toLinearMap.IsSymmetric} => index F p.1 p.2) hpair
  have hir' := hiEq.symm.trans hir
  constructor
  · have he := index_reverse F hδ hq hne hc hs hsRev
    rw [hir', hi] at he
    exact he
  · have he := nullity_reverse F hδ hq hne hc
    rw [hνr, hν] at he
    exact he

theorem label_index (s : Set (Sphere n)) (hs : s ∈ Finsler.Geodesics.primeImages F)
    (o : Bool) (m : ℕ) [NeZero m] :
    (iterData (labelGeod F (s, o) hs)).I m = (iterData (Finsler.CriticalLevels.chosen F s hs)).I m := by
  cases o
  · exact (iteration_reverse _ m).1
  · rfl


theorem label_nullity (s : Set (Sphere n)) (hs : s ∈ Finsler.Geodesics.primeImages F)
    (o : Bool) (m : ℕ) [NeZero m] :
    (iterData (labelGeod F (s, o) hs)).ν (Nat.gcd m (iterData (labelGeod F (s, o) hs)).L) =
      (iterData (Finsler.CriticalLevels.chosen F s hs)).ν
        (Nat.gcd m (iterData (Finsler.CriticalLevels.chosen F s hs)).L) := by
  cases o
  · exact (iteration_reverse _ m).2
  · rfl

end

end Finsler.GeodesicReverseData
