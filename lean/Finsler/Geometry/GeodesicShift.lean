module

public import Finsler.Geometry.GeodesicArcs

/-! Rotations of closed geodesics. The rotation of a regular smooth loop is regular, and the
rotation of a stationary loop is stationary: a variation of the rotated loop is the rotation of
a variation of the loop, and the energy is invariant under rotation. Hence the rotations of a
closed geodesic are closed geodesics. An arc of the rotated loop is an arc of the loop, so the
rotations of a loop by all phases in [0, 1] have a common scale below which all arcs starting in
[0, 1] are good for a segment package. -/

@[expose] public section

namespace Finsler.GeodesicShift

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics Finsler.GeodesicArcs
open Finsler.SphereCoordinateEuler Finsler.SegmentAtlas
open TauCeti.Manifold Function Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

variable {n : ℕ}

/-- Rotating back gives the loop. -/
theorem shift_shift_neg (γ : SmoothLoop n) (a : ℝ) : shift (shift γ a) (-a) = γ := by
  apply loop_ext
  intro t
  change γ (t + -a + a) = γ t
  rw [neg_add_cancel_right]

/-- The rotation of a regular loop is regular. -/
theorem regular_shift {γ : SmoothLoop n} (hγ : Regular γ) (a : ℝ) : Regular (shift γ a) := by
  intro t
  have hvel := curveVelocity_comp (I := 𝓡 n) ((hasDerivAt_id t).add_const a)
    (γ.smooth.mdifferentiableAt (by simp))
  have he : curveVelocity (𝓡 n) (shift γ a) t = curveVelocity (𝓡 n) γ (t + a) := by
    simpa [shift, comp_def] using hvel
  rw [he]
  exact hγ (t + a)

/-- The rotation of a variation. -/
def shiftVariation (V : SmoothVariation n) (a : ℝ) : SmoothVariation n where
  family := fun p => V.family (p.1, p.2 + a)
  smooth := V.smooth.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contMDiff
  periodic := by
    intro s t
    change V.family (s, t + 1 + a) = V.family (s, t + a)
    rw [add_right_comm]
    exact V.periodic s (t + a)

theorem loopAt_shiftVariation (V : SmoothVariation n) (a s : ℝ) :
    loopAt (shiftVariation V a) s = shift (loopAt V s) a := by
  apply loop_ext
  intro t
  rfl

/-- The rotation of a stationary loop is stationary. -/
theorem stationary_shift {F : ReversibleMetric n} {γ : SmoothLoop n} (hγ : Stationary F γ)
    (a : ℝ) : Stationary F (shift γ a) := by
  intro V hV
  have hbase : loopAt (shiftVariation V (-a)) 0 = γ := by
    rw [loopAt_shiftVariation, hV, shift_shift_neg]
  have h := hγ (shiftVariation V (-a)) hbase
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
    change Finsler.LoopEnergy.energy F (loopAt V s) =
      Finsler.LoopEnergy.energy F (loopAt (shiftVariation V (-a)) s)
    rw [loopAt_shiftVariation, Finsler.LoopEnergy.energy_shift])

/-- The rotation of a closed geodesic. -/
def shiftGeodesic {F : ReversibleMetric n} (g : ClosedGeodesic F) (a : ℝ) : ClosedGeodesic F where
  loop := shift g.loop a
  regular := regular_shift g.regular a
  stationary := stationary_shift g.stationary a

theorem shiftGeodesic_loop {F : ReversibleMetric n} (g : ClosedGeodesic F) (a : ℝ) :
    (shiftGeodesic g a).loop = shift g.loop a := rfl

variable {F : ReversibleMetric n}

/-- A good arc of the loop is a good arc of the rotated loop. -/
theorem arcGood_shift {γ : SmoothLoop n} {S : SegChart F} {a t h : ℝ}
    (hg : ArcGood γ S (t + a) h) : ArcGood (shift γ a) S t h := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  refine ⟨h1, ?_, fun s hs => ?_, ?_⟩
  · change ‖(γ (t + h + a) : Ambient n) - γ (t + a)‖ < S.δ
    rw [add_right_comm]
    exact h2
  · change γ (t + s * h + a) ∈ _
    rw [add_right_comm]
    exact h3 s hs
  · have hc : coordinateCurve S.p (shift γ a) = fun x => coordinateCurve S.p γ (x + a) := rfl
    rw [hc, deriv_comp_add_const]
    exact h4

/-- A uniform scale below which all arcs starting in a compact interval are good. -/
theorem exists_arc_scale_Icc (γ : SmoothLoop n) {A B : ℝ} (hAB : A ≤ B) :
    ∃ h₀ > 0, ∀ a ∈ Icc A B, ∀ h ∈ Ioo (0 : ℝ) h₀, ∃ S : SegChart F, ArcGood γ S a h := by
  choose ε hε S hS using fun t : ℝ => local_arc_scale (F := F) (γ := γ) t
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover (fun t : ℝ => ball t (ε t))
    (fun _ => isOpen_ball) (fun x (_ : x ∈ Icc A B) => mem_iUnion.mpr ⟨x, mem_ball_self (hε x)⟩)
  have hT0 : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := mem_iUnion₂.mp (hT (left_mem_Icc.mpr hAB))
    exact ⟨t, ht⟩
  refine ⟨T.inf' hT0 ε, (Finset.lt_inf'_iff hT0).mpr (fun t _ => hε t), fun a ha h hh => ?_⟩
  obtain ⟨t, ht, hat⟩ := mem_iUnion₂.mp (hT ha)
  exact ⟨S t, hS t a hat h ⟨hh.1, hh.2.trans_le (Finset.inf'_le _ ht)⟩⟩

/-- A common scale for the rotations of a loop by all phases in [0, 1]: below it all arcs of
every rotated loop starting in [0, 1] are good. -/
theorem exists_arc_scale_shift (γ : SmoothLoop n) :
    ∃ h₀ > 0, ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ h ∈ Ioo (0 : ℝ) h₀,
      ∃ S : SegChart F, ArcGood (shift γ a) S t h := by
  obtain ⟨h₀, hh₀, hs⟩ := exists_arc_scale_Icc (F := F) γ (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨h₀, hh₀, fun a ha t ht h hh => ?_⟩
  obtain ⟨S, hS⟩ := hs (t + a) ⟨by linarith [ha.1, ht.1], by linarith [ha.2, ht.2]⟩ h hh
  exact ⟨S, arcGood_shift hS⟩

end

end Finsler.GeodesicShift
