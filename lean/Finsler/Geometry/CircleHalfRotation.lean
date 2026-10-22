module

public import Finsler.Geometry.CircleFrameField
public import Finsler.Geometry.GeodesicNormalData
public import Finsler.Geometry.RotationNatural
public import Finsler.Algebra.FrameSignPath
public import Finsler.Analysis.CurveEquivFrames
public import Finsler.Analysis.InvolutionIndex

/-! Half-rotation on the actual sampled critical circle. The phase is that of the prime
geodesic. Consequently the half-rotation shifts it by one half for odd total iteration and
fixes it for even total iteration. -/

@[expose] public section

namespace Finsler.CircleHalfRotation

open Set Module QuadraticForm QuadraticMap
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientSymmetry Finsler.AmbientRotation Finsler.SymmetricBlocks
open Finsler.AmbientDescent Finsler.AmbientPenalty
open Finsler.PolygonDescent Finsler.EnergySphereSmooth Finsler.PolygonCritical
open Finsler.PolygonHessian Finsler.PolygonIterateReduction Finsler.AmbientNormalIndex
open Finsler.PolygonLoop Finsler.SamplePhase Finsler.SmoothSobolev
open Finsler.PolygonModel
open Finsler.GeodesicIteration Finsler.PhaseNullity
open Finsler.NormalFamily Finsler.GeodesicFrames Finsler.CircleFrameField
open Finsler.DefiniteFrames Finsler.FramePath Finsler.FrameIndex
open Finsler.CurveEquivFrames
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {F : ReversibleMetric n}

/-- Natural-number phase periods of the sampled root circle. -/
theorem rootFamily_add_nat (g : Finsler.Geodesics.ClosedGeodesic F) (s N j : ℕ) (a : ℝ) :
    rootFamily g s N (a + j) = rootFamily g s N a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ, ← add_assoc, rootFamily_add_one, ih]

/-- An arbitrary number of vertex shifts in the prime-phase parameter. -/
theorem rootFamily_add_steps (g : Finsler.Geodesics.ClosedGeodesic F) (s N j : ℕ)
    [NeZero s] [NeZero N] (a : ℝ) :
    rootFamily g s N (a + j * (1 / ((2 * N : ℕ) : ℝ))) =
      rotP (j : ZMod (s * (2 * N))) (rootFamily g s N a) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero]
    funext i
    simp [rotP_apply]
  | succ j ih =>
    have he : a + ((j + 1 : ℕ) : ℝ) * (1 / ((2 * N : ℕ) : ℝ)) =
        (a + (j : ℝ) * (1 / ((2 * N : ℕ) : ℝ))) + 1 / ((2 * N : ℕ) : ℝ) := by
      push_cast; ring
    rw [he, rootFamily_add, ih]
    funext i
    simp only [rotP_apply, Nat.cast_succ]
    congr 1
    abel

/-- The vertex index of the half-rotation of the full polygon. -/
def halfIndex (m s N : ℕ) : ZMod (m * (s * (2 * N))) := (m * s * N : ℕ)

theorem halfIndex_add (m s N : ℕ) : halfIndex m s N + halfIndex m s N = 0 := by
  unfold halfIndex
  rw [← Nat.cast_add, show m * s * N + m * s * N = m * (s * (2 * N)) by ring]
  exact ZMod.natCast_self _

/-- The actual normal half-rotation is an involution. -/
theorem normal_half_involutive (m s N : ℕ)
    (v : normal (rotL (n := n) m (s * (2 * N))) m) :
    rotV m (s * (2 * N)) (halfIndex m s N)
      (rotV m (s * (2 * N)) (halfIndex m s N) v) = v := by
  rw [Finsler.RotationNatural.rotV_rotV (n := n), halfIndex_add,
    Finsler.RotationNatural.rotV_zero (n := n)]

/-- The reduced root action is an involution, including when the reduction is zero. -/
theorem root_half_involutive (m s N : ℕ) (z : ZMod (s * (2 * N)) → Ambient n) :
    rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
      (rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z) = z := by
  rw [rotA_rotA, ← map_add, halfIndex_add, map_zero, rotA_zero]

/-- Full half-rotation acts on the sampled prime phase by the total iteration divided by two. -/
theorem root_half_phase (g : Finsler.Geodesics.ClosedGeodesic F) (m s N : ℕ)
    [NeZero s] [NeZero N] (a : ℝ) :
    amb (rootFamily g s N (a + (m * s : ℕ) / 2)) =
      rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
        (amb (rootFamily g s N a)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have he : ((m * s * N : ℕ) : ℝ) * (1 / ((2 * N : ℕ) : ℝ)) = (m * s : ℕ) / 2 := by
    push_cast
    field_simp
  rw [← he, rootFamily_add_steps, amb_rotP]
  simp only [halfIndex, red_natCast]

/-- Odd total iteration moves the actual critical root circle by a half prime period. -/
theorem root_half_odd (g : Finsler.Geodesics.ClosedGeodesic F) (m s N : ℕ)
    [NeZero s] [NeZero N] (hodd : Odd (m * s)) (a : ℝ) :
    amb (rootFamily g s N (a + 1 / 2)) =
      rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
        (amb (rootFamily g s N a)) := by
  obtain ⟨j, hj⟩ := hodd
  have he : a + (m * s : ℕ) / 2 = (a + 1 / 2) + (j : ℝ) := by
    rw [hj]; push_cast; ring
  have h := root_half_phase g m s N a
  rw [he, rootFamily_add_nat] at h
  exact h

/-- Even total iteration fixes every point of the actual critical root circle. -/
theorem root_half_even (g : Finsler.Geodesics.ClosedGeodesic F) (m s N : ℕ)
    [NeZero s] [NeZero N] (heven : Even (m * s)) (a : ℝ) :
    rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
      (amb (rootFamily g s N a)) = amb (rootFamily g s N a) := by
  obtain ⟨j, hj⟩ := heven
  have he : a + (m * s : ℕ) / 2 = a + (j : ℝ) := by
    rw [hj]; push_cast; ring
  have h := root_half_phase g m s N a
  rw [he, rootFamily_add_nat] at h
  exact h.symm

/-- Naturality of the actual normal Hessian under an arbitrary vertex rotation. -/
theorem normalForm_rot (m N : ℕ) [NeZero m] [NeZero N] (a : ZMod (m * N))
    (z : ZMod N → Ambient n)
    (hz : rotA N (red m N a) z ∈ smoothSet m N F)
    (v w : normal (rotL (n := n) m N) m) :
    normalForm m N F (rotA N (red m N a) z) (rotV m N a v) (rotV m N a w) =
      normalForm m N F z v w := by
  change fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N (rotA N (red m N a) z))
    (rotA (m * N) a (v : ZMod (m * N) → Ambient n))
    (rotA (m * N) a (w : ZMod (m * N) → Ambient n)) = _
  rw [Finsler.RotationNatural.iterA_rotA]
  apply sndDeriv_pen_rotA F 1 a
  have h : ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N (rotA N (red m N a) z)) := hz
  rw [Finsler.RotationNatural.iterA_rotA] at h
  exact h.of_le (by norm_num)

/-- For odd total iteration the normal form has the involutive half-period symmetry. -/
theorem formB_half_odd (g : Finsler.Geodesics.ClosedGeodesic F) (m s N : ℕ)
    [NeZero m] [NeZero s] [NeZero N] (hodd : Odd (m * s))
    (hsm : ∀ a, amb (rootFamily g s N a) ∈ smoothSet m (s * (2 * N)) F)
    (a : ℝ) (v w : normal (rotL (n := n) m (s * (2 * N))) m) :
    formB m (s * (2 * N)) F (rootFamily g s N) (a + 1 / 2)
      (rotV m (s * (2 * N)) (halfIndex m s N) v)
      (rotV m (s * (2 * N)) (halfIndex m s N) w) =
        formB m (s * (2 * N)) F (rootFamily g s N) a v w := by
  change normalForm m (s * (2 * N)) F (amb (rootFamily g s N (a + 1 / 2))) _ _ = _
  rw [root_half_odd g m s N hodd a]
  apply normalForm_rot
  rw [← root_half_odd g m s N hodd a]
  exact hsm _

/-- For even total iteration each normal form is invariant under the half-rotation. -/
theorem formB_half_even (g : Finsler.Geodesics.ClosedGeodesic F) (m s N : ℕ)
    [NeZero m] [NeZero s] [NeZero N] (heven : Even (m * s))
    (hsm : ∀ a, amb (rootFamily g s N a) ∈ smoothSet m (s * (2 * N)) F)
    (a : ℝ) (v w : normal (rotL (n := n) m (s * (2 * N))) m) :
    formB m (s * (2 * N)) F (rootFamily g s N) a
      (rotV m (s * (2 * N)) (halfIndex m s N) v)
      (rotV m (s * (2 * N)) (halfIndex m s N) w) =
        formB m (s * (2 * N)) F (rootFamily g s N) a v w := by
  have h := normalForm_rot m (s * (2 * N)) (F := F) (halfIndex m s N)
    (amb (rootFamily g s N a)) (by rw [root_half_even g m s N heven a]; exact hsm a) v w
  rw [root_half_even g m s N heven a] at h
  exact h

/-- A closed frame is constant on the fibers of the actual sampled prime circle. -/
theorem closed_frame_same_root (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m N : ℕ) [NeZero s] [NeZero N]
    (hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N))
    {b : ℕ} (H : ℝ → Fin b → normal (rotL (n := n) m (s * (2 * N))) m)
    (he : H 1 = H 0) :
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ a' ∈ Icc (0 : ℝ) 1,
      amb (rootFamily g s N a) = amb (rootFamily g s N a') → H a = H a' := by
  intro a ha a' ha' h
  have hroot : rootFamily g s N a = rootFamily g s N a' :=
    funext fun i => Subtype.ext (congrFun h i)
  rcases phase_eq_of_root_eq M g hprime s N hf ha ha' hroot with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
  · rw [h1, h2, he]
  · rw [h1, h2, he]

/-- A signed-equivariant definite frame field near an entire actual critical circle. -/
structure SignedFrameField (g : Finsler.Geodesics.ClosedGeodesic F) (s m N : ℕ)
    [NeZero s] [NeZero m] [NeZero N] (ε : ℝ) (b : ℕ) where
  d : Fin b → ℝ
  G : (ZMod (s * (2 * N)) → Ambient n) →
    Fin b → normal (rotL (n := n) m (s * (2 * N))) m
  U : Set (ZMod (s * (2 * N)) → Ambient n)
  signs : ∀ i, d i * d i = 1
  smooth : ContDiff ℝ ∞ G
  equivariant : ∀ z,
    G (rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z) =
      signAction (rotV m (s * (2 * N)) (halfIndex m s N)) d (G z)
  isOpen : IsOpen U
  circle_mem : ∀ a, amb (rootFamily g s N a) ∈ U
  subset_smooth : U ⊆ smoothSet m (s * (2 * N)) F
  invariant : ∀ z,
    rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z ∈ U ↔ z ∈ U
  definite : ∀ z ∈ U, Neg (ε • normalForm m (s * (2 * N)) F z) (G z)

/-- For odd total iteration a maximal definite family on the actual critical circle gives a
smooth signed-equivariant frame on an invariant neighborhood. Taking ε = 1 or -1 treats the
negative and positive frames with the same construction. -/
theorem exists_odd_frame_field (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m N : ℕ)
    [NeZero s] [NeZero m] [NeZero N] (hodd : Odd (m * s))
    (hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N))
    (hsm : ∀ a, amb (rootFamily g s N a) ∈ smoothSet m (s * (2 * N)) F)
    {b : ℕ} (ε : ℝ)
    (hF : Family (fun a => ε • formB m (s * (2 * N)) F (rootFamily g s N) a) b) :
    Nonempty (SignedFrameField g s m N ε b) := by
  let T := rotV (n := n) m (s * (2 * N)) (halfIndex m s N)
  let τ := rotA (n := n) (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
  have hTT : ∀ v, T (T v) = v := normal_half_involutive m s N
  have hττ : ∀ z, τ (τ z) = z := root_half_involutive m s N
  obtain ⟨G₀, hG₀⟩ := hF.ex 0
  have hT : ∀ a v w,
      (ε • formB m (s * (2 * N)) F (rootFamily g s N) (a + 1 / 2)) (T v) (T w) =
        (ε • formB m (s * (2 * N)) F (rootFamily g s N) a) v w := by
    intro a v w
    change ε * formB m (s * (2 * N)) F (rootFamily g s N) (a + 1 / 2) (T v) (T w) =
      ε * formB m (s * (2 * N)) F (rootFamily g s N) a v w
    rw [formB_half_odd g m s N hodd hsm]
  obtain ⟨d, hd, H, hH, hH0, hHe, hHn, hHs⟩ :=
    Finsler.FrameSignPath.exists_twisted_closed_frame hF T hTT (by norm_num : (0 : ℝ) < 1 / 2) hT hG₀
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hHe hHn
  have hclosed : H 1 = H 0 := hHe.trans hH0.symm
  have hHS : ∀ a ∈ Icc (0 : ℝ) (1 / 2), H (a + 1 / 2) = signAction T d (H a) := by
    intro a ha
    rw [signAction_eq_mulF]
    exact hHs a ha
  have hshift := half_shift_witnesses τ (signAction T d) hττ
    (signAction_involutive T hTT d hd) (c := fun a => amb (rootFamily g s N a))
    (H := H) (by norm_num : (0 : ℝ) < 1 / 2)
    (fun a _ => root_half_odd g m s N hodd a) hHS
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hshift
  obtain ⟨G, U, hG, hGeq, hU, hcurve, hsub, hUτ, hneg⟩ :=
    exists_equivariant_field_on_curve τ (signAction T d) hττ (signAction_involutive T hTT d hd)
      (rootFamily_continuous g s N) hH (closed_frame_same_root M g hprime s m N hf H hclosed)
      hshift (smoothSet_isOpen m (s * (2 * N)) F) (fun a _ => hsm a)
      (fun z => ε • normalForm m (s * (2 * N)) F z)
      (continuousOn_const.smul (normalForm_continuousOn m (s * (2 * N)) F)) hHn
  refine ⟨⟨d, G, U, hd, hG, hGeq, hU, ?_, hsub, hUτ, hneg⟩⟩
  intro a
  rw [rootFamily_fract]
  exact hcurve _ ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩

/-- **Adapted fields for odd iterates of a prime geodesic.** For all sufficiently fine samples,
the actual negative and positive normal frames are smooth and signed-equivariant under the
full polygon half-rotation. Their sizes are the index difference and its complement. -/
theorem exists_odd_frame_fields (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hodd : Odd (m * s)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      Nonempty (SignedFrameField g s m N 1 ((iterData g).I (s * m) - (iterData g).I s)) ∧
      Nonempty (SignedFrameField g s m N (-1)
        (finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
          ((iterData g).I (s * m) - (iterData g).I s))) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all M g
  obtain ⟨N₁, hN₁⟩ := Finsler.GeodesicNormalData.exists_normal_families g s m hgcd
  refine ⟨K₀ + N₁, fun N hN _ => ?_⟩
  have hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N) := fun a =>
    hK₀ a (2 * N) (by omega)
  obtain ⟨hsm, hF₁, hF₂, -⟩ := hN₁ N (by omega)
  exact ⟨exists_odd_frame_field M g hprime s m N hodd hf hsm 1 (by simpa only [one_smul] using hF₁),
    exists_odd_frame_field M g hprime s m N hodd hf hsm (-1) (by simpa only [neg_one_smul] using hF₂)⟩

end

end Finsler.CircleHalfRotation
