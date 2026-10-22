module

public import Finsler.Geometry.GeodesicFrames
public import Finsler.Analysis.FrameField

/-! Smooth definite frame fields of the normal bundle near the critical circle of an iterate of
a prime closed geodesic. Iteration of polygons is injective. For a prime closed geodesic and N
large, two phases in [0, 1] with the same root polygon are equal or are the two ends of the
interval: the polygon of samples determines its broken geodesic, which is the rotated loop, and
a prime loop has no period below 1. The penalized energy is C³ at short sphere polygons without
zero edges, and the set of the ambient root polygons whose m-fold iterates are points at which
it is C³ is open and contains the circle of the root polygons. On this set the second
derivative at the iterate, restricted to the normal space, depends continuously on the root
polygon. Hence the closed negative and positive frames along the critical circle extend to
smooth negative and positive frame fields on a neighbourhood of the circle of the root
polygons. -/

@[expose] public section

namespace Finsler.CircleFrameField

open Module QuadraticForm QuadraticMap Filter Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.PolygonSampling Finsler.PolygonModel
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.AmbientRotation
open Finsler.PolygonIterateReduction Finsler.PhaseNullity Finsler.SamplePhase
open Finsler.SmoothSobolev Finsler.DefiniteFrames Finsler.NormalFamily Finsler.GeodesicFrames
open Finsler.GeodesicIteration Finsler.FrameField
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ}

/-- Iteration of polygons is injective. -/
theorem iterate_injective {α : Type*} (m N : ℕ) [NeZero N] {q q' : ZMod N → α}
    (h : iterate m N q = iterate m N q') : q = q' := by
  funext i
  have h1 := congrFun h ((i.val : ℕ) : ZMod (m * N))
  rw [iterate_apply, iterate_apply, red_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

section Normal

variable (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n)

/-- The second derivative of the penalized energy at the m-fold iterate of an ambient polygon,
restricted to the normal space. -/
def normalForm (z : ZMod N → Ambient n) :
    normal (rotL (n := n) m N) m →ₗ[ℝ] normal (rotL (n := n) m N) m →ₗ[ℝ] ℝ :=
  ((fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N z)).toLinearMap₁₂).compl₁₂
    (normal (rotL (n := n) m N) m).subtype (normal (rotL (n := n) m N) m).subtype

/-- The ambient polygons at whose m-fold iterates the penalized energy is C³. -/
def smoothSet : Set (ZMod N → Ambient n) :=
  {z | ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N z)}

theorem smoothSet_isOpen : IsOpen (smoothSet m N F) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have h1 : ∀ᶠ y in 𝓝 (iterA (n := n) m N z), ContDiffAt ℝ 3 (pen F (m * N) 1) y :=
    ContDiffAt.eventually hz (by simp)
  exact (iterA (n := n) m N).continuous.continuousAt.eventually h1

theorem normalForm_continuousOn :
    ContinuousOn (fun p : (ZMod N → Ambient n) × normal (rotL (n := n) m N) m ×
        normal (rotL (n := n) m N) m => normalForm m N F p.1 p.2.1 p.2.2)
      (smoothSet m N F ×ˢ univ) := by
  rintro ⟨z, v, w⟩ ⟨hz, -⟩
  have hz' : ContDiffAt ℝ 3 (pen F (m * N) 1) (iterA m N z) := hz
  have h2 : ContinuousAt (fderiv ℝ (fderiv ℝ (pen F (m * N) 1))) (iterA m N z) :=
    (((hz'.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_right (m := 1)
      (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have h3 : ContinuousAt (fun p : (ZMod N → Ambient n) × normal (rotL (n := n) m N) m ×
      normal (rotL (n := n) m N) m =>
      fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N p.1)) (z, v, w) :=
    ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ (pen F (m * N) 1)))
      (f := fun p : (ZMod N → Ambient n) × normal (rotL (n := n) m N) m ×
        normal (rotL (n := n) m N) m => iterA m N p.1) h2
      ((iterA (n := n) m N).continuous.comp continuous_fst).continuousAt
  have h4 : ContinuousAt (fun p : (ZMod N → Ambient n) × normal (rotL (n := n) m N) m ×
      normal (rotL (n := n) m N) m =>
      fderiv ℝ (fderiv ℝ (pen F (m * N) 1)) (iterA m N p.1)
        (p.2.1 : ZMod (m * N) → Ambient n) (p.2.2 : ZMod (m * N) → Ambient n)) (z, v, w) :=
    (h3.clm_apply (continuous_subtype_val.comp
      (continuous_fst.comp continuous_snd)).continuousAt).clm_apply
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).continuousAt
  exact h4.continuousWithinAt

end Normal

variable {F : ReversibleMetric n}

/-- The root polygon only depends on the fractional part of the phase. -/
theorem rootFamily_fract (g : Finsler.Geodesics.ClosedGeodesic F) (s N : ℕ) (a : ℝ) :
    rootFamily g s N a = rootFamily g s N (Int.fract a) := by
  unfold rootFamily
  rw [shift_fract]

/-- **Phases with the same root polygon.** For a prime closed geodesic whose polygons of 2 N
samples have the sample facts at all phases, two phases in [0, 1] with the same root polygon
are equal or are the two ends of the interval. -/
theorem phase_eq_of_root_eq (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s N : ℕ) [NeZero s] [NeZero N]
    (hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N)) {a a' : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ha' : a' ∈ Icc (0 : ℝ) 1)
    (h : rootFamily g s N a = rootFamily g s N a') :
    a = a' ∨ (a = 0 ∧ a' = 1) ∨ (a = 1 ∧ a' = 0) := by
  have hp : samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)) =
      samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a')) :=
    iterate_injective s (2 * N) h
  have key : ∀ (q q' : ZMod (2 * N) → Sphere n), q = q' → ∀ (hq : ShortPolygon M.δ q)
      (hq' : ShortPolygon M.δ q'), polySphereLoop F M.seg hq = polySphereLoop F M.seg hq' := by
    intro q q' e
    subst e
    intro hq hq'
    rfl
  have hloop : ofSmooth (Finsler.Loops.shift g.loop a) =
      ofSmooth (Finsler.Loops.shift g.loop a') := by
    rw [← (hf a).2.2.2.2.2.2 (hf a).1, ← (hf a').2.2.2.2.2.2 (hf a').1]
    exact key _ _ hp _ _
  have hshift := ofSmooth_injective hloop
  have hval : ∀ t : ℝ, g.loop (t + a) = g.loop (t + a') := fun t =>
    congrArg (fun σ : Finsler.Loops.SmoothLoop n => σ t) hshift
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have hper : Function.Periodic g.loop (a' - a) := fun t => by
      have h1 := hval (t - a)
      rw [sub_add_cancel] at h1
      rw [h1]
      congr 1
      ring
    have h1 := hprime (a' - a) (by linarith) hper
    exact Or.inr (Or.inl ⟨by linarith [ha.1, ha'.2], by linarith [ha.1, ha'.2]⟩)
  · exact Or.inl heq
  · have hper : Function.Periodic g.loop (a - a') := fun t => by
      have h1 := hval (t - a')
      rw [sub_add_cancel] at h1
      rw [← h1]
      congr 1
      ring
    have h1 := hprime (a - a') (by linarith) hper
    exact Or.inr (Or.inr ⟨by linarith [ha.2, ha'.1], by linarith [ha.2, ha'.1]⟩)

/-- The penalized energy is C³ at a short sphere polygon without zero edges. -/
theorem pen_contDiffAt_three (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {K : ℕ} [NeZero K] {q : ZMod K → Sphere n} (hq : ShortPolygon δ q)
    (hne : ∀ i, q (i + 1) ≠ q i) (lam : ℝ) : ContDiffAt ℝ 3 (pen F K lam) (amb q) := by
  have hE : ContDiffAt ℝ 3 (polyEnergyN F K) (amb q) := polyEnergyN_contDiffAt F hδ hq hne
  unfold pen
  exact hE.add (contDiffAt_const.mul ((logPen_contDiffAt (incl q)).of_le (by simp)))


/-- The normal form at a root polygon is the form of the family. -/
theorem normalForm_root (g : Finsler.Geodesics.ClosedGeodesic F) (s m N : ℕ) [NeZero s]
    [NeZero m] [NeZero N] (a : ℝ) :
    normalForm m (s * (2 * N)) F (amb (rootFamily g s N a)) =
      formB m (s * (2 * N)) F (rootFamily g s N) a := rfl

/-- **Smooth frame fields near the critical circle.** For a prime closed geodesic with period L
and index function I, and s, m ≥ 1 with gcd(s m, L) = gcd(s, L) and s even or m odd: for N
large there are an open set of ambient root polygons containing the circle of the root
polygons, on whose m-fold iterates the penalized energy is C³, and smooth fields of
I(s m) - I(s) negative and of the complementary number of positive normal vectors on it. -/
theorem exists_frame_fields (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m : ℕ) [NeZero s] [NeZero m]
    (hgcd : Nat.gcd (s * m) (iterData g).L = Nat.gcd s (iterData g).L)
    (hpar : Even s ∨ Odd m) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ∃ 𝒪 : Set (ZMod (s * (2 * N)) → Ambient n), IsOpen 𝒪 ∧
        (∀ a : ℝ, amb (rootFamily g s N a) ∈ 𝒪) ∧ 𝒪 ⊆ smoothSet m (s * (2 * N)) F ∧
        ∃ (G₁ : (ZMod (s * (2 * N)) → Ambient n) →
            Fin ((iterData g).I (s * m) - (iterData g).I s) →
              normal (rotL (n := n) m (s * (2 * N))) m)
          (G₂ : (ZMod (s * (2 * N)) → Ambient n) →
            Fin (finrank ℝ (normal (rotL (n := n) m (s * (2 * N))) m) -
              ((iterData g).I (s * m) - (iterData g).I s)) →
              normal (rotL (n := n) m (s * (2 * N))) m),
          ContDiff ℝ ∞ G₁ ∧ ContDiff ℝ ∞ G₂ ∧
          ∀ z ∈ 𝒪, Neg (normalForm m (s * (2 * N)) F z) (G₁ z) ∧
            Neg (-normalForm m (s * (2 * N)) F z) (G₂ z) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all M g
  obtain ⟨N₁, hN₁⟩ := exists_closed_frames g s m hgcd hpar
  refine ⟨K₀ + N₁, fun N hN _ => ?_⟩
  have hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N) := fun a =>
    hK₀ a (2 * N) (by omega)
  obtain ⟨⟨H₁, hH₁, hH₁e, hH₁n⟩, ⟨H₂, hH₂, hH₂e, hH₂n⟩⟩ := hN₁ N (by omega)
  have hcirc : ∀ a : ℝ, amb (rootFamily g s N a) ∈ smoothSet m (s * (2 * N)) F := fun a =>
    pen_contDiffAt_three F M.smooth
      (shortPolygon_iterate m (s * (2 * N)) (shortPolygon_iterate s (2 * N) (hf a).1))
      (iterate_ne m (s * (2 * N)) (iterate_ne s (2 * N) (hf a).2.1)) 1
  have hcont := rootFamily_continuous g s N
  have hcH : ∀ (b : ℕ) (H : ℝ → Fin b → normal (rotL (n := n) m (s * (2 * N))) m),
      H 1 = H 0 → ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1,
      amb (rootFamily g s N θ) = amb (rootFamily g s N θ') → H θ = H θ' := by
    intro b H hHe θ hθ θ' hθ' h
    have hroot : rootFamily g s N θ = rootFamily g s N θ' :=
      funext fun i => Subtype.ext (congrFun h i)
    rcases phase_eq_of_root_eq M g hprime s N hf hθ hθ' hroot with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
    · rw [h1, h2, hHe]
    · rw [h1, h2, hHe]
  obtain ⟨𝒪₁, h𝒪₁, hc₁, hsub₁, G₁, hG₁, hneg₁⟩ := exists_frame_field
    (smoothSet_isOpen m (s * (2 * N)) F) (normalForm m (s * (2 * N)) F)
    (normalForm_continuousOn m (s * (2 * N)) F) hcont (L := 1) (fun θ _ => hcirc θ) hH₁
    (hcH _ H₁ hH₁e) hH₁n
  obtain ⟨𝒪₂, h𝒪₂, hc₂, hsub₂, G₂, hG₂, hneg₂⟩ := exists_frame_field
    (smoothSet_isOpen m (s * (2 * N)) F) (fun z => -normalForm m (s * (2 * N)) F z)
    ((normalForm_continuousOn m (s * (2 * N)) F).neg) hcont (L := 1) (fun θ _ => hcirc θ) hH₂
    (hcH _ H₂ hH₂e) hH₂n
  refine ⟨𝒪₁ ∩ 𝒪₂, h𝒪₁.inter h𝒪₂, fun a => ?_, fun z hz => hsub₁ hz.1, G₁, G₂, hG₁, hG₂,
    fun z hz => ⟨hneg₁ z hz.1, hneg₂ z hz.2⟩⟩
  rw [rootFamily_fract]
  have hmem : Int.fract a ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩
  exact ⟨hc₁ _ hmem, hc₂ _ hmem⟩

end

end Finsler.CircleFrameField
