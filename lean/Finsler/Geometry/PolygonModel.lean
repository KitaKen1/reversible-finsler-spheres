module

public import Finsler.Geometry.MilnorEquivariance
public import Finsler.Geometry.PolygonGeodesic
public import Finsler.Geometry.NormalizationContinuity

/-! The finite polygon model of energy sublevels. Short minimizing segments with uniform
dependence, reversal symmetry, package identification and C³ minimal energy off the diagonal
exist below one radius δ. For every level a and every N above a threshold, samples at spacing
1/N of loops of energy below a² are closer than δ; the sampling map s_N, the broken geodesic
map b_N on short polygons and the straightening homotopy H form the model: s_N∘b_N = id,
f_N∘s_N ≤ E, E∘b_N = f_N, H is an energy non-increasing homotopy from the identity to b_N∘s_N,
all three commute with the rotation by 1/N and with the reversal, and so every sublevel
{E < b²}, b ≤ a, corresponds to the polygon sublevel {f_N < b²}. Critical polygons of positive
energy are closed geodesics and fine samples of closed geodesics are critical with f_N = E and
broken geodesic the geodesic. The normalization deforms the length sublevel {ℓ < a} into
{E < a²} through loops of the same length. -/

@[expose] public section

namespace Finsler.PolygonModel

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling Finsler.MilnorContinuity
open Finsler.MilnorEquivariance Finsler.PolygonGeodesic Finsler.SegmentAtlas Finsler.GeodesicArcs
open Finsler.NormalizationHomotopy Finsler.NormalizationContinuity Finsler.SobolevLength
open Finsler.SmoothSobolev
open Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- Short minimizing segments below a uniform radius. -/
structure SegmentData (F : ReversibleMetric n) where
  δ : ℝ
  pos : 0 < δ
  sc : Sphere n → Sphere n → ℝ → Ambient n
  sv : Sphere n → Sphere n → ℝ → Ambient n
  seg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q
  unif : ∀ P₀ Q₀ : Sphere n, ‖(Q₀ : Ambient n) - P₀‖ < δ → ∀ ε > 0,
    ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖sc x.1 x.2 t - sc P₀ Q₀ t‖ < ε ∧ ‖sv x.1 x.2 t - sv P₀ Q₀ t‖ < ε
  rev : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
    sc Q P s = sc P Q (1 - s)
  pkg : ∀ (T : SegChart F) (P Q : Sphere n), P ∈ segDom T → ‖(Q : Ambient n) - P‖ < δ →
    ‖(Q : Ambient n) - P‖ < T.δ → ∀ t ∈ Icc (0 : ℝ) 1, sc P Q t = segCurve T P Q t
  smooth : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (Finsler.EnergySphereSmooth.ambientMinEnergy F)
      ((P : Ambient n), (Q : Ambient n))

theorem exists_segmentData (F : ReversibleMetric n) : Nonempty (SegmentData F) := by
  obtain ⟨δ₁, hδ₁, sc, sv, hseg, hunif, hrev, -, hpkg⟩ :=
    Finsler.SegmentCurves.exists_segment_curves F
  obtain ⟨δ₂, hδ₂, hsm⟩ := Finsler.EnergySphereSmooth.exists_ambientMinEnergy_contDiffAt F
  exact ⟨SegmentData.mk (min δ₁ δ₂) (lt_min hδ₁ hδ₂) sc sv
    (fun P Q h => hseg P Q (h.trans_le (min_le_left _ _)))
    (fun P₀ Q₀ h => hunif P₀ Q₀ (h.trans_le (min_le_left _ _)))
    (fun P Q h s hs => (hrev P Q (h.trans_le (min_le_left _ _)) s hs).1)
    (fun T P Q hP h hT t ht => hpkg T P Q hP (h.trans_le (min_le_left _ _)) hT t ht)
    (fun P Q hne h => hsm P Q hne (h.trans_le (min_le_right _ _)))⟩

/-- A polygon model of the sublevel {E < a²} with N vertices. -/
structure PolygonModelData (F : ReversibleMetric n) (a : ℝ) (N : ℕ) extends SegmentData F where
  space : ∀ u : SphereLoop n, SobolevEnergy.energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ

/-- Every level has polygon models for all large N. -/
theorem exists_polygonModelData (F : ReversibleMetric n) (a : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N → Nonempty (PolygonModelData F a N) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  exact ⟨N₀, fun N hN hpos =>
    ⟨PolygonModelData.mk S fun u hu s t hs ht hst => hN₀ N hN hpos u hu s t hs ht hst⟩⟩

section Model

variable {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F a N)

/-- The broken geodesic of a short polygon. -/
def broken (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) : SphereLoop n :=
  polySphereLoop F M.seg q.2

/-- The straightening homotopy of the model. -/
def deform (p : ℝ × SphereLoop n) : SphereLoop n := milnorH F M.seg M.space p

theorem sample_short {u : SphereLoop n} (hu : SobolevEnergy.energy F u < a ^ 2) :
    ShortPolygon M.δ (samplePoly N u) :=
  shortPolygon_samplePoly F M.space hu

theorem broken_continuous : Continuous (broken M) := by
  rw [(sphereLoop_data_isometry n).isEmbedding.continuous_iff]
  rw [continuous_iff_continuousAt]
  intro q₀
  have h := (brokenGeodesic_continuousAt F M.seg M.unif N q₀.2).comp
    (continuous_subtype_val.continuousAt (x := q₀))
  refine h.congr (Eventually.of_forall fun q => ?_)
  change brokenGeodesic F M.seg N q.1 = polyLoop F M.seg q.2
  exact brokenGeodesic_of_short F M.seg N q.2

theorem sample_broken (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    samplePoly N (broken M q) = q.1 :=
  samplePoly_polySphereLoop F M.seg q.2

theorem energy_broken (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    SobolevEnergy.energy F (broken M q) = polyEnergy F N (fun i => (q.1 i : Ambient n)) :=
  (polyEnergy_polySphereLoop F M.seg q.2).symm

theorem polyEnergy_samplePoly_le (u : SphereLoop n) :
    polyEnergy F N (fun i => (samplePoly N u i : Ambient n)) ≤ SobolevEnergy.energy F u :=
  polyEnergy_sample_le F u

theorem deform_continuousOn :
    ContinuousOn (deform M)
      (Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | SobolevEnergy.energy F u < a ^ 2}) :=
  milnorH_continuousOn F M.seg M.unif M.space

theorem deform_zero {u : SphereLoop n} (hu : SobolevEnergy.energy F u < a ^ 2) :
    deform M (0, u) = u :=
  milnorH_zero F M.seg M.space hu

theorem deform_one {u : SphereLoop n} (hu : SobolevEnergy.energy F u < a ^ 2) :
    deform M (1, u) = broken M ⟨samplePoly N u, sample_short M hu⟩ :=
  milnorH_one F M.seg M.space hu

theorem energy_deform_le {p : ℝ × SphereLoop n}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | SobolevEnergy.energy F u < a ^ 2}) :
    SobolevEnergy.energy F (deform M p) ≤ SobolevEnergy.energy F p.2 :=
  energy_milnorH_le F M.seg M.space hp

theorem sample_rotate (u : SphereLoop n) :
    samplePoly N ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u) =
      rotatePolygon (samplePoly N u) :=
  samplePoly_rotate u

theorem broken_rotate (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    broken M ⟨rotatePolygon q.1, shortPolygon_rotate q.2⟩ =
      (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ broken M q :=
  polySphereLoop_rotate F M.seg q.2

theorem deform_rotate (p : ℝ × SphereLoop n) :
    deform M (p.1, (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ p.2) =
      (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ deform M p :=
  milnorH_rotate F M.seg M.space p

theorem sample_reverse (u : SphereLoop n) :
    samplePoly N (Finsler.SobolevReverse.reverseSphere u) = reversePolygon (samplePoly N u) :=
  samplePoly_reverse u

theorem broken_reverse (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    broken M ⟨reversePolygon q.1, shortPolygon_reverse q.2⟩ =
      Finsler.SobolevReverse.reverseSphere (broken M q) :=
  polySphereLoop_reverse F M.seg M.rev q.2

theorem deform_reverse (p : ℝ × SphereLoop n) :
    deform M (p.1, Finsler.SobolevReverse.reverseSphere p.2) =
      Finsler.SobolevReverse.reverseSphere (deform M p) :=
  milnorH_reverse F M.seg M.rev M.space p

omit [NeZero N] in
/-- The circle point of k/N. -/
theorem circle_natCast_div_succ (k : ℕ) :
    ((((k + 1 : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) =
      (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +
        ((((k : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) := by
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  ring

/-- Sampling commutes with the rotation by k/N. -/
theorem sample_rotate_nat (k : ℕ) (u : SphereLoop n) :
    samplePoly N (((((k : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ u) =
      rotatePolygon^[k] (samplePoly N u) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_div, AddCircle.coe_zero, zero_vadd, Function.iterate_zero,
      id_eq]
  | succ k ih =>
    rw [circle_natCast_div_succ, add_vadd, sample_rotate, ih, Function.iterate_succ_apply']

/-- The homotopy commutes with the rotation by k/N. -/
theorem deform_rotate_nat (k : ℕ) (p : ℝ × SphereLoop n) :
    deform M (p.1, (((((k : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ p.2)) =
      ((((k : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ deform M p := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_div, AddCircle.coe_zero, zero_vadd]
  | succ k ih =>
    rw [circle_natCast_div_succ, add_vadd, add_vadd, ← ih]
    exact deform_rotate M (p.1, ((((k : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ p.2)

/-- Rotation of short polygons. -/
def rotateShort (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    {q : ZMod N → Sphere n // ShortPolygon M.δ q} :=
  ⟨rotatePolygon q.1, shortPolygon_rotate q.2⟩

/-- Broken geodesics commute with the rotation by k/N. -/
theorem broken_rotate_nat (k : ℕ) (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    broken M ((rotateShort M)^[k] q) =
      ((((k : ℕ) : ℝ) / N : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ broken M q := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_div, AddCircle.coe_zero,
      zero_vadd]
  | succ k ih =>
    rw [Function.iterate_succ_apply', circle_natCast_div_succ, add_vadd, ← ih]
    exact broken_rotate M ((rotateShort M)^[k] q)

/-- Sampling maps every sublevel into the corresponding polygon sublevel. -/
theorem sample_sublevel {b : ℝ} {u : SphereLoop n} (hu : SobolevEnergy.energy F u < b ^ 2) :
    polyEnergy F N (fun i => (samplePoly N u i : Ambient n)) < b ^ 2 :=
  (polyEnergy_samplePoly_le u).trans_lt hu

/-- Broken geodesics map polygon sublevels into the corresponding sublevels. -/
theorem broken_sublevel {b : ℝ} (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q})
    (hq : polyEnergy F N (fun i => (q.1 i : Ambient n)) < b ^ 2) :
    SobolevEnergy.energy F (broken M q) < b ^ 2 := by
  rw [energy_broken]
  exact hq

/-- The homotopy preserves every sublevel. -/
theorem deform_sublevel {b : ℝ} {p : ℝ × SphereLoop n}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ {u : SphereLoop n | SobolevEnergy.energy F u < a ^ 2})
    (hb : SobolevEnergy.energy F p.2 < b ^ 2) :
    SobolevEnergy.energy F (deform M p) < b ^ 2 :=
  (energy_deform_le M hp).trans_lt hb

/-- Critical polygons of positive energy are closed geodesics. -/
theorem broken_closedGeodesic (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q})
    (hc : PolyCritical F N q.1) (hpos : 0 < polyEnergy F N (fun i => (q.1 i : Ambient n))) :
    ∃ γ : Finsler.Geodesics.ClosedGeodesic F, ∀ t,
      ((γ.loop t : Sphere n) : Ambient n) =
        Finsler.SobolevCircleRepresentative.realMap (broken M q).data t :=
  exists_closedGeodesic_of_polyCritical F M.seg q.2 hc hpos

end Model

section Geodesics

variable {F : ReversibleMetric n} (S : SegmentData F)

/-- Fine samples of a closed geodesic are short critical polygons with f_N = E. -/
theorem sample_closedGeodesic (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ShortPolygon S.δ (samplePoly N (ofSmooth g.loop)) ∧
      PolyCritical F N (samplePoly N (ofSmooth g.loop)) ∧
      polyEnergy F N (sampleN N (ofSmooth g.loop)) = SobolevEnergy.energy F (ofSmooth g.loop) :=
  polyCritical_of_closedGeodesic F S.pos S.smooth g

/-- For N large the broken geodesic of the samples of a closed geodesic is the geodesic. -/
theorem broken_sample_closedGeodesic (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ∀ hq : ShortPolygon S.δ (samplePoly N (ofSmooth g.loop)),
        polySphereLoop F S.seg hq = ofSmooth g.loop := by
  obtain ⟨h₀, hh₀, hscale⟩ := exists_arc_scale (F := F) (γ := g.loop)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / h₀)
  refine ⟨N₀ + 1, fun N hN _ hq => polySphereLoop_samples S.seg S.pkg g hscale ?_ hq⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hlt : 1 / h₀ < N := hN₀.trans (by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self N₀) hN)
  rw [div_lt_iff₀ hNpos]
  rw [div_lt_iff₀ hh₀] at hlt
  linarith

end Geodesics

section Length

variable (F : ReversibleMetric n)

/-- Energy sublevels lie in length sublevels. -/
theorem length_lt_of_energy_lt {a : ℝ} (ha : 0 < a) {u : SphereLoop n}
    (hu : SobolevEnergy.energy F u < a ^ 2) : length F u < a := by
  have h := length_sq_le_energy F u
  have h0 := length_nonneg F u
  nlinarith

/-- The normalized loop of a loop of length below a has energy below a². -/
theorem energy_normLoop_one_lt {a : ℝ} (ha : 0 < a) {u : SphereLoop n} (hu : length F u < a) :
    SobolevEnergy.energy F (normLoop F (1, u)) < a ^ 2 := by
  by_cases hL : 0 < length F u
  · rw [energy_normLoop_one F hL]
    have h0 := length_nonneg F u
    nlinarith
  · have hL0 : length F u = 0 := le_antisymm (not_lt.mp hL) (length_nonneg F u)
    rw [normLoop_of_length_eq_zero F (p := (1, u)) hL0]
    have hE := energy_eq_zero_of_length F hL0
    change SobolevEnergy.energy F u < a ^ 2
    rw [hE]
    positivity

/-- The normalization homotopy stays in the length sublevel. -/
theorem length_normLoop_lt {a : ℝ} {p : ℝ × SphereLoop n} (hu : length F p.2 < a) :
    length F (normLoop F p) < a := by
  rw [length_normLoop F p]
  exact hu

/-- The normalization homotopy stays in the energy sublevel. -/
theorem energy_normLoop_lt {a : ℝ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {u : SphereLoop n}
    (hu : SobolevEnergy.energy F u < a ^ 2) :
    SobolevEnergy.energy F (normLoop F (s, u)) < a ^ 2 :=
  (energy_normLoop_le_energy F hs u).trans_lt hu

end Length

end

end Finsler.PolygonModel
