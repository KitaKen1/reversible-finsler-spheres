module

public import Finsler.Geometry.PolygonDescent
public import Finsler.Geometry.PolygonModel
public import Finsler.Topology.PairTriple
public import Finsler.Topology.BorelCrossing
public import Finsler.Geometry.PolygonEnergyGlobal

/-! The crossing pairs of the loop space and of a polygon model have the same cohomology. Let M
be a polygon model of the sublevel of a level A with N vertices, and 0 < a ≤ b ≤ A cuts such
that the polygons of energy below b² are short. Sampling maps the loops below b to the polygons
of energy below b², and the loops below a to those of energy below a²; the broken geodesic maps
back; sampling a broken geodesic gives the polygon again, and the straightening homotopy joins
the broken geodesic of the samples to the loop without increasing the energy. Hence sampling is
bijective on the ordinary cohomology of the pairs: the cohomology of the polygons of energy
below b² relative to those of energy below a² is the cohomology of the loop pair (t_b, t_a).
For every level A this holds for all large N and all cuts 0 < a ≤ b ≤ A. -/

@[expose] public section

namespace Finsler.PolygonLoopPairs

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevReflectionAction Finsler.PolygonCritical
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.PolygonDescent
open Finsler.FlowLens Finsler.BorelCochain Finsler.BorelLoop Finsler.PairTriple
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} {F : ReversibleMetric n} {A : ℝ} {N : ℕ} [NeZero N]
  (M : PolygonModelData F A N)

/-- For b > 0 the level set t_b consists of the loops with √E < b. -/
theorem mem_lev_iff {b : ℝ} (hb : 0 < b) (u : SphereLoop n) :
    u ∈ lev F b ↔ SobolevEnergy.energy F u < b ^ 2 := by
  have hE : 0 ≤ SobolevEnergy.energy F u := energy_nonneg F u
  constructor
  · rintro (h | ⟨x, rfl⟩)
    · have h' : Real.sqrt (SobolevEnergy.energy F u) < b := h
      have := Real.sq_sqrt hE
      nlinarith [Real.sqrt_nonneg (SobolevEnergy.energy F u)]
    · rw [energy_constantSphereLoop]
      positivity
  · intro h
    left
    change Real.sqrt (SobolevEnergy.energy F u) < b
    exact (Real.sqrt_lt' hb).mpr h

variable {a b : ℝ}

/-- Sampling on the loops below b. -/
def sampleMap (hb : 0 < b) : C(lev F b, sub (PolygonDescent.energy F N) (b ^ 2)) :=
  ⟨fun u => ⟨samplePoly N (u : SphereLoop n),
      (polyEnergy_samplePoly_le (F := F) (N := N) (u : SphereLoop n)).trans_lt
        ((mem_lev_iff hb _).mp u.2)⟩,
    ((samplePoly_continuous N).comp continuous_subtype_val).subtype_mk _⟩

variable (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q < b ^ 2 → ShortPolygon M.δ q)

/-- The broken geodesic on the polygons of energy below b². -/
def brokenMap (hb : 0 < b) : C(sub (PolygonDescent.energy F N) (b ^ 2), lev F b) :=
  ⟨fun q => ⟨broken M ⟨(q : ZMod N → Sphere n), hshort _ q.2⟩,
      (mem_lev_iff hb _).mpr (by
        rw [energy_broken]
        exact q.2)⟩,
    ((broken_continuous M).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

theorem sample_brokenMap (hb : 0 < b) :
    (sampleMap (F := F) (N := N) hb).comp (brokenMap M hshort hb) =
      ContinuousMap.id (sub (PolygonDescent.energy F N) (b ^ 2)) := by
  refine ContinuousMap.ext fun q => Subtype.ext ?_
  exact sample_broken M ⟨(q : ZMod N → Sphere n), hshort _ q.2⟩

/-- The straightening homotopy from the broken geodesic of the samples to the loop. -/
def straighten (hb : 0 < b) (hbA : b ≤ A) :
    ((brokenMap M hshort hb).comp (sampleMap (F := F) (N := N) hb)).Homotopy
      (ContinuousMap.id (lev F b)) where
  toFun p := ⟨deform M (1 - (p.1 : ℝ), (p.2 : SphereLoop n)), (mem_lev_iff hb _).mpr
    ((energy_deform_le M (p := (1 - (p.1 : ℝ), (p.2 : SphereLoop n)))
      ⟨⟨sub_nonneg.mpr p.1.2.2, sub_le_self 1 p.1.2.1⟩,
        ((mem_lev_iff hb _).mp p.2.2).trans_le (pow_le_pow_left₀ hb.le hbA 2)⟩).trans_lt
      ((mem_lev_iff hb _).mp p.2.2))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hmap : Continuous fun p : _root_.unitInterval × lev F b =>
        ((1 - (p.1 : ℝ), (p.2 : SphereLoop n)) : ℝ × SphereLoop n) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)
    refine (deform_continuousOn M).comp_continuous hmap fun p => ?_
    exact ⟨⟨sub_nonneg.mpr p.1.2.2, sub_le_self 1 p.1.2.1⟩,
      ((mem_lev_iff hb _).mp p.2.2).trans_le (pow_le_pow_left₀ hb.le hbA 2)⟩
  map_zero_left u := by
    apply Subtype.ext
    have hu : SobolevEnergy.energy F (u : SphereLoop n) < A ^ 2 :=
      ((mem_lev_iff hb _).mp u.2).trans_le (pow_le_pow_left₀ hb.le hbA 2)
    change deform M (1 - ((0 : _root_.unitInterval) : ℝ), (u : SphereLoop n)) =
      broken M ⟨samplePoly N (u : SphereLoop n), _⟩
    rw [show ((0 : _root_.unitInterval) : ℝ) = 0 from rfl, sub_zero, deform_one M hu]
  map_one_left u := by
    apply Subtype.ext
    have hu : SobolevEnergy.energy F (u : SphereLoop n) < A ^ 2 :=
      ((mem_lev_iff hb _).mp u.2).trans_le (pow_le_pow_left₀ hb.le hbA 2)
    change deform M (1 - ((1 : _root_.unitInterval) : ℝ), (u : SphereLoop n)) = (u : SphereLoop n)
    rw [show ((1 : _root_.unitInterval) : ℝ) = 1 from rfl, sub_self, deform_zero M hu]

omit [NeZero N] in
theorem sub_sq_mono (hab : a ≤ b) (ha : 0 < a) :
    sub (PolygonDescent.energy F N) (a ^ 2) ⊆ sub (PolygonDescent.energy F N) (b ^ 2) :=
  fun _ hq => lt_of_lt_of_le hq (pow_le_pow_left₀ ha.le hab 2)

include hshort in
/-- Sampling is bijective on the cohomology of the crossing pairs: the cohomology of the
polygons of energy below b² relative to those below a² is that of (t_b, t_a). -/
theorem sample_bijective (ha : 0 < a) (hab : a ≤ b) (hbA : b ≤ A) (k : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (lev_mono F hab)
      (sub_sq_mono (F := F) (N := N) hab ha) (sampleMap (F := F) (N := N) (ha.trans_le hab))
      (fun u hu => (polyEnergy_samplePoly_le (F := F) (N := N) (u : SphereLoop n)).trans_lt
        ((mem_lev_iff ha _).mp hu)))) k) := by
  have hb : 0 < b := ha.trans_le hab
  refine bijective_Hmap_of_section (lev_mono F hab) (sub_sq_mono hab ha)
    (sampleMap (F := F) (N := N) hb) (brokenMap M hshort hb) _ ?_
    (sample_brokenMap M hshort hb) (straighten M hshort hb hbA) ?_ k
  · intro q hq
    refine (mem_lev_iff ha _).mpr ?_
    change SobolevEnergy.energy F (broken M ⟨(q : ZMod N → Sphere n), hshort _ q.2⟩) < a ^ 2
    rw [energy_broken]
    exact hq
  · intro τ u hu
    refine (mem_lev_iff ha _).mpr ?_
    have huA : SobolevEnergy.energy F (u : SphereLoop n) < A ^ 2 :=
      ((mem_lev_iff hb _).mp u.2).trans_le (pow_le_pow_left₀ hb.le hbA 2)
    exact (energy_deform_le M (p := (1 - (τ : ℝ), (u : SphereLoop n)))
      ⟨⟨sub_nonneg.mpr τ.2.2, sub_le_self 1 τ.2.1⟩, huA⟩).trans_lt ((mem_lev_iff ha _).mp hu)

omit [NeZero N] in
/-- Polygons of energy below b² are short when N is large. -/
theorem short_of_energy_lt {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hedge : ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n) (b : ℝ),
      polyEnergy F N (fun i => (q i : Ambient n)) ≤ b →
      ∀ j : ZMod N, N * (c * ‖(q (j + 1) : Ambient n) - q j‖ ^ 2) ≤ b)
    {N : ℕ} [NeZero N] (hbA : b ≤ A) (hb : 0 ≤ b) (hN : A ^ 2 / (c * δ ^ 2) < N)
    (q : ZMod N → Sphere n) (hq : PolygonDescent.energy F N q < b ^ 2) : ShortPolygon δ q := by
  intro j
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h1 := hedge N q (b ^ 2) hq.le j
  have h2 : b ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hb hbA 2
  have h3 : A ^ 2 < N * (c * δ ^ 2) := by
    rw [div_lt_iff₀ (by positivity)] at hN
    linarith
  have h4 : N * (c * ‖(q (j + 1) : Ambient n) - q j‖ ^ 2) < N * (c * δ ^ 2) := by linarith
  have h5 : ‖(q (j + 1) : Ambient n) - q j‖ ^ 2 < δ ^ 2 :=
    lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_left h4 hN0.le) hc.le
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h5

omit [NeZero N] in
/-- For all large N sampling is bijective on the cohomology of the crossing pairs below a given
level: the polygon crossing pairs have the cohomology of the loop pairs (t_b, t_a). -/
theorem exists_sample_bijective (F : ReversibleMetric n) (hn : 1 ≤ n) (A : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b), b ≤ A →
      ∀ k : ℕ, Function.Bijective (Hmap (trivHom (pairMapX (lev_mono F hab)
        (sub_sq_mono (F := F) (N := N) hab ha) (sampleMap (F := F) (N := N) (ha.trans_le hab))
        (fun u hu => (polyEnergy_samplePoly_le (F := F) (N := N) (u : SphereLoop n)).trans_lt
          ((mem_lev_iff ha _).mp hu)))) k) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := A) S.pos
  obtain ⟨c, hc, hedge⟩ := PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (A ^ 2 / (c * S.δ ^ 2))
  refine ⟨max N₁ N₂, fun N hN _ a b ha hab hbA k => ?_⟩
  have hNpos : 0 < N := NeZero.pos N
  let M : PolygonModelData F A N :=
    PolygonModelData.mk S fun u hu s t hs ht hst =>
      hN₁ N ((le_max_left _ _).trans hN) hNpos u hu s t hs ht hst
  have hNR : A ^ 2 / (c * S.δ ^ 2) < N :=
    hN₂.trans_le (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  exact sample_bijective M (fun q hq =>
    short_of_energy_lt hc S.pos hedge hbA (ha.le.trans hab) hNR q hq) ha hab hbA k

end

end Finsler.PolygonLoopPairs
