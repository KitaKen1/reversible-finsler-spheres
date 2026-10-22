module

public import Finsler.Geometry.PolygonRefineIndex
public import Finsler.Geometry.PolygonTypes

/-! Refinement and iteration. The refinement of the d-fold iterate of a short polygon is the
refinement of the polygon composed with the reduction of the indices, that is, the d-fold
iterate of the refinement after the identification of the residues modulo r (d N) with the
residues modulo d (r N). Hence, for a short polygon q without zero edges which is a critical
point of its coordinate energy and whose refinement q' is short without zero edges, the d-fold
iterates of q' and of q have the same index for every d ≥ 1: the index function of the iterates
is invariant under refinement. For a closed geodesic the index function of the polygon of
samples does not depend on the number of samples. The nullities of the iterates are not treated
here. -/

@[expose] public section

namespace Finsler.PolygonRefineIterate

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonRefine Finsler.PolygonChart Finsler.PolygonModel Finsler.SegmentAtlas
open Finsler.PolygonRefineIndex Finsler.PolygonHessian Finsler.PolygonIterate
open Finsler.PolygonIterateReduction Finsler.PolygonIndex Finsler.EnergySphereSmooth
open Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ}

/-! ### The index only depends on the polygon up to the identification of the indices -/

section Congr

variable {F : ReversibleMetric n}

/-- The index of equal polygons. -/
theorem index_congr {K : ℕ} [NeZero K] {q₁ q₂ : ZMod K → Sphere n} (e : q₁ = q₂)
    (hs₁ : (hessian F q₁).toLinearMap.IsSymmetric)
    (hs₂ : (hessian F q₂).toLinearMap.IsSymmetric) : index F q₁ hs₁ = index F q₂ hs₂ := by
  subst e
  rfl

/-- Relabelling the vertices by the identification of the residues modulo equal numbers does not
change the index. -/
theorem index_comp_congr {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    (q : ZMod K' → Sphere n)
    (hs : (hessian F (fun i => q (ZMod.ringEquivCongr h i))).toLinearMap.IsSymmetric)
    (hs' : (hessian F q).toLinearMap.IsSymmetric) :
    index F (fun i => q (ZMod.ringEquivCongr h i)) hs = index F q hs' := by
  subst h
  exact index_congr (funext fun i => by rw [ZMod.ringEquivCongr_refl_apply]) hs hs'

/-- The index function of the polygon of samples only depends on the number of samples. -/
theorem iterIndex_sample_congr (u : SphereLoop n) {K K' : ℕ} [NeZero K] [NeZero K']
    (h : K = K') (d : ℕ) :
    iterIndex F (samplePoly K u) d = iterIndex F (samplePoly K' u) d := by
  subst h
  rfl

end Congr

/-! ### The refinement of an iterate -/

section Refine

variable {F : ReversibleMetric n} (M : SegmentData F) (r N : ℕ) [NeZero r] [NeZero N]

/-- A polygon with r N vertices, repeated d times. -/
def pull (d : ℕ) (q' : ZMod (r * N) → Sphere n) : ZMod (r * (d * N)) → Sphere n :=
  fun i => q' (ZMod.castHom (Nat.mul_dvd_mul_left r (Dvd.intro_left d rfl)) (ZMod (r * N)) i)

omit [NeZero r] [NeZero N] in
theorem pull_short (d : ℕ) {δ : ℝ} {q' : ZMod (r * N) → Sphere n} (h : ShortPolygon δ q') :
    ShortPolygon δ (pull r N d q') := fun i => by
  unfold pull
  rw [map_add, map_one]
  exact h _

omit [NeZero r] [NeZero N] in
theorem pull_ne (d : ℕ) {q' : ZMod (r * N) → Sphere n} (h : ∀ i, q' (i + 1) ≠ q' i)
    (i : ZMod (r * (d * N))) : pull r N d q' (i + 1) ≠ pull r N d q' i := by
  unfold pull
  rw [map_add, map_one]
  exact h _

omit [NeZero r] [NeZero N] in
/-- The repeated polygon is the iterate after the identification of the indices. -/
theorem pull_eq (d : ℕ) (q' : ZMod (r * N) → Sphere n) (i : ZMod (r * (d * N))) :
    pull r N d q' i = iterate d (r * N) q'
      (ZMod.ringEquivCongr (show r * (d * N) = d * (r * N) by ring) i) := by
  have h := RingHom.ext_zmod
    (ZMod.castHom (Nat.mul_dvd_mul_left r (Dvd.intro_left d rfl)) (ZMod (r * N)))
    ((red d (r * N)).comp
      (ZMod.ringEquivCongr (show r * (d * N) = d * (r * N) by ring) :
        ZMod (r * (d * N)) →+* ZMod (d * (r * N))))
  exact congrArg q' (RingHom.congr_fun h i)

/-- **The refinement of an iterate.** The refinement of the d-fold iterate of a short polygon is
the refinement of the polygon repeated d times. -/
theorem refine_iterate (d : ℕ) [NeZero d] {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) :
    refine r (d * N) F M.seg (shortPolygon_iterate d N hq) =
      pull r N d (refine r N F M.seg hq) := by
  funext i
  have hr := Nat.pos_of_neZero r
  have hNpos := Nat.pos_of_neZero N
  have hj : i.val / r < d * N := Nat.div_lt_of_lt_mul (ZMod.val_lt i)
  have hs : i.val % r < r := Nat.mod_lt _ hr
  have hi : ((r * (i.val / r) + i.val % r : ℕ) : ZMod (r * (d * N))) = i := by
    rw [Nat.div_add_mod, ZMod.natCast_zmod_val]
  apply Subtype.ext
  have hL := refine_coe F M.seg r (d * N) (shortPolygon_iterate d N hq) hj hs
  rw [hi, iterate_natCast, iterate_natCast_add_one] at hL
  have hj'N : (i.val / r) % N < N := Nat.mod_lt _ hNpos
  have hR := refine_coe F M.seg r N hq hj'N hs
  rw [ZMod.natCast_mod] at hR
  have e : r * (i.val / r) = r * N * (i.val / r / N) + r * ((i.val / r) % N) := by
    rw [mul_assoc, ← mul_add, Nat.div_add_mod]
  have hcast : ZMod.castHom (Nat.mul_dvd_mul_left r (Dvd.intro_left d rfl)) (ZMod (r * N)) i =
      ((r * ((i.val / r) % N) + i.val % r : ℕ) : ZMod (r * N)) := by
    conv_lhs => rw [← hi]
    rw [map_natCast, e, Nat.cast_add, Nat.cast_add, Nat.cast_mul (r * N), ZMod.natCast_self,
      zero_mul, zero_add, ← Nat.cast_add]
  unfold pull
  rw [hL, hcast, hR]

section Critical

variable {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (hne : ∀ j, q (j + 1) ≠ q j)
  (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
    ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
  (hq' : ShortPolygon M.δ (refine r N F M.seg hq))
  (hne' : ∀ i, refine r N F M.seg hq (i + 1) ≠ refine r N F M.seg hq i)
  (hcrit : fderiv ℝ (energy F q) (base q) = 0)

include hne hpk hq' hne' hcrit in
/-- **The iterates of the refinement have the indices of the iterates of the polygon.** -/
theorem index_iterate_refine (d : ℕ) [NeZero d]
    (hs : (hessian F (iterate d N q)).toLinearMap.IsSymmetric)
    (hs' : (hessian F (iterate d (r * N) (refine r N F M.seg hq))).toLinearMap.IsSymmetric) :
    index F (iterate d (r * N) (refine r N F M.seg hq)) hs' = index F (iterate d N q) hs := by
  have hQ := shortPolygon_iterate d N hq
  have hQne := iterate_ne d N hne
  have hQpk : ∀ j : ZMod (d * N), ∃ T : SegChart F, iterate d N q j ∈ segDom T ∧
      ‖((iterate d N q (j + 1) : Sphere n) : Ambient n) -
        (iterate d N q j : Sphere n)‖ < T.δ := by
    intro j
    obtain ⟨T, hT, hTδ⟩ := hpk (red d N j)
    refine ⟨T, hT, ?_⟩
    rw [iterate_apply, iterate_apply, map_add, map_one]
    exact hTδ
  have hQcrit : fderiv ℝ (energy F (iterate d N q)) (base (iterate d N q)) = 0 :=
    (Hessian.gradient_eq_zero_iff _ _).mp
      (PolygonTypes.grad_iterate_eq_zero_of_grad F M.smooth hq hne d
        ((Hessian.gradient_eq_zero_iff _ _).mpr hcrit))
  have he := refine_iterate M r N d hq
  have hP := pull_short r N d hq'
  have hPne := pull_ne r N d hne'
  have hsP := hessian_isSymmetric F M.smooth hP hPne
  have h1 := index_eq_of_refine M r (d * N) hQ hQne hQpk he hP hPne hQcrit hs hsP
  have e : pull r N d (refine r N F M.seg hq) = fun i =>
      iterate d (r * N) (refine r N F M.seg hq)
        (ZMod.ringEquivCongr (show r * (d * N) = d * (r * N) by ring) i) :=
    funext fun i => pull_eq r N d _ i
  have hsX : (hessian F (fun i => iterate d (r * N) (refine r N F M.seg hq)
      (ZMod.ringEquivCongr (show r * (d * N) = d * (r * N) by ring) i))).toLinearMap.IsSymmetric := by
    rw [← e]
    exact hsP
  rw [← h1, index_congr e hsP hsX]
  exact (index_comp_congr _ _ hsX hs').symm

include hne hpk hq' hne' hcrit in
/-- **The index function is invariant under refinement.** -/
theorem iterIndex_refine {d : ℕ} (hd : 1 ≤ d) :
    iterIndex F (refine r N F M.seg hq) d = iterIndex F q d := by
  have : NeZero d := ⟨by omega⟩
  have hs := hessian_isSymmetric F M.smooth (shortPolygon_iterate d N hq) (iterate_ne d N hne)
  have hs' := hessian_isSymmetric F M.smooth (shortPolygon_iterate d (r * N) hq')
    (iterate_ne d (r * N) hne')
  rw [← iterIndex_eq F M.smooth hq' hne' d hs', ← iterIndex_eq F M.smooth hq hne d hs]
  exact index_iterate_refine M r N hq hne hpk hq' hne' hcrit d hs hs'

end Critical

end Refine

/-! ### Samples of a closed geodesic -/

section Samples

open Finsler.SmoothSobolev Finsler.PolygonGeodesic Finsler.GeodesicArcs

variable {F : ReversibleMetric n}

/-- **The index function of a closed geodesic does not depend on the number of samples.** There
is N₀ such that for all N, N' ≥ N₀ the d-fold iterates of the polygons of N and of N' samples
have the same index, for every d ≥ 1. -/
theorem exists_iterIndex_sample_eq (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N N' : ℕ, N₀ ≤ N → N₀ ≤ N' → ∀ [NeZero N] [NeZero N'] (d : ℕ), 1 ≤ d →
      iterIndex F (samplePoly N' (ofSmooth g.loop)) d =
        iterIndex F (samplePoly N (ofSmooth g.loop)) d := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨δa, hδa, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  obtain ⟨N₁, hN₁⟩ := polyCritical_of_closedGeodesic F (lt_min M.pos hδa)
    (fun P Q hne h => M.smooth P Q hne (h.trans_le (min_le_left _ _))) g
  obtain ⟨N₂, hN₂⟩ := broken_sample_closedGeodesic M g
  obtain ⟨h₀, hh₀, hscale⟩ := exists_arc_scale (F := F) (γ := g.loop)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (1 / h₀)
  have hfacts : ∀ K : ℕ, max N₁ (max N₂ (N₃ + 1)) ≤ K → ∀ [NeZero K],
      ShortPolygon M.δ (samplePoly K (ofSmooth g.loop)) ∧
      (∀ i, samplePoly K (ofSmooth g.loop) (i + 1) ≠ samplePoly K (ofSmooth g.loop) i) ∧
      (∀ j : ZMod K, ∃ T : SegChart F, samplePoly K (ofSmooth g.loop) j ∈ segDom T ∧
        ‖(samplePoly K (ofSmooth g.loop) (j + 1) : Ambient n) -
          samplePoly K (ofSmooth g.loop) j‖ < T.δ) ∧
      fderiv ℝ (energy F (samplePoly K (ofSmooth g.loop)))
        (base (samplePoly K (ofSmooth g.loop))) = 0 ∧
      (∀ hq : ShortPolygon M.δ (samplePoly K (ofSmooth g.loop)),
        polySphereLoop F M.seg hq = ofSmooth g.loop) := by
    intro K hK _
    have hK1 : N₁ ≤ K := (le_max_left _ _).trans hK
    have hK2 : N₂ ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
    have hK3 : N₃ + 1 ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans hK
    obtain ⟨hshort, hc, -⟩ := hN₁ K hK1
    have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_neZero K
    have hlt : 1 / (K : ℝ) < h₀ := by
      have h1 : 1 / h₀ < K := hN₃.trans (by exact_mod_cast hK3)
      rw [div_lt_iff₀ hKpos]
      rw [div_lt_iff₀ hh₀] at h1
      linarith
    have hq : ShortPolygon M.δ (samplePoly K (ofSmooth g.loop)) := fun i =>
      (hshort i).trans_le (min_le_left _ _)
    have hqa : ShortPolygon δa (samplePoly K (ofSmooth g.loop)) := fun i =>
      (hshort i).trans_le (min_le_right _ _)
    have hne : ∀ i, samplePoly K (ofSmooth g.loop) (i + 1) ≠
        samplePoly K (ofSmooth g.loop) i := fun i => samplePoly_ofSmooth_ne g hscale hlt i
    refine ⟨hq, hne, fun j => ?_,
      fderiv_energy_eq_zero_of_polyCritical F M.smooth hq hne hc, fun hq' => hN₂ K hK2 hq'⟩
    obtain ⟨P₀, hP₀, hP⟩ := hcover (samplePoly K (ofSmooth g.loop) j)
    exact ⟨S P₀, hP, (hqa j).trans_le (hδS P₀ hP₀)⟩
  -- refinement by r of the polygon of K samples
  have hmul : ∀ K : ℕ, max N₁ (max N₂ (N₃ + 1)) ≤ K → ∀ [NeZero K] (r : ℕ) [NeZero r] (d : ℕ),
      1 ≤ d → iterIndex F (samplePoly (r * K) (ofSmooth g.loop)) d =
        iterIndex F (samplePoly K (ofSmooth g.loop)) d := by
    intro K hK _ r _ d hd
    obtain ⟨hq, hne, hpk, hcrit, hbr⟩ := hfacts K hK
    have hrK : max N₁ (max N₂ (N₃ + 1)) ≤ r * K :=
      hK.trans (Nat.le_mul_of_pos_left K (Nat.pos_of_neZero r))
    obtain ⟨hq', hne', -, -, -⟩ := hfacts (r * K) hrK
    have he : refine r K F M.seg hq = samplePoly (r * K) (ofSmooth g.loop) := by
      unfold refine
      rw [hbr hq]
    have h := iterIndex_refine M r K hq hne hpk (by rw [he]; exact hq')
      (by rw [he]; exact hne') hcrit hd
    rw [he] at h
    exact h
  refine ⟨max N₁ (max N₂ (N₃ + 1)), fun N N' hN hN' _ _ d hd => ?_⟩
  rw [← hmul N' hN' N d hd, ← hmul N hN N' d hd]
  exact iterIndex_sample_congr (ofSmooth g.loop) (Nat.mul_comm N N') d

end Samples

end

end Finsler.PolygonRefineIterate
