module

public import Finsler.Geometry.PhaseNullity
public import Finsler.Algebra.ChainPositive

/-! The nullities of the iterates do not depend on the number of samples. For a short polygon
without zero edges with the twist condition whose number of vertices is divisible by 2 r, if
the form of the Hessian is nonnegative on the vectors vanishing at the vertices with index
divisible by 2 r, it is positive on the nonzero vectors vanishing at the vertices with index
divisible by r: the complement consists of chains of r - 1 vertices one of whose ends is not
divisible by 2 r. Nonnegativity is transported along identifications of the indices, and the
twist condition passes to polygons composed with a ring homomorphism of the indices. For the
samples of a loop with the sample facts, the polygon of 2 r N samples repeated d times is the
refinement of order 2 r of the d-fold iterate of the polygon of N samples, which gives the
nonnegativity, and it is the refinement of order r of the iterate of the polygon of 2 N
samples; hence the d-fold iterates of the polygons of r (2 N) and of 2 N samples have the same
nullity, for every r ≥ 1. With the independence of the phase: for a closed geodesic the
nullities of all iterates of the polygons of 2 N samples at all phases are the same for all
large N. -/

@[expose] public section

namespace Finsler.PolygonRefineGeneral

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonRefine Finsler.PolygonChart Finsler.PolygonModel Finsler.SegmentAtlas
open Finsler.PolygonRefineIndex Finsler.PolygonHessian Finsler.PolygonIterate
open Finsler.PolygonIterateReduction Finsler.PolygonNullity Finsler.PolygonMonodromy
open Finsler.PolygonRefineIterate Finsler.PolygonRefineNullity Finsler.EnergySphereSmooth
open Finsler.PolygonRefineIterateNullity Finsler.SmoothSobolev Finsler.SamplePhase
open Finsler.PhaseNullity
open Set Filter
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### Positivity on the vectors vanishing at the multiples of r -/

section Jacobi

variable {K : ℕ} [NeZero K] (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod K → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- **Positivity between the multiples of r.** If the number of vertices is divisible by 2 r and
the form of the Hessian is nonnegative on the vectors vanishing at the vertices with index
divisible by 2 r, then it is positive on the nonzero vectors vanishing at the vertices with
index divisible by r. -/
theorem hessian_pos_of_nonneg_mul {r : ℕ} (hr : 0 < r) (h2r : 2 * r ∣ K) (htw : Twist F q)
    (hpsd : ∀ z : Model n K, (∀ i : ZMod K, i.val % (2 * r) = 0 → z i = 0) →
      0 ≤ ⟪hessian F q z, z⟫)
    {u : Model n K} (hu : ∀ i : ZMod K, i.val % r = 0 → u i = 0) (hu0 : u ≠ 0) :
    0 < ⟪hessian F q u, u⟫ := by
  have hKpos := Nat.pos_of_neZero K
  have h2rK : 2 * r ≤ K := Nat.le_of_dvd hKpos h2r
  have hrK : r < K := by omega
  have hrdvd : r ∣ K := (Dvd.intro_left 2 rfl).trans h2r
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hval : ∀ {m : ℕ}, m ∣ K → ∀ a : ℕ, ((a : ZMod K)).val % m = a % m := by
    intro m hm a
    rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ hm]
  refine ChainPositive.inner_pos (hessian F q).toLinearMap
    (fun i => (Tmap F q i).toLinearMap) (fun i => (Amap F q i).toLinearMap)
    (fun i => (Bmap F q i).toLinearMap) (c := (K : ℝ))
    (fun w i => hessian_apply F hδ hq hne w i) (hessian_isSymmetric F hδ hq hne) hKR
    {i : ZMod K | i.val % (2 * r) = 0} hpsd (fun i => Bmap_injective F hδ hq hne htw i)
    (fun i => Tmap_injective F hδ hq hne htw i) {i : ZMod K | i.val % r = 0} ?_ ?_ hu hu0
  · intro i hi
    have hi' : i.val % (2 * r) = 0 := hi
    exact Nat.mod_eq_zero_of_dvd ((Dvd.intro_left 2 rfl).trans (Nat.dvd_of_mod_eq_zero hi'))
  · intro i hi
    have hi' : i.val % r ≠ 0 := hi
    have ha : r * (i.val / r) + i.val % r = i.val := Nat.div_add_mod i.val r
    have hs₀r : i.val % r < r := Nat.mod_lt _ hr
    have hicast : ((i.val : ℕ) : ZMod K) = i := ZMod.natCast_zmod_val i
    have hb2 := Nat.div_add_mod (i.val / r) 2
    rcases Nat.mod_two_eq_zero_or_one (i.val / r) with hb | hb
    · -- the chain ends at the next multiple of r, which is not a multiple of 2 r
      rw [hb, add_zero] at hb2
      have hstep : (i.val / r + 1) * r = r * (i.val / r) + r := by ring
      refine ⟨(((i.val / r + 1) * r : ℕ) : ZMod K), r, r - i.val % r, by omega, hrK, ?_,
        Or.inl ⟨?_, ?_, ?_⟩⟩
      · change ((((i.val / r + 1) * r : ℕ) : ZMod K)).val % r = 0
        rw [hval hrdvd, Nat.mul_mod_left]
      · have h1 : (i.val / r + 1) * r = i.val + (r - i.val % r) := by omega
        rw [h1, Nat.cast_add, hicast, add_sub_cancel_right]
      · have h1 : ((((i.val / r + 1) * r : ℕ) : ZMod K)) - (r : ZMod K) =
            ((r * (i.val / r) : ℕ) : ZMod K) := by
          rw [hstep, Nat.cast_add, add_sub_cancel_right]
        change ((((i.val / r + 1) * r : ℕ) : ZMod K) - (r : ZMod K)).val % r = 0
        rw [h1, hval hrdvd, Nat.mul_mod_right]
      · intro t ht
        have hle : t ≤ (i.val / r + 1) * r := by omega
        have h1 : ((((i.val / r + 1) * r : ℕ) : ZMod K)) - (t : ZMod K) =
            (((i.val / r + 1) * r - t : ℕ) : ZMod K) := (Nat.cast_sub hle).symm
        have h2 : (i.val / r + 1) * r - t = (r - t) + (i.val / r / 2) * (2 * r) := by
          have h3 : (i.val / r + 1) * r = (i.val / r / 2) * (2 * r) + r := by
            have h4 : (i.val / r + 1) * r = (2 * (i.val / r / 2) + 1) * r := by rw [hb2]
            rw [h4]
            ring
          omega
        change ¬ ((((i.val / r + 1) * r : ℕ) : ZMod K) - (t : ZMod K)).val % (2 * r) = 0
        rw [h1, hval h2r, h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        omega
    · -- the chain starts at the previous multiple of r, which is not a multiple of 2 r
      rw [hb] at hb2
      refine ⟨((r * (i.val / r) : ℕ) : ZMod K), r, i.val % r, hs₀r, hrK, ?_,
        Or.inr ⟨?_, ?_, ?_⟩⟩
      · change (((r * (i.val / r) : ℕ) : ZMod K)).val % r = 0
        rw [hval hrdvd, Nat.mul_mod_right]
      · rw [← Nat.cast_add, ha, hicast]
      · change (((r * (i.val / r) : ℕ) : ZMod K) + (r : ZMod K)).val % r = 0
        rw [← Nat.cast_add, hval hrdvd, Nat.add_mod_right, Nat.mul_mod_right]
      · intro t ht
        have h2 : r * (i.val / r) + t = (r + t) + (i.val / r / 2) * (2 * r) := by
          have h3 : r * (i.val / r) = (i.val / r / 2) * (2 * r) + r := by
            have h4 : r * (i.val / r) = r * (2 * (i.val / r / 2) + 1) := by rw [hb2]
            rw [h4]
            ring
          omega
        change ¬ (((r * (i.val / r) : ℕ) : ZMod K) + (t : ZMod K)).val % (2 * r) = 0
        rw [← Nat.cast_add, hval h2r, h2, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
        omega

end Jacobi

/-! ### Identification of the indices and composition with ring homomorphisms -/

section Congr

variable {F : ReversibleMetric n}

/-- The samples only depend on the number of samples. -/
theorem samplePoly_congr (u : SphereLoop n) {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    (x : ZMod K) : samplePoly K u x = samplePoly K' u (ZMod.ringEquivCongr h x) := by
  subst h
  rw [ZMod.ringEquivCongr_refl_apply]

/-- Nonnegativity on the vectors vanishing at the vertices with index divisible by R is
transported along an identification of the indices. -/
theorem nonneg_comp_congr {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    {q : ZMod K → Sphere n} {q' : ZMod K' → Sphere n}
    (hqq : ∀ i, q i = q' (ZMod.ringEquivCongr h i)) (R : ℕ)
    (hpsd : ∀ z : Model n K', (∀ i : ZMod K', i.val % R = 0 → z i = 0) →
      0 ≤ ⟪hessian F q' z, z⟫) :
    ∀ z : Model n K, (∀ i : ZMod K, i.val % R = 0 → z i = 0) → 0 ≤ ⟪hessian F q z, z⟫ := by
  subst h
  have e : q = q' := funext fun i => by rw [hqq i, ZMod.ringEquivCongr_refl_apply]
  subst e
  exact hpsd

/-- The nullities of the iterates of the samples only depend on the number of samples. -/
theorem nullity_iterate_sample_congr (u : SphereLoop n) {K K' : ℕ} [NeZero K] [NeZero K']
    (h : K = K') (d : ℕ) [NeZero d] :
    nullity F (iterate d K (samplePoly K u)) = nullity F (iterate d K' (samplePoly K' u)) := by
  subst h
  rfl

/-- The twist condition passes to a polygon composed with a ring homomorphism of the
indices. -/
theorem twist_comp {K K₀ : ℕ} (φ : ZMod K →+* ZMod K₀) {q : ZMod K₀ → Sphere n}
    (htw : Twist F q) : Twist F (fun i => q (φ i)) := by
  intro j v hv
  refine htw (φ j) v fun η => ?_
  have h := hv η
  rw [pairE_comp, edgeL_base_comp] at h
  exact h

end Congr

/-! ### Refinement of order r of the iterates -/

section Refine

variable {F : ReversibleMetric n} (M : SegmentData F) (r N : ℕ) [NeZero r] [NeZero N]
  {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (hne : ∀ j, q (j + 1) ≠ q j)
  (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
    ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
  (hq' : ShortPolygon M.δ (refine r N F M.seg hq))
  (hne' : ∀ i, refine r N F M.seg hq (i + 1) ≠ refine r N F M.seg hq i)
  (hcrit : fderiv ℝ (energy F q) (base q) = 0)

include hne hpk hq' hne' hcrit in
/-- **The nullities of the iterates under refinement of order r.** If the refinement has the
twist condition, the number of vertices of its d-fold repetition is divisible by 2 r, and the
form of the Hessian of the repetition is nonnegative on the vectors vanishing at the vertices
with index divisible by 2 r, the d-fold iterates of the refinement and of the polygon have the
same nullity. -/
theorem nullity_iterate_refine_of_nonneg (d : ℕ) [NeZero d]
    (htw : Twist F (refine r N F M.seg hq)) (h2r : 2 * r ∣ r * (d * N))
    (hpsd : ∀ z : Model n (r * (d * N)),
      (∀ i : ZMod (r * (d * N)), i.val % (2 * r) = 0 → z i = 0) →
      0 ≤ ⟪hessian F (pull r N d (refine r N F M.seg hq)) z, z⟫) :
    nullity F (iterate d (r * N) (refine r N F M.seg hq)) = nullity F (iterate d N q) := by
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
  have hPtw : Twist F (pull r N d (refine r N F M.seg hq)) :=
    twist_comp (ZMod.castHom (Nat.mul_dvd_mul_left r (Dvd.intro_left d rfl)) (ZMod (r * N))) htw
  have h1 := nullity_refine_of_pos M r (d * N) hQ hQne hQpk he hP hPne hQcrit fun u hu hu0 =>
    hessian_pos_of_nonneg_mul F M.smooth hP hPne (Nat.pos_of_neZero r) h2r hPtw hpsd
      (fun i hi => eq_zero_of_coarseL r (d * N) hu i hi) hu0
  have e : pull r N d (refine r N F M.seg hq) = fun i =>
      iterate d (r * N) (refine r N F M.seg hq)
        (ZMod.ringEquivCongr (show r * (d * N) = d * (r * N) by ring) i) :=
    funext fun i => pull_eq r N d _ i
  rw [← h1, e]
  exact (nullity_comp_congr _ _).symm

end Refine

/-! ### Samples -/

section Samples

variable {F : ReversibleMetric n}

/-- **Refinement of order r from the sample facts.** If the polygons of N, 2 N, r (2 N) and
2 r N samples of a loop have the sample facts, the d-fold iterates of the polygons of r (2 N)
and of 2 N samples have the same nullity. -/
theorem nullity_iterate_mul_of_facts (M : SegmentData F) (u : SphereLoop n) (r N : ℕ)
    [NeZero r] [NeZero N] (h₀ : SampleFacts M u N) (h₁ : SampleFacts M u (2 * N))
    (hf : SampleFacts M u (r * (2 * N))) (hf' : SampleFacts M u (2 * r * N)) (d : ℕ)
    [NeZero d] :
    nullity F (iterate d (r * (2 * N)) (samplePoly (r * (2 * N)) u)) =
      nullity F (iterate d (2 * N) (samplePoly (2 * N) u)) := by
  obtain ⟨hq₀, hne₀, hpk₀, -, -, hcrit₀, hbr₀⟩ := h₀
  obtain ⟨hq₁, hne₁, hpk₁, -, -, hcrit₁, hbr₁⟩ := h₁
  obtain ⟨hqf, hnef, -, htwf, -, -, -⟩ := hf
  obtain ⟨hqf', hnef', -, -, -, -, -⟩ := hf'
  -- the fine polygon as refinements
  have he₁ : refine r (2 * N) F M.seg hq₁ = samplePoly (r * (2 * N)) u := by
    unfold refine
    rw [hbr₁ hq₁]
  have he₀ : refine (2 * r) N F M.seg hq₀ = samplePoly (2 * r * N) u := by
    unfold refine
    rw [hbr₀ hq₀]
  -- nonnegativity for the repetition of the polygon of 2 r N samples
  have hQ₀ := shortPolygon_iterate d N hq₀
  have hQ₀ne := iterate_ne d N hne₀
  have hQ₀pk : ∀ j : ZMod (d * N), ∃ T : SegChart F, iterate d N (samplePoly N u) j ∈ segDom T ∧
      ‖((iterate d N (samplePoly N u) (j + 1) : Sphere n) : Ambient n) -
        (iterate d N (samplePoly N u) j : Sphere n)‖ < T.δ := by
    intro j
    obtain ⟨T, hT, hTδ⟩ := hpk₀ (red d N j)
    refine ⟨T, hT, ?_⟩
    rw [iterate_apply, iterate_apply, map_add, map_one]
    exact hTδ
  have hQ₀crit : fderiv ℝ (energy F (iterate d N (samplePoly N u)))
      (base (iterate d N (samplePoly N u))) = 0 :=
    (Hessian.gradient_eq_zero_iff _ _).mp
      (PolygonTypes.grad_iterate_eq_zero_of_grad F M.smooth hq₀ hne₀ d
        ((Hessian.gradient_eq_zero_iff _ _).mpr hcrit₀))
  have heit : refine (2 * r) (d * N) F M.seg hQ₀ =
      pull (2 * r) N d (samplePoly (2 * r * N) u) := by
    rw [refine_iterate M (2 * r) N d hq₀, he₀]
  have hpsd' : ∀ z : Model n (2 * r * (d * N)),
      (∀ i : ZMod (2 * r * (d * N)), i.val % (2 * r) = 0 → z i = 0) →
      0 ≤ ⟪hessian F (pull (2 * r) N d (samplePoly (2 * r * N) u)) z, z⟫ := fun z hz =>
    hessian_nonneg_of_coarse M (2 * r) (d * N) hQ₀ hQ₀ne hQ₀pk heit
      (pull_short (2 * r) N d hqf') (pull_ne (2 * r) N d hnef') hQ₀crit
      (coarseL_eq_zero (2 * r) (d * N) hz)
  -- transport to the repetition of the polygon of r (2 N) samples
  have hK : r * (d * (2 * N)) = 2 * r * (d * N) := by ring
  have hK₀ : r * (2 * N) = 2 * r * N := by ring
  have hqq : ∀ i : ZMod (r * (d * (2 * N))),
      pull r (2 * N) d (samplePoly (r * (2 * N)) u) i =
        pull (2 * r) N d (samplePoly (2 * r * N) u) (ZMod.ringEquivCongr hK i) := by
    intro i
    have hhom := RingHom.ext_zmod
      ((ZMod.ringEquivCongr hK₀ : ZMod (r * (2 * N)) →+* ZMod (2 * r * N)).comp
        (ZMod.castHom (Nat.mul_dvd_mul_left r (Dvd.intro_left d rfl)) (ZMod (r * (2 * N)))))
      ((ZMod.castHom (Nat.mul_dvd_mul_left (2 * r) (Dvd.intro_left d rfl))
          (ZMod (2 * r * N))).comp
        (ZMod.ringEquivCongr hK : ZMod (r * (d * (2 * N))) →+* ZMod (2 * r * (d * N))))
    unfold pull
    rw [samplePoly_congr u hK₀]
    exact congrArg (samplePoly (2 * r * N) u) (RingHom.congr_fun hhom i)
  have hpsd := nonneg_comp_congr hK hqq (2 * r) hpsd'
  have h2r : 2 * r ∣ r * (d * (2 * N)) := ⟨d * N, by ring⟩
  have h := nullity_iterate_refine_of_nonneg M r (2 * N) hq₁ hne₁ hpk₁
    (by rw [he₁]; exact hqf) (by rw [he₁]; exact hnef) hcrit₁ d
    (by rw [he₁]; exact htwf) h2r (by rw [he₁]; exact hpsd)
  rw [he₁] at h
  exact h

/-- **The nullities of the iterates of the samples of a closed geodesic do not depend on the
number of samples nor on the phase.** For a closed geodesic there is N₀ such that for all
N₁, N₂ ≥ N₀, all d ≥ 1 and all real phases a, a', the d-fold iterates of the polygons of 2 N₁
samples at the phase a and of 2 N₂ samples at the phase a' have the same nullity. -/
theorem exists_nullity_sample_invariance (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N₁ N₂ : ℕ, N₀ ≤ N₁ → N₀ ≤ N₂ → ∀ [NeZero N₁] [NeZero N₂] (d : ℕ) [NeZero d]
      (a a' : ℝ),
      nullity F (iterate d (2 * N₁)
          (samplePoly (2 * N₁) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
        nullity F (iterate d (2 * N₂)
          (samplePoly (2 * N₂) (ofSmooth (Finsler.Loops.shift g.loop a')))) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all M g
  obtain ⟨K₁, hK₁⟩ := exists_phase_invariance g
  refine ⟨max K₀ K₁, fun N₁ N₂ hN₁ hN₂ _ _ d _ a a' => ?_⟩
  have h1 : K₀ ≤ N₁ := (le_max_left _ _).trans hN₁
  have h2 : K₀ ≤ N₂ := (le_max_left _ _).trans hN₂
  have hpos₁ := Nat.pos_of_neZero N₁
  have hpos₂ := Nat.pos_of_neZero N₂
  have hmul : ∀ (r N : ℕ) [NeZero r] [NeZero N], K₀ ≤ N →
      nullity F (iterate d (r * (2 * N))
          (samplePoly (r * (2 * N)) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
        nullity F (iterate d (2 * N)
          (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) := by
    intro r N _ _ hN
    have hr := Nat.pos_of_neZero r
    have hN2 : K₀ ≤ 2 * N := hN.trans (Nat.le_mul_of_pos_left N two_pos)
    have hrN : K₀ ≤ r * (2 * N) := hN2.trans (Nat.le_mul_of_pos_left (2 * N) hr)
    have hrN' : K₀ ≤ 2 * r * N := hN.trans (Nat.le_mul_of_pos_left N (by omega))
    exact nullity_iterate_mul_of_facts M _ r N (hK₀ a N hN) (hK₀ a (2 * N) hN2)
      (hK₀ a (r * (2 * N)) hrN) (hK₀ a (2 * r * N) hrN') d
  have e1 := hmul N₂ N₁ h1
  have e2 := hmul N₁ N₂ h2
  have e3 := nullity_iterate_sample_congr (F := F)
    (ofSmooth (Finsler.Loops.shift g.loop a)) (show N₂ * (2 * N₁) = N₁ * (2 * N₂) by ring) d
  have e4 := (hK₁ N₂ ((le_max_right _ _).trans hN₂) d a a').1
  rw [← e1, e3, e2, e4]

end Samples

end

end Finsler.PolygonRefineGeneral
