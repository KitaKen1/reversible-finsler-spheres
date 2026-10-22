module

public import Finsler.Geometry.PolygonRefineIterate
public import Finsler.Geometry.PolygonRefineNullity

/-! The nullities of the iterates when the number of vertices is doubled. The coefficients of the
Jacobi form of the Hessian of a polygon composed with a ring homomorphism of the indices are the
coefficients of the polygon at the image index. If the number of vertices is even and the
diagonal coefficients at the odd vertices are positive definite, the form of the Hessian is
positive on the nonzero vectors vanishing at the even vertices; under the hypotheses of the
doubling theorem the diagonal coefficients at the odd vertices of the refinement are positive
definite. Since the iterates of the refinement have the same diagonal coefficients, the d-fold
iterates of the refinement of order two and of the polygon have the same nullity for every d.
For a closed geodesic, the iterates of the polygons of 4 N and of 2 N samples have the same
nullities for all large N. -/

@[expose] public section

namespace Finsler.PolygonRefineIterateNullity

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonRefine Finsler.PolygonChart Finsler.PolygonModel Finsler.SegmentAtlas
open Finsler.PolygonRefineIndex Finsler.PolygonHessian Finsler.PolygonIterate
open Finsler.PolygonIterateReduction Finsler.PolygonNullity Finsler.PolygonMonodromy
open Finsler.PolygonRefineIterate Finsler.PolygonRefineNullity Finsler.EnergySphereSmooth
open Set Filter
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### Polygons composed with a ring homomorphism of the indices -/

section Comp

variable {K K₀ : ℕ} (φ : ZMod K →+* ZMod K₀) (F : ReversibleMetric n) (q : ZMod K₀ → Sphere n)

theorem pairE_comp (j : ZMod K) : pairE F (fun i => q (φ i)) j = pairE F q (φ j) := by
  funext z
  change ambientMinEnergy F (inverseAmbient (q (φ j)) z.1, inverseAmbient (q (φ (j + 1))) z.2) =
    ambientMinEnergy F (inverseAmbient (q (φ j)) z.1, inverseAmbient (q (φ j + 1)) z.2)
  rw [map_add, map_one]

theorem edgeL_base_comp (j : ZMod K) :
    edgeL j (base (fun i => q (φ i))) = edgeL (φ j) (base q) := by
  change (base q (φ j), base q (φ (j + 1))) = (base q (φ j), base q (φ j + 1))
  rw [map_add, map_one]

theorem hess2_comp (j : ZMod K) : hess2 F (fun i => q (φ i)) j = hess2 F q (φ j) := by
  rw [hess2, hess2, pairE_comp, edgeL_base_comp]

/-- The diagonal coefficient of the composed polygon. -/
theorem Amap_comp (j : ZMod K) : Amap F (fun i => q (φ i)) j = Amap F q (φ j) := by
  rw [Amap, Amap, hess2_comp, hess2_comp, map_sub, map_one]

end Comp

/-! ### Positivity from the diagonal coefficients -/

section Diagonal

variable {K : ℕ} [NeZero K] (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod K → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- If the number of vertices is even and the diagonal coefficients at the odd vertices are
positive definite, the form of the Hessian is positive on the nonzero vectors vanishing at the
even vertices. -/
theorem hessian_pos_of_diag (h2 : 2 ∣ K)
    (hA : ∀ i : ZMod K, i.val % 2 ≠ 0 → ∀ a : Coordinates n, a ≠ 0 → 0 < ⟪Amap F q i a, a⟫)
    {u : Model n K} (hu : ∀ i : ZMod K, i.val % 2 = 0 → u i = 0) (hu0 : u ≠ 0) :
    0 < ⟪hessian F q u, u⟫ := by
  have hK2 : 2 ≤ K := Nat.le_of_dvd (Nat.pos_of_neZero K) h2
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_neZero K
  have hsucc : ∀ j : ZMod K, (j + 1).val % 2 = (j.val + 1) % 2 := by
    intro j
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < K),
      Nat.mod_mod_of_dvd _ h2]
  have hterm : ∀ i : ZMod K, ⟪hessian F q u i, u i⟫ = K * ⟪Amap F q i (u i), u i⟫ := by
    intro i
    by_cases hi : i.val % 2 = 0
    · rw [hu i hi, inner_zero_right, inner_zero_right, mul_zero]
    · have h1 := hsucc i
      have h3 := hsucc (i - 1)
      rw [sub_add_cancel] at h3
      rw [hessian_apply F hδ hq hne, hu (i + 1) (by omega), hu (i - 1) (by omega), map_zero,
        map_zero, zero_add, add_zero, real_inner_smul_left]
  have hnonneg : ∀ i : ZMod K, 0 ≤ (K : ℝ) * ⟪Amap F q i (u i), u i⟫ := by
    intro i
    by_cases hi : i.val % 2 = 0
    · rw [hu i hi, inner_zero_right, mul_zero]
    · by_cases h0 : u i = 0
      · rw [h0, inner_zero_right, mul_zero]
      · exact (mul_pos hKpos (hA i hi _ h0)).le
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra hall
    exact hu0 (PiLp.ext fun i => by
      by_contra h
      exact hall ⟨i, h⟩)
  have hi₀odd : i₀.val % 2 ≠ 0 := fun h => hi₀ (hu i₀ h)
  rw [PiLp.inner_apply]
  simp only [hterm]
  exact Finset.sum_pos' (fun i _ => hnonneg i)
    ⟨i₀, Finset.mem_univ _, mul_pos hKpos (hA i₀ hi₀odd _ hi₀)⟩

include hδ hq hne in
/-- **Positivity of the diagonal coefficients at the odd vertices**, if the number of vertices is
divisible by 4 and the form of the Hessian is nonnegative on the vectors vanishing at the
vertices with index divisible by 4. -/
theorem Amap_pos_of_nonneg (h4 : 4 ∣ K) (htw : Twist F q)
    (hpsd : ∀ z : Model n K, (∀ i : ZMod K, i.val % 4 = 0 → z i = 0) →
      0 ≤ ⟪hessian F q z, z⟫)
    {i : ZMod K} (hi : i.val % 2 ≠ 0) {a : Coordinates n} (ha : a ≠ 0) :
    0 < ⟪Amap F q i a, a⟫ := by
  have hK4 : 4 ≤ K := Nat.le_of_dvd (Nat.pos_of_neZero K) h4
  have h10 : (1 : ZMod K) ≠ 0 := fun h => hne 0 (by rw [zero_add, h])
  have h20 : (2 : ZMod K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod K) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_neZero K
  have hsucc : ∀ j : ZMod K, (j + 1).val % 4 = (j.val + 1) % 4 := by
    intro j
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < K),
      Nat.mod_mod_of_dvd _ h4]
  have h1 := hsucc i
  have h3 := hsucc (i - 1)
  rw [sub_add_cancel] at h3
  have hiS : i ∉ {i : ZMod K | i.val % 4 = 0} := by
    change ¬ i.val % 4 = 0
    omega
  have hn : i + 1 ∉ {i : ZMod K | i.val % 4 = 0} ∨ i - 1 ∉ {i : ZMod K | i.val % 4 = 0} := by
    change ¬ (i + 1).val % 4 = 0 ∨ ¬ (i - 1).val % 4 = 0
    omega
  exact JacobiPositive.diag_pos (hessian F q).toLinearMap
    (fun i => (Tmap F q i).toLinearMap) (fun i => (Amap F q i).toLinearMap)
    (fun i => (Bmap F q i).toLinearMap) (c := (K : ℝ))
    (fun w i => hessian_apply F hδ hq hne w i) h10 h20 (hessian_isSymmetric F hδ hq hne) hKpos
    {i : ZMod K | i.val % 4 = 0} hpsd (fun i => Tmap_injective F hδ hq hne htw i)
    (fun i => Bmap_injective F hδ hq hne htw i) hiS hn ha

end Diagonal

/-! ### The nullities of the iterates -/

section Congr

variable {F : ReversibleMetric n}

/-- Relabelling the vertices by the identification of the residues modulo equal numbers does not
change the nullity. -/
theorem nullity_comp_congr {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    (q : ZMod K' → Sphere n) :
    nullity F (fun i => q (ZMod.ringEquivCongr h i)) = nullity F q := by
  subst h
  have e : (fun i => q (ZMod.ringEquivCongr rfl i)) = q :=
    funext fun i => by rw [ZMod.ringEquivCongr_refl_apply]
  exact congrArg (fun p : ZMod K → Sphere n => nullity F p) e

end Congr

section Double

variable {F : ReversibleMetric n} (M : SegmentData F) (N : ℕ) [NeZero N]
  {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (hne : ∀ j, q (j + 1) ≠ q j)
  (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
    ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
  (hq' : ShortPolygon M.δ (refine 2 N F M.seg hq))
  (hne' : ∀ i, refine 2 N F M.seg hq (i + 1) ≠ refine 2 N F M.seg hq i)
  (hcrit : fderiv ℝ (energy F q) (base q) = 0)

include hne hpk hq' hne' hcrit in
/-- **The nullities of the iterates when the number of vertices is doubled.** If the diagonal
coefficients of the refinement of order two at the odd vertices are positive definite, the
d-fold iterates of the refinement and of the polygon have the same nullity. -/
theorem nullity_iterate_refine_two
    (hA : ∀ i : ZMod (2 * N), i.val % 2 ≠ 0 → ∀ a : Coordinates n, a ≠ 0 →
      0 < ⟪Amap F (refine 2 N F M.seg hq) i a, a⟫)
    (d : ℕ) [NeZero d] :
    nullity F (iterate d (2 * N) (refine 2 N F M.seg hq)) = nullity F (iterate d N q) := by
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
  have he := refine_iterate M 2 N d hq
  have hP := pull_short 2 N d hq'
  have hPne := pull_ne 2 N d hne'
  have h2 : 2 ∣ 2 * (d * N) := Dvd.intro _ rfl
  have hAP : ∀ i : ZMod (2 * (d * N)), i.val % 2 ≠ 0 → ∀ a : Coordinates n, a ≠ 0 →
      0 < ⟪Amap F (pull 2 N d (refine 2 N F M.seg hq)) i a, a⟫ := by
    intro i hi a ha
    have hA' := Amap_comp
      (ZMod.castHom (Nat.mul_dvd_mul_left 2 (Dvd.intro_left d rfl)) (ZMod (2 * N))) F
      (refine 2 N F M.seg hq) i
    change 0 < ⟪Amap F (fun i => refine 2 N F M.seg hq
      (ZMod.castHom (Nat.mul_dvd_mul_left 2 (Dvd.intro_left d rfl)) (ZMod (2 * N)) i)) i a, a⟫
    rw [hA']
    refine hA _ ?_ a ha
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      Nat.mod_mod_of_dvd _ (Dvd.intro N rfl)]
    exact hi
  have h1 := nullity_refine_of_pos M 2 (d * N) hQ hQne hQpk he hP hPne hQcrit fun u hu hu0 =>
    hessian_pos_of_diag F M.smooth hP hPne h2 hAP
      (fun i hi => eq_zero_of_coarseL 2 (d * N) hu i hi) hu0
  have e : pull 2 N d (refine 2 N F M.seg hq) = fun i =>
      iterate d (2 * N) (refine 2 N F M.seg hq)
        (ZMod.ringEquivCongr (show 2 * (d * N) = d * (2 * N) by ring) i) :=
    funext fun i => pull_eq 2 N d _ i
  rw [← h1, e]
  exact (nullity_comp_congr _ _).symm

end Double

/-! ### Samples of a closed geodesic -/

section Samples

open Finsler.SmoothSobolev Finsler.PolygonGeodesic Finsler.GeodesicArcs

variable {F : ReversibleMetric n}

/-- **The nullities of the iterates of the samples of a closed geodesic do not change when the
number of samples is doubled.** For N large and every d ≥ 1, the d-fold iterates of the polygons
of 4 N and of 2 N samples have the same nullity. -/
theorem exists_nullity_iterate_sample_double (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (d : ℕ) [NeZero d],
      nullity F (iterate d (2 * (2 * N)) (samplePoly (2 * (2 * N)) (ofSmooth g.loop))) =
        nullity F (iterate d (2 * N) (samplePoly (2 * N) (ofSmooth g.loop))) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨δa, hδa, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  obtain ⟨δt, hδt, htw⟩ := PolygonTwist.exists_twist F
  obtain ⟨N₁, hN₁⟩ := polyCritical_of_closedGeodesic F (lt_min M.pos (lt_min hδa hδt))
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
      Twist F (samplePoly K (ofSmooth g.loop)) ∧
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
      (hshort i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hqt : ShortPolygon δt (samplePoly K (ofSmooth g.loop)) := fun i =>
      (hshort i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hne : ∀ i, samplePoly K (ofSmooth g.loop) (i + 1) ≠
        samplePoly K (ofSmooth g.loop) i := fun i => samplePoly_ofSmooth_ne g hscale hlt i
    refine ⟨hq, hne, fun j => ?_, htw K _ hqt hne,
      fderiv_energy_eq_zero_of_polyCritical F M.smooth hq hne hc, fun hq' => hN₂ K hK2 hq'⟩
    obtain ⟨P₀, hP₀, hP⟩ := hcover (samplePoly K (ofSmooth g.loop) j)
    exact ⟨S P₀, hP, (hqa j).trans_le (hδS P₀ hP₀)⟩
  refine ⟨max N₁ (max N₂ (N₃ + 1)), fun N hN _ d _ => ?_⟩
  have hN1 : max N₁ (max N₂ (N₃ + 1)) ≤ 2 * N := hN.trans (Nat.le_mul_of_pos_left N two_pos)
  have hN2 : max N₁ (max N₂ (N₃ + 1)) ≤ 2 * (2 * N) :=
    hN1.trans (Nat.le_mul_of_pos_left (2 * N) two_pos)
  have hN4 : max N₁ (max N₂ (N₃ + 1)) ≤ 4 * N := hN.trans (Nat.le_mul_of_pos_left N (by norm_num))
  obtain ⟨hq₀, hne₀, hpk₀, -, hcrit₀, hbr₀⟩ := hfacts N hN
  obtain ⟨hq₁, hne₁, hpk₁, -, hcrit₁, hbr₁⟩ := hfacts (2 * N) hN1
  obtain ⟨hq₂, hne₂, -, htw₂, -, -⟩ := hfacts (2 * (2 * N)) hN2
  obtain ⟨hq₄, hne₄, -, -, -, -⟩ := hfacts (4 * N) hN4
  have he₁ : refine 2 (2 * N) F M.seg hq₁ = samplePoly (2 * (2 * N)) (ofSmooth g.loop) := by
    unfold refine
    rw [hbr₁ hq₁]
  have he₄ : refine 4 N F M.seg hq₀ = samplePoly (4 * N) (ofSmooth g.loop) := by
    unfold refine
    rw [hbr₀ hq₀]
  have hpsd₄ : ∀ z : Model n (4 * N), (∀ i : ZMod (4 * N), i.val % 4 = 0 → z i = 0) →
      0 ≤ ⟪hessian F (samplePoly (4 * N) (ofSmooth g.loop)) z, z⟫ := fun z hz =>
    hessian_nonneg_of_coarse M 4 N hq₀ hne₀ hpk₀ he₄ hq₄ hne₄ hcrit₀ (coarseL_eq_zero 4 N hz)
  have hpsd₂ := nonneg_congr (ofSmooth g.loop) (show 4 * N = 2 * (2 * N) by ring) hpsd₄
  have h4 : 4 ∣ 2 * (2 * N) := ⟨N, by ring⟩
  have h := nullity_iterate_refine_two M (2 * N) hq₁ hne₁ hpk₁ (by rw [he₁]; exact hq₂)
    (by rw [he₁]; exact hne₂) hcrit₁
    (by
      rw [he₁]
      exact fun i hi a ha => Amap_pos_of_nonneg F M.smooth hq₂ hne₂ h4 htw₂ hpsd₂ hi ha) d
  rw [he₁] at h
  exact h

end Samples

end

end Finsler.PolygonRefineIterateNullity
