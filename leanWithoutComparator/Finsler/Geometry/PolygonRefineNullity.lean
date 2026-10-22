module

public import Finsler.Geometry.PolygonRefineIndex
public import Finsler.Analysis.NullityComparison
public import Finsler.Algebra.JacobiPositive

/-! The nullity of a polygon when the number of vertices is doubled. For a short polygon without
zero edges with the twist condition, the coefficient B_j of the previous vertex in the Jacobi
form of the Hessian is the adjoint of the coefficient T_{j-1} of the next vertex, hence
injective. If the number of vertices is divisible by 4 and the quadratic form of the Hessian is
nonnegative on the vectors vanishing at the vertices with index divisible by 4, it is positive
on the nonzero vectors vanishing at the vertices with even index. -/

@[expose] public section

namespace Finsler.PolygonRefineNullity

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonLoop Finsler.PolygonChart Finsler.PolygonHessian Finsler.PolygonNullity
open Finsler.PolygonMonodromy Finsler.EnergySphereSmooth Finsler.PolygonRefine
open Finsler.PolygonRefineIndex Finsler.PolygonModel Finsler.PolygonSampling
open Finsler.SegmentAtlas Finsler.AmbientEnergyRegularity Finsler.SphereRetraction
open Finsler.OperatorIndex
open Set Filter Module
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ}

section Jacobi

variable {K : ℕ} [NeZero K] (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod K → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- The coefficient of the previous vertex is the adjoint of the coefficient of the next vertex
of the previous edge. -/
theorem inner_Bmap_eq (j : ZMod K) (v η : Coordinates n) :
    ⟪Bmap F q j v, η⟫ = ⟪Tmap F q (j - 1) η, v⟫ := by
  rw [inner_Bmap, inner_Tmap]
  exact (pairE_contDiffAt F hδ hq hne (j - 1)).isSymmSndFDerivAt (by norm_num) _ _

include hδ hq hne in
/-- Under the twist condition the coefficient of the previous vertex is injective. -/
theorem Bmap_injective (htw : Twist F q) (j : ZMod K) : Function.Injective (Bmap F q j) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hsurj : Function.Surjective (Tmap F q (j - 1)) :=
    (LinearMap.injective_iff_surjective (f := (Tmap F q (j - 1)).toLinearMap)).mp
      (Tmap_injective F hδ hq hne htw (j - 1))
  obtain ⟨η, hη⟩ := hsurj v
  have h := inner_Bmap_eq F hδ hq hne j v η
  rw [hv, inner_zero_left, hη] at h
  exact inner_self_eq_zero.mp h.symm

include hδ hq hne in
/-- **Positivity at the odd vertices.** If the number of vertices is divisible by 4 and the form
of the Hessian is nonnegative on the vectors vanishing at the vertices with index divisible by
4, then it is positive on the nonzero vectors vanishing at the vertices with even index. -/
theorem hessian_pos_of_nonneg (h4 : 4 ∣ K) (htw : Twist F q)
    (hpsd : ∀ z : Model n K, (∀ i : ZMod K, i.val % 4 = 0 → z i = 0) →
      0 ≤ ⟪hessian F q z, z⟫)
    {u : Model n K} (hu : ∀ i : ZMod K, i.val % 2 = 0 → u i = 0) (hu0 : u ≠ 0) :
    0 < ⟪hessian F q u, u⟫ := by
  have hK4 : 4 ≤ K := Nat.le_of_dvd (Nat.pos_of_neZero K) h4
  have h10 : (1 : ZMod K) ≠ 0 := fun h => hne 0 (by rw [zero_add, h])
  have h20 : (2 : ZMod K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod K) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_neZero K
  -- residues modulo 4 of the neighbours
  have hsucc : ∀ j : ZMod K, (j + 1).val % 4 = (j.val + 1) % 4 := by
    intro j
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < K),
      Nat.mod_mod_of_dvd _ h4]
  have hS₂ : ∀ i : ZMod K, i ∉ {i : ZMod K | i.val % 2 = 0} →
      i + 1 ∈ {i : ZMod K | i.val % 2 = 0} ∧ i - 1 ∈ {i : ZMod K | i.val % 2 = 0} ∧
      i ∉ {i : ZMod K | i.val % 4 = 0} ∧
      (i + 1 ∉ {i : ZMod K | i.val % 4 = 0} ∨ i - 1 ∉ {i : ZMod K | i.val % 4 = 0}) := by
    intro i hi
    have hi' : i.val % 2 ≠ 0 := hi
    have h1 := hsucc i
    have h2 := hsucc (i - 1)
    rw [sub_add_cancel] at h2
    change (i + 1).val % 2 = 0 ∧ (i - 1).val % 2 = 0 ∧ ¬ i.val % 4 = 0 ∧
      (¬ (i + 1).val % 4 = 0 ∨ ¬ (i - 1).val % 4 = 0)
    omega
  exact JacobiPositive.inner_pos (hessian F q).toLinearMap
    (fun i => (Tmap F q i).toLinearMap) (fun i => (Amap F q i).toLinearMap)
    (fun i => (Bmap F q i).toLinearMap) (c := (K : ℝ))
    (fun w i => hessian_apply F hδ hq hne w i) h10 h20 (hessian_isSymmetric F hδ hq hne) hKpos
    {i : ZMod K | i.val % 4 = 0} hpsd (fun i => Tmap_injective F hδ hq hne htw i)
    (fun i => Bmap_injective F hδ hq hne htw i) {i : ZMod K | i.val % 2 = 0} hS₂ hu hu0

end Jacobi

/-! ### Refinement -/

section Refine

variable {F : ReversibleMetric n} (M : SegmentData F) (r N : ℕ) [NeZero r] [NeZero N]

/-- Forgetting the inserted vertices of the refined coordinates gives back the coordinates, near
the centre. -/
theorem eventually_coarseL_refineCoord {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) :
    ∀ᶠ x in 𝓝 (base q),
      coarseL r N (refineCoord M r N q (refine r N F M.seg hq) x) = x := by
  have hr := Nat.pos_of_neZero r
  have htar : ∀ᶠ x in 𝓝 (base q), ∀ j : ZMod N, x j ∈ (extChartAt (𝓡 n) (q j)).target := by
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun x : Model n N => x j) (base q) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) j).continuous.continuousAt
    exact hc.eventually ((isOpen_extChartAt_target (I := 𝓡 n) (q j)).mem_nhds
      ((extChartAt (𝓡 n) (q j)).map_source (mem_extChartAt_source (q j))))
  filter_upwards [eventually_short hq, htar] with x hP ht
  refine PiLp.ext fun j => ?_
  have hj : j.val < N := ZMod.val_lt j
  have hlt : r * j.val < r * N := Nat.mul_lt_mul_of_pos_left hj hr
  have hval : (((r * j.val : ℕ) : ZMod (r * N))).val = r * j.val := ZMod.val_natCast_of_lt hlt
  have hqj : refine r N F M.seg hq ((r * j.val : ℕ) : ZMod (r * N)) = q j :=
    congrFun (coarse_refine r N F M.seg hq) j
  have hvert : vert M r N q ((r * j.val : ℕ) : ZMod (r * N)) x = (poly q x j : Ambient n) := by
    unfold vert
    rw [hval, Nat.mul_div_cancel_left _ hr, Nat.mul_mod_right, ZMod.natCast_zmod_val,
      Nat.cast_zero, zero_div]
    exact (M.seg _ _ (hP j)).2.2.1
  change chartNormalize (refine r N F M.seg hq ((r * j.val : ℕ) : ZMod (r * N)))
    (vert M r N q ((r * j.val : ℕ) : ZMod (r * N)) x) = x j
  rw [hqj, hvert]
  unfold chartNormalize
  rw [normalize_inclusion]
  exact (extChartAt (𝓡 n) (q j)).right_inv (ht j)

section Critical

variable {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (hne : ∀ j, q (j + 1) ≠ q j)
  (hpk : ∀ j : ZMod N, ∃ T : SegChart F, q j ∈ segDom T ∧
    ‖(q (j + 1) : Ambient n) - q j‖ < T.δ)
  {q' : ZMod (r * N) → Sphere n} (he : refine r N F M.seg hq = q')
  (hq' : ShortPolygon M.δ q') (hne' : ∀ i, q' (i + 1) ≠ q' i)
  (hcrit : fderiv ℝ (energy F q) (base q) = 0)

include hne hpk he hq' hne' hcrit in
/-- The form of the Hessian of the refinement is nonnegative on the vectors vanishing at the
vertices of the polygon. -/
theorem hessian_nonneg_of_coarse {z : Model n (r * N)} (hz : coarseL r N z = 0) :
    0 ≤ ⟪hessian F q' z, z⟫ := by
  subst he
  have hc := coarse_refine r N F M.seg hq
  have hf₁ : ContDiffAt ℝ 2 (energy F q) (base q) :=
    (energy_contDiffAt F M.smooth hq hne).of_le (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (energy F (refine r N F M.seg hq))
      (base (refine r N F M.seg hq)) :=
    (energy_contDiffAt F M.smooth hq' hne').of_le (by norm_num)
  have h₂ := fderiv_refine_eq_zero M r N hq hne hpk hq' hne' hcrit
  have heq : energy F q (base q) =
      energy F (refine r N F M.seg hq) (base (refine r N F M.seg hq)) := by
    have h := (eventually_energy_refine M r N hq hne hpk hq').self_of_nhds
    rw [refineCoord_base M r N hq] at h
    exact h.symm
  have h := IndexComparison.sndDeriv_le_of_le (coarseL_base r N hc) hf₁ hf₂ hcrit h₂
    (coarseL r N).hasFDerivAt
    ((eventually_short hq').mono fun y hy => energy_coarse_le M r N hc hy) heq z
  rw [hz, map_zero] at h
  change 0 ≤ ⟪Hessian.operator (energy F (refine r N F M.seg hq))
    (base (refine r N F M.seg hq)) z, z⟫
  rw [Hessian.inner_operator]
  exact h

include hne hpk he hq' hne' hcrit in
/-- **The nullity of the refinement**, if the form of its Hessian is positive on the nonzero
vectors vanishing at the vertices of the polygon. -/
theorem nullity_refine_of_pos
    (hpos : ∀ u : Model n (r * N), coarseL r N u = 0 → u ≠ 0 → 0 < ⟪hessian F q' u, u⟫) :
    nullity F q' = nullity F q := by
  subst he
  have hc := coarse_refine r N F M.seg hq
  have hf₁ : ContDiffAt ℝ 2 (energy F q) (base q) :=
    (energy_contDiffAt F M.smooth hq hne).of_le (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (energy F (refine r N F M.seg hq))
      (base (refine r N F M.seg hq)) :=
    (energy_contDiffAt F M.smooth hq' hne').of_le (by norm_num)
  have h₂ := fderiv_refine_eq_zero M r N hq hne hpk hq' hne' hcrit
  have hcomp := eventually_energy_refine M r N hq hne hpk hq'
  have heq : energy F q (base q) =
      energy F (refine r N F M.seg hq) (base (refine r N F M.seg hq)) := by
    have h := hcomp.self_of_nhds
    rw [refineCoord_base M r N hq] at h
    exact h.symm
  have hR := (refineCoord_differentiableAt M r N hq hne hpk).hasFDerivAt
  -- the composite of the two derivatives is the identity
  have hid : (coarseL r N).comp
      (fderiv ℝ (refineCoord M r N q (refine r N F M.seg hq)) (base q)) =
      ContinuousLinearMap.id ℝ (Model n N) := by
    have h1 : HasFDerivAt (fun x => coarseL r N (refineCoord M r N q (refine r N F M.seg hq) x))
        ((coarseL r N).comp (fderiv ℝ (refineCoord M r N q (refine r N F M.seg hq)) (base q)))
        (base q) := (coarseL r N).hasFDerivAt.comp (base q) hR
    have h2 : HasFDerivAt (fun x : Model n N => x)
        ((coarseL r N).comp (fderiv ℝ (refineCoord M r N q (refine r N F M.seg hq)) (base q)))
        (base q) :=
      h1.congr_of_eventuallyEq
        ((eventually_coarseL_refineCoord M r N hq).mono fun x hx => hx.symm)
    exact h2.unique (hasFDerivAt_id (base q))
  exact NullityComparison.finrank_ker_eq_of_retraction
    (hessian_isSymmetric F M.smooth hq hne) (hessian_isSymmetric F M.smooth hq' hne')
    (fderiv ℝ (refineCoord M r N q (refine r N F M.seg hq)) (base q)).toLinearMap
    (coarseL r N).toLinearMap
    (fun v => by
      change quad (Hessian.operator (energy F (refine r N F M.seg hq))
        (base (refine r N F M.seg hq))) _ = quad (Hessian.operator (energy F q) (base q)) v
      rw [quad_apply, quad_apply, Hessian.inner_operator, Hessian.inner_operator]
      exact (IndexComparison.sndDeriv_eq_of_comp (refineCoord_base M r N hq) hf₁ hf₂ hcrit h₂
        hR hcomp v).symm)
    (fun u => by
      change quad (Hessian.operator (energy F q) (base q)) _ ≤
        quad (Hessian.operator (energy F (refine r N F M.seg hq))
          (base (refine r N F M.seg hq))) u
      rw [quad_apply, quad_apply, Hessian.inner_operator, Hessian.inner_operator]
      exact IndexComparison.sndDeriv_le_of_le (coarseL_base r N hc) hf₁ hf₂ hcrit h₂
        (coarseL r N).hasFDerivAt
        ((eventually_short hq').mono fun y hy => energy_coarse_le M r N hc hy) heq u)
    (fun v => congrArg (fun A : Model n N →L[ℝ] Model n N => A v) hid)
    (fun u hu hu0 => hpos u hu hu0)

end Critical

/-- A vector vanishing at the vertices with index divisible by r has zero coarse part. -/
theorem coarseL_eq_zero {z : Model n (r * N)}
    (hz : ∀ i : ZMod (r * N), i.val % r = 0 → z i = 0) : coarseL r N z = 0 := by
  refine PiLp.ext fun j => ?_
  have hlt : r * j.val < r * N :=
    Nat.mul_lt_mul_of_pos_left (ZMod.val_lt j) (Nat.pos_of_neZero r)
  change z ((r * j.val : ℕ) : ZMod (r * N)) = 0
  exact hz _ (by rw [ZMod.val_natCast_of_lt hlt, Nat.mul_mod_right])

/-- A vector with zero coarse part vanishes at the vertices with index divisible by r. -/
theorem eq_zero_of_coarseL {u : Model n (r * N)} (hu : coarseL r N u = 0)
    (i : ZMod (r * N)) (hi : i.val % r = 0) : u i = 0 := by
  have hiN : i.val / r < N := Nat.div_lt_of_lt_mul (ZMod.val_lt i)
  have h : coarseL r N u ((i.val / r : ℕ) : ZMod N) = 0 := by rw [hu]; rfl
  change u ((r * (((i.val / r : ℕ) : ZMod N)).val : ℕ) : ZMod (r * N)) = 0 at h
  have e : r * (i.val / r) = i.val := by
    have h3 := Nat.div_add_mod i.val r
    rw [hi, add_zero] at h3
    exact h3
  rw [ZMod.val_natCast_of_lt hiN, e, ZMod.natCast_zmod_val] at h
  exact h

end Refine

/-! ### Samples of a closed geodesic -/

section Samples

open Finsler.SmoothSobolev Finsler.PolygonGeodesic Finsler.GeodesicArcs
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy

variable {F : ReversibleMetric n}

/-- Nonnegativity on the vectors vanishing at the vertices with index divisible by 4 only
depends on the number of samples. -/
theorem nonneg_congr (u : SphereLoop n) {K K' : ℕ} [NeZero K] [NeZero K'] (h : K = K')
    (hK : ∀ z : Model n K, (∀ i : ZMod K, i.val % 4 = 0 → z i = 0) →
      0 ≤ ⟪hessian F (samplePoly K u) z, z⟫) :
    ∀ z : Model n K', (∀ i : ZMod K', i.val % 4 = 0 → z i = 0) →
      0 ≤ ⟪hessian F (samplePoly K' u) z, z⟫ := by
  subst h
  exact hK

/-- **The nullity of the samples of a closed geodesic does not change when the number of samples
is doubled.** For N large, the polygons of 2 N and of 4 N samples of a closed geodesic have the
same nullity. -/
theorem exists_nullity_sample_double (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      nullity F (samplePoly (2 * (2 * N)) (ofSmooth g.loop)) =
        nullity F (samplePoly (2 * N) (ofSmooth g.loop)) := by
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
  refine ⟨max N₁ (max N₂ (N₃ + 1)), fun N hN _ => ?_⟩
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
  exact nullity_refine_of_pos M 2 (2 * N) hq₁ hne₁ hpk₁ he₁ hq₂ hne₂ hcrit₁ fun w hw hw0 =>
    hessian_pos_of_nonneg F M.smooth hq₂ hne₂ h4 htw₂ hpsd₂
      (fun i hi => eq_zero_of_coarseL 2 (2 * N) hw i hi) hw0

end Samples

end

end Finsler.PolygonRefineNullity
