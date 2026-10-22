module

public import Finsler.Topology.CircleRoot
public import Finsler.Topology.LoopCrossingOriented
public import Finsler.Geometry.LevelDescent
public import Finsler.Analysis.FrameIndex
public import Finsler.Geometry.CircleLabelFields
public import Finsler.Topology.RootLens

/-! The label of a critical circle. With finitely many prime closed geodesic images, let a
label (a prime image with an orientation) have a critical circle at the level c > 0, the
rotations of the k-fold iterate of its closed geodesic. Write k = s m with s = gcd(k, 2L) for the
period L of the iteration data. For all large N and every K = k (2 N), every open set of
ambient polygons with K vertices containing the samples of the circle and every η > 0, there are
the data of the label in the space of the level: a region inside the open set, the split field,
a deformation bounded by η with closed support in a compact tube containing the samples of the
circle, label sets, and the critical set where the penalized energy has the value c² and the
deformation vanishes; and for every descent agreeing with the split field on the tube of a
function equal to the deformed energy on the tube, the lens pairs of the label set for tight
cuts around c² have in degree j + b (b = I(k) - I(s)) the dimensions r of the root labels in
degree j and no cohomology below b. The root data come from the frames along the root circle,
the chosen isolated band [a₁, b₁] around the root level c/m = gcd(k, 2L) √E, the isolation of the
sampled root circle, the root fields and the rest of the root band; for tight cuts the root labels
are at most the ordinary cohomology of the loop pair (t_{b₁}, t_{a₁}) in every degree in which it
is finite dimensional (the root label is a summand of the root crossing, which is the loop
crossing of the root band). -/

@[expose] public section

namespace Finsler.CircleLabel

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.Loops
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel
open Finsler.PolygonDescent Finsler.PolygonSmooth Finsler.CriticalLevels Finsler.OrientedCritical
open Finsler.CriticalCircles Finsler.SmoothSobolev Finsler.EnergyDiagonal
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.AmbientDescent
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.GeodesicFrames Finsler.PhaseNullity Finsler.SamplePhase
open Finsler.LevelField Finsler.LevelDescent Finsler.LabelPack Finsler.RootBand
open Finsler.RootIsolation Finsler.CircleSampling Finsler.CircleRoot Finsler.LoopCrossingOriented
open Finsler.FlowLens Finsler.LensContinuation Finsler.ProductModel
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.RootLens Finsler.LevelCrossing Finsler.CutMove Finsler.LensFamily
open Finsler.AmbientLoopPairs
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 5

variable {n : ℕ} (F : ReversibleMetric n)

/-- **An isolated critical level.** With finitely many prime closed geodesic images every
positive level c has a neighbourhood [a₁, b₁] in which c is the only possible critical level. -/
theorem exists_isolated_level (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c) :
    ∃ a₁ b₁ : ℝ, 0 < a₁ ∧ a₁ < c ∧ c < b₁ ∧
      ∀ c' ∈ crit F, a₁ ≤ c' → c' ≤ b₁ → c' = c := by
  set T : Set ℝ := (crit F ∩ Icc (c / 2) (2 * c)) \ {c} with hT
  have hTf : T.Finite := (crit_finite F hfin _ _).subset sdiff_subset
  have hcT : c ∉ T := fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hTf.isClosed.isOpen_compl c hcT
  refine ⟨max (c / 2) (c - ε / 2), min (2 * c) (c + ε / 2), lt_max_of_lt_left (half_pos hc),
    max_lt (half_lt_self hc) (by linarith), lt_min (by linarith) (by linarith), ?_⟩
  intro c' hc' h1 h2
  by_contra hne
  have hmem : c' ∈ T := ⟨⟨hc', (le_max_left _ _).trans h1, h2.trans (min_le_left _ _)⟩, hne⟩
  have hd : c' ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1' := (le_max_right _ _).trans h1
    have h2' := h2.trans (min_le_right _ _)
    constructor <;> linarith
  exact hball hd hmem

/-- The root of an iterate: s = gcd(k, 2L) divides k, and s, m = k / s satisfy the hypotheses of
the frames along the circle. -/
theorem root_facts {k L : ℕ} (hk : 0 < k) :
    0 < Nat.gcd k (2 * L) ∧ Nat.gcd k (2 * L) * (k / Nat.gcd k (2 * L)) = k ∧
      Nat.gcd (Nat.gcd k (2 * L) * (k / Nat.gcd k (2 * L))) L = Nat.gcd (Nat.gcd k (2 * L)) L ∧
      (Even (Nat.gcd k (2 * L)) ∨ Odd (k / Nat.gcd k (2 * L))) := by
  have hdvd := Nat.gcd_dvd_left k (2 * L)
  have hmul : Nat.gcd k (2 * L) * (k / Nat.gcd k (2 * L)) = k := Nat.mul_div_cancel' hdvd
  refine ⟨Nat.gcd_pos_of_pos_left _ hk, hmul, ?_, ?_⟩
  · rw [hmul, Nat.gcd_assoc, Nat.gcd_eq_right (Dvd.intro_left 2 rfl : L ∣ 2 * L)]
  · by_cases he : Even k
    · left
      rw [even_iff_two_dvd] at he ⊢
      exact Nat.dvd_gcd he (Dvd.intro L rfl)
    · right
      exact (Nat.not_even_iff_odd.mp he).of_dvd_nat (Nat.div_dvd_of_dvd hdvd)

/-- A chosen isolated band around a positive level. -/
def isoBand (hfin : (primeImages F).Finite) (x : ℝ) : ℝ × ℝ :=
  if hx : 0 < x then
    (Classical.choose (exists_isolated_level F hfin hx),
      Classical.choose (Classical.choose_spec (exists_isolated_level F hfin hx)))
  else (1, 1)

theorem isoBand_spec (hfin : (primeImages F).Finite) {x : ℝ} (hx : 0 < x) :
    0 < (isoBand F hfin x).1 ∧ (isoBand F hfin x).1 < x ∧ x < (isoBand F hfin x).2 ∧
      ∀ c' ∈ crit F, (isoBand F hfin x).1 ≤ c' → c' ≤ (isoBand F hfin x).2 → c' = x := by
  have h := Classical.choose_spec (Classical.choose_spec (exists_isolated_level F hfin hx))
  unfold isoBand
  rw [dite_eq_left hx]
  exact h

theorem isoBand_le (hfin : (primeImages F).Finite) (x : ℝ) :
    (isoBand F hfin x).1 ≤ (isoBand F hfin x).2 := by
  by_cases hx : 0 < x
  · obtain ⟨-, h1, h2, -⟩ := isoBand_spec F hfin hx
    exact (h1.trans h2).le
  · unfold isoBand
    rw [dite_eq_right hx]

/-- The energy of a stationary short polygon of an isolated band is the square of the level. -/
theorem energy_eq_of_crit {A : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F A N) {c a₁ b₁ : ℝ}
    (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁) (hone : ∀ c' ∈ crit F, a₁ ≤ c' → c' ≤ b₁ → c' = c)
    {q : ZMod N → Sphere n} (hq : ShortPolygon M.δ q) (hc : PolyCritical F N q)
    (ha : a₁ ^ 2 ≤ PolygonDescent.energy F N q) (hb : PolygonDescent.energy F N q ≤ b₁ ^ 2) :
    PolygonDescent.energy F N q = c ^ 2 := by
  have htc : Finsler.SobolevCurveVariation.TangentCritical F (broken M ⟨q, hq⟩) :=
    tangentCritical_of_polyCritical F M.seg hq hc
  have hE : Finsler.SobolevEnergy.energy F (broken M ⟨q, hq⟩) = PolygonDescent.energy F N q :=
    energy_broken M ⟨q, hq⟩
  have hpos : 0 < Finsler.SobolevEnergy.energy F (broken M ⟨q, hq⟩) := by
    rw [hE]
    exact lt_of_lt_of_le (by positivity) ha
  have hb₁ : 0 ≤ b₁ := ha₁.le.trans hab₁
  have hlevel : Real.sqrt (Finsler.SobolevEnergy.energy F (broken M ⟨q, hq⟩)) = c := by
    apply hone _ (crit_mem F _ htc hpos)
    · rw [hE]
      calc a₁ = Real.sqrt (a₁ ^ 2) := (Real.sqrt_sq ha₁.le).symm
        _ ≤ Real.sqrt (PolygonDescent.energy F N q) := Real.sqrt_le_sqrt ha
    · rw [hE]
      calc Real.sqrt (PolygonDescent.energy F N q) ≤ Real.sqrt (b₁ ^ 2) := Real.sqrt_le_sqrt hb
        _ = b₁ := Real.sqrt_sq hb₁
  rw [← hE, ← hlevel, Real.sq_sqrt hpos.le]

set_option maxHeartbeats 1600000 in
/-- **A half-equivariant label of an actual critical circle.** All ordinary label estimates
are retained, with invariant neighbourhoods, tube, deformation and label sets. -/
theorem circle_label_half (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K], k * (2 * N) = K →
      ∀ {𝒰 : Set (ZMod K → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
      ∃ (b : ℕ) (r : ℝ → ℝ → ℝ → ℕ → ℕ) (U : Set (ZMod K → Ambient n))
        (W : (ZMod K → Ambient n) → ZMod K → Ambient n)
        (β : (ZMod K → Ambient n) → ℝ) (C T : Set (ZMod K → Ambient n)) (𝒲 𝒲' : Set (Om n K)),
        (∀ y, rotA K (k * N : ZMod K) y ∈ U ↔ y ∈ U) ∧
        (∀ y, rotA K (k * N : ZMod K) y ∈ T ↔ y ∈ T) ∧
        (∀ y ∈ U, W (rotA K (k * N : ZMod K) y) = rotA K (k * N : ZMod K) (W y)) ∧
        (∀ y, β (rotA K (k * N : ZMod K) y) = β y) ∧
        (∀ Q, (⟨rotA K (k * N : ZMod K) Q.1,
          Finsler.AmbientSymmetry.rotA_ne_zero K _ Q.2⟩ : Om n K) ∈ 𝒲 ↔ Q ∈ 𝒲) ∧
        (∀ Q, (⟨rotA K (k * N : ZMod K) Q.1,
          Finsler.AmbientSymmetry.rotA_ne_zero K _ Q.2⟩ : Om n K) ∈ 𝒲' ↔ Q ∈ 𝒲') ∧
        b = (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k -
          (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I
            (Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L)) ∧
        IsOpen U ∧ U ⊆ 𝒰 ∧ U ⊆ regSet F K 1 ∧ ContDiffOn ℝ ∞ W U ∧
        (∀ y ∈ U, fderiv ℝ (pen F K 1) y (W y) ≤ 0) ∧
        (∀ y ∈ U, y ∉ C → fderiv ℝ (pen F K 1) y (W y) < 0) ∧
        IsCompact T ∧ T ⊆ U ∧ tsupport β ⊆ T ∧ (∀ y, DifferentiableAt ℝ β y) ∧
        (∀ y, |β y| ≤ η) ∧
        (∀ y ∈ tsupport β, fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) ≤ 0) ∧
        (∀ y ∈ tsupport β, y ∉ C → fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) < 0) ∧
        IsOpen 𝒲 ∧ IsOpen 𝒲' ∧ 𝒲' ⊆ 𝒲 ∧ (∀ Q ∈ 𝒲, Q.1 ∈ T) ∧
        (∀ Q : Om n K, Q.1 ∈ C → Q ∈ 𝒲') ∧ C ⊆ U ∧
        (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ T) ∧
        (∀ y ∈ C, pen F K 1 y = c ^ 2 ∧ β y = 0) ∧
        (∃ dr : ℝ, 0 < dr ∧ ∀ a c' t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < c' → c' - a < dr →
          ∀ j : ℕ, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
            ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
              Real.sqrt (Finsler.LoopEnergy.energy F
                (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j) →
          r a c' t j ≤ finrank (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
            ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
              Real.sqrt (Finsler.LoopEnergy.energy F
                (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j)) ∧
        ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
          (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
          {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
          (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
          (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
          (∀ y ∈ T, V y = W y) → (∀ y ∈ T, g y = pen F K 1 y + β y) →
          ∀ {a₀a b₀a : ℝ}, a₀a < c ^ 2 → c ^ 2 < b₀a → Continuous (fun Q : Om n K => g Q.1) →
          IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a} →
          ∀ {R : Set (Om n K)}, IsOpen R → Disjoint 𝒲 R →
          (∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ 𝒲' ∪ R →
            g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
          ∃ d : ℝ, 0 < d ∧ ∀ a c' t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < c' → c' - a < d →
            (∀ j : ℕ, finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
                (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c' t))) (j + b)) =
              r a c' t j) ∧
            (∀ j : ℕ, j < b → ∀ x : H (triv (pairOf (partY_sub_partU
                (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c' t))) j,
              x = 0) := by
  classical
  have hℓ' : ℓ.1 ∈ primeImages F := (mem_labels F hfin ℓ).mp hℓ
  set g := labelGeod F ℓ hℓ' with hgdef
  have hprime := labelGeod_prime F ℓ hℓ'
  have hEpos := chosen_energy_pos F ℓ.1 hℓ'
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.cast_zero, zero_mul] at hkc
      exact absurd hkc hc.ne
    · exact h
  obtain ⟨hs0, hsm, hgcd, hpar⟩ := root_facts (L := (iterData g).L) hk
  set s := Nat.gcd k (2 * (iterData g).L) with hsdef
  set m := k / s with hmdef
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hsm
    omega
  have : NeZero s := ⟨hs0.ne'⟩
  have : NeZero m := ⟨hm0.ne'⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm1 : (0 : ℝ) < 1 / (m : ℝ) := one_div_pos.mpr hmR
  -- the root level
  have hsc : (s : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ').loop) =
      c / m := by
    rw [eq_div_iff hmR.ne', ← hkc, ← hsm]
    push_cast
    ring
  have hcm : 0 < c / m := div_pos hc hmR
  have hxr : (0 : ℝ) < (s : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 hℓ').loop) := by
    rw [hsc]
    exact hcm
  obtain ⟨ha₁, hac₁', hcb₁', hone₁'⟩ := isoBand_spec F hfin hxr
  set a₁ := (isoBand F hfin ((s : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
    (chosen F ℓ.1 hℓ').loop))).1 with ha₁def
  set b₁ := (isoBand F hfin ((s : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
    (chosen F ℓ.1 hℓ').loop))).2 with hb₁def
  have hac₁ : a₁ < c / m := by
    rw [← hsc]
    exact hac₁'
  have hcb₁ : c / m < b₁ := by
    rw [← hsc]
    exact hcb₁'
  have hone₁ : ∀ c' ∈ crit F, a₁ ≤ c' → c' ≤ b₁ → c' = c / m := fun c' hc' h1 h2 =>
    (hone₁' c' hc' h1 h2).trans hsc
  have hab₁ : a₁ ≤ b₁ := (hac₁.trans hcb₁).le
  -- frames
  obtain ⟨Nf, hNf⟩ := Finsler.CircleEvenFields.exists_adapted_frame_fields g hprime s m hgcd hpar
  -- segment data, models and sample facts
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨δ₁, hδ₁, hC1⟩ := exists_ambientMinEnergy_contDiffAt_one F
  set S := shrink S₀ (lt_min S₀.pos hδ₁) (min_le_left _ _) with hS
  have hSδ : S.δ ≤ δ₁ := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := b₁) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b₁ ^ 2 / (e * S.δ ^ 2))
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all S g
  refine ⟨max Nf (max K₀ (max N₁ (max N₂ 1))), fun N hN _ K _ hK 𝒰 h𝒰 h𝒰c η hη => ?_⟩
  have hNf' : Nf ≤ N := (le_max_left _ _).trans hN
  have hK₀' : K₀ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₁' : N₁ ≤ N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hN₂' : N₂ ≤ N := ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans hN
  have hN1 : 1 ≤ N := ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans hN
  set N' := s * (2 * N) with hN'def
  have hKm : m * N' = K := by
    rw [← hK, ← hsm, hN'def]
    ring
  have hNN' : N ≤ N' := by
    rw [hN'def]
    nlinarith [hs0]
  obtain ⟨⟨S₁⟩, ⟨S₂⟩⟩ := hNf N hNf'
  let 𝒪f := S₁.U ∩ S₂.U
  have h𝒪f : IsOpen 𝒪f := S₁.isOpen.inter S₂.isOpen
  have hfam : ∀ a, amb (rootFamily g s N a) ∈ 𝒪f :=
    fun a => ⟨S₁.circle_mem a, S₂.circle_mem a⟩
  have hsmooth : 𝒪f ⊆ smoothSet m N' F := fun _ hz => S₁.subset_smooth hz.1
  let G₁ := S₁.G
  let G₂ := S₂.G
  have hG₁ := S₁.smooth
  have hG₂ := S₂.smooth
  have hneg : ∀ z ∈ 𝒪f, Neg (normalForm m N' F z) (G₁ z) ∧
      Neg (-normalForm m N' F z) (G₂ z) := by
    intro z hz
    constructor
    · simpa only [one_smul] using S₁.definite z hz.1
    · intro x hx
      have h := S₂.definite z hz.2 x hx
      change (-1 : ℝ) * normalForm m N' F z (comb (G₂ z) x) (comb (G₂ z) x) < 0 at h
      change -(normalForm m N' F z (comb (G₂ z) x) (comb (G₂ z) x)) < 0
      linarith only [h]
  -- the root model
  let M' : PolygonModelData F b₁ N' :=
    PolygonModelData.mk S fun u hu s' t hs' ht hst =>
      hN₁ N' (hN₁'.trans hNN') (Nat.pos_of_neZero N') u hu s' t hs' ht hst
  have hNR : b₁ ^ 2 / (e * S.δ ^ 2) < N' :=
    hN₂.trans_le (Nat.cast_le.mpr (hN₂'.trans hNN'))
  have hshortR : ∀ q : ZMod N' → Sphere n, PolygonDescent.energy F N' q ≤ b₁ ^ 2 →
      ShortPolygon M'.δ q := fun q hq => short_of_energy_le he S.pos hedge hNR q hq
  have hC : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < M'.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q h => hC1 P Q (h.trans_le hSδ)
  have h2N : 1 < 2 * N := by omega
  have hf : ∀ x : ℝ, SampleFacts S (ofSmooth (shift g.loop x)) (2 * N) := fun x =>
    hK₀ x (2 * N) (by omega)
  -- the circles
  have hcircR : circle F (c / m) ℓ =
      range fun a : ℝ => ofSmooth (shift (iterate g.loop s) a) := circle_eq F hcm ℓ hℓ' hsc
  have hcircK : circle F c ℓ = range fun a : ℝ => ofSmooth (shift (iterate g.loop k) a) :=
    circle_eq F hc ℓ hℓ' hkc
  have hsamp : ∀ u ∈ circle F (c / m) ℓ, ∃ hq : ShortPolygon M'.δ (samplePoly N' u),
      broken M' ⟨samplePoly N' u, hq⟩ = u := by
    rw [hcircR]
    rintro _ ⟨a, rfl⟩
    exact ⟨short_iterate S g.loop s h2N hf rfl a, broken_iterate S g.loop s h2N hf rfl a _⟩
  have hEroot := circle_energy F hcm ℓ hℓ' hsc
  -- the isolation of the root circle
  obtain ⟨𝒱, h𝒱, hΓ𝒱, hiso𝒱⟩ := exists_isolation M' hn hfin hC ha₁ hac₁ hcb₁ hone₁ hshortR
    hℓ hsamp hEroot hm1.ne'
  set Γ := sampleSet N' (circle F (c / m) ℓ) with hΓdef
  have hΓeq : Γ = range fun a : ℝ => amb (rootFamily g s N a) := by
    rw [hΓdef, hcircR, sampleSet_root]
  have hΓc : IsCompact Γ := sampleSet_isCompact (isCompact_circle F (c / m) ℓ)
  have hΓne : Γ.Nonempty := by
    rw [hΓeq]
    exact range_nonempty _
  have hΓpen : ∀ z ∈ Γ, pen F N' (1 / m) z = (c / m) ^ 2 := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hq, hbr⟩ := hsamp u hu
    have h1 := penW_incl F (1 / (m : ℝ)) (samplePoly N' u)
    have h2 := energy_broken M' ⟨samplePoly N' u, hq⟩
    rw [hbr, hEroot u hu] at h2
    change penW F N' (1 / m) (incl (samplePoly N' u)) = _
    rw [h1]
    exact h2.symm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hcsq : (m : ℝ) ^ 2 * (c / m) ^ 2 = c ^ 2 := by
    field_simp
  -- the values on the root circle
  have hΓval : ∀ z ∈ Γ, (m : ℝ) ^ 2 * a₁ ^ 2 < (m : ℝ) ^ 2 * pen F N' (1 / m) z ∧
      (m : ℝ) ^ 2 * pen F N' (1 / m) z < (m : ℝ) ^ 2 * b₁ ^ 2 := fun z hz => by
    rw [hΓpen z hz]
    exact ⟨mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hac₁ ha₁.le two_ne_zero) hm2,
      mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hcb₁ hcm.le two_ne_zero) hm2⟩
  have hΓc₀ : ∀ z ∈ Γ, (m : ℝ) ^ 2 * pen F N' (1 / m) z = c ^ 2 := fun z hz => by
    rw [hΓpen z hz, hcsq]
  -- the root band
  have hKr : IsCompact {z : Om n N' | (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * pen F N' (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N' (1 / m) z.1 ≤ (m : ℝ) ^ 2 * b₁ ^ 2} := by
    have he : {z : Om n N' | (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * pen F N' (1 / m) z.1 ∧
        (m : ℝ) ^ 2 * pen F N' (1 / m) z.1 ≤ (m : ℝ) ^ 2 * b₁ ^ 2} =
        {Q : Om n N' | a₁ ^ 2 ≤ penW F N' (1 / m) Q ∧ penW F N' (1 / m) Q ≤ b₁ ^ 2} := by
      ext z
      change _ ∧ _ ↔ a₁ ^ 2 ≤ pen F N' (1 / m) z.1 ∧ pen F N' (1 / m) z.1 ≤ b₁ ^ 2
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨le_of_mul_le_mul_left h1 hm2, le_of_mul_le_mul_left h2 hm2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨mul_le_mul_of_nonneg_left h1 hm2.le, mul_le_mul_of_nonneg_left h2 hm2.le⟩
    rw [he]
    exact band_isCompact F hn hm1 (a₁ ^ 2) (b₁ ^ 2)
  have hbandreg : ∀ Q : Om n N', (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 ≤ (m : ℝ) ^ 2 * b₁ ^ 2 →
      Q.1 ∈ regSet F N' (1 / m) := fun Q _ h2 =>
    band_regular F hm1 hC hshortR Q (le_of_mul_le_mul_left h2 hm2)
  -- the root fields
  set Sg : Set (ZMod N' → Ambient n) :=
    ⋃ ℓ' ∈ labels F hfin, sampleSet N' (circle F (c / m) ℓ') with hSg
  have hSgc : IsCompact Sg :=
    (labels F hfin).isCompact_biUnion fun ℓ' _ => sampleSet_isCompact (isCompact_circle F _ ℓ')
  have hSgreg : Sg ⊆ regSet F N' (1 / m) := by
    refine iUnion₂_subset fun ℓ' _ => sampleSet_subset_regSet hC (fun u hu => ?_) _
    apply hshortR
    have h1 := polyEnergy_samplePoly_le (F := F) (N := N') u
    rw [energy_of_mem_circle F ℓ' u hu] at h1
    exact h1.trans (pow_le_pow_left₀ hcm.le hcb₁.le 2)
  have hcritSg : ∀ q : ZMod N' → Sphere n, a₁ ^ 2 ≤ PolygonDescent.energy F N' q →
      PolygonDescent.energy F N' q ≤ b₁ ^ 2 → PolyCritical F N' q →
      (incl q : Om n N').1 ∈ Sg := by
    intro q ha hb hcq
    obtain ⟨ℓ', hℓ'', -, hmem⟩ := crit_mem_sampleSet M' hfin ha₁ hab₁ hone₁ hshortR hcq ha hb
    exact mem_iUnion₂.mpr ⟨ℓ', hℓ'', hmem⟩
  have hroot : ∀ κ : ℝ, 0 < κ → ∃ V₀ : (ZMod N' → Ambient n) → ZMod N' → Ambient n,
      ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧ tsupport V₀ ⊆ regSet F N' (1 / m) ∧
      (∀ z, ‖V₀ z‖ ≤ κ) ∧
      (∀ z ∈ regSet F N' (1 / m), fderiv ℝ (pen F N' (1 / m)) z (V₀ z) ≤ 0) ∧
      ∀ z ∈ regSet F N' (1 / m), (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * pen F N' (1 / m) z →
        (m : ℝ) ^ 2 * pen F N' (1 / m) z ≤ (m : ℝ) ^ 2 * b₁ ^ 2 →
        fderiv ℝ (pen F N' (1 / m)) z ≠ 0 → fderiv ℝ (pen F N' (1 / m)) z (V₀ z) < 0 := by
    intro κ hκ
    obtain ⟨V₀, h1, h2, h3, h4, h5, h6⟩ := exists_root_fields F hn hm1 hC hshortR hSgc hSgreg
      hcritSg hκ
    exact ⟨V₀, h1, h2, h3, h4, h5, fun z hz ha hb hne =>
      h6 ⟨z, hz.1⟩ (le_of_mul_le_mul_left ha hm2) (le_of_mul_le_mul_left hb hm2) hne⟩
  -- the values of the critical points of the root band
  have hrval : ∀ Q : Om n N', (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 ≤ (m : ℝ) ^ 2 * b₁ ^ 2 →
      fderiv ℝ (pen F N' (1 / m)) Q.1 = 0 → (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 = c ^ 2 := by
    intro Q h1 h2 h0
    have h1' : a₁ ^ 2 ≤ pen F N' (1 / m) Q.1 := le_of_mul_le_mul_left h1 hm2
    have h2' : pen F N' (1 / m) Q.1 ≤ b₁ ^ 2 := le_of_mul_le_mul_left h2 hm2
    have hq := hshortR _ ((energy_le_penW F hm1.le Q).trans h2')
    have hEd : DifferentiableAt ℝ (polyEnergyN F N') Q.1 :=
      (polyEnergyN_contDiffAt F Q (polyEnergyN_contDiffAt_one F hC hq)).differentiableAt
        one_ne_zero
    obtain ⟨hQ, hcQ⟩ := polyCritical_of_critical F hm1.ne' Q hEd h0
    have hpe : pen F N' (1 / m) Q.1 = PolygonDescent.energy F N' (normalizeP Q) := by
      have h := congrArg (penW F N' (1 / (m : ℝ))) hQ
      rw [penW_incl] at h
      exact h
    rw [hpe] at h1' h2' ⊢
    rw [energy_eq_of_crit F M' ha₁ hab₁ hone₁ hq hcQ h1' h2', hcsq]
  -- the rest of the root band
  obtain ⟨δ₂, hδ₂, Wrest, hWrest, hWΓ, hrcrit⟩ := exists_rest hΓc hΓne h𝒱 hΓ𝒱
    (fun Q : Om n N' => (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 ∧
      (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 ≤ (m : ℝ) ^ 2 * b₁ ^ 2 ∧
      fderiv ℝ (pen F N' (1 / m)) Q.1 = 0)
    (fun Q hP hQ => hiso𝒱 Q.1 hQ hP.2.2)
  -- the open set of root polygons
  set 𝒪 : Set (ZMod N' → Ambient n) := 𝒪f ∩ 𝒱 ∩ {z | ∀ j, z j ≠ 0} with h𝒪def
  have h𝒪 : IsOpen 𝒪 := (h𝒪f.inter h𝒱).inter isOpen_nonzero
  have hΓ𝒪 : Γ ⊆ 𝒪 := by
    intro z hz
    refine ⟨⟨?_, hΓ𝒱 hz⟩, ?_⟩
    · rw [hΓeq] at hz
      obtain ⟨a, rfl⟩ := hz
      exact hfam a
    · rw [hΓeq] at hz
      obtain ⟨a, rfl⟩ := hz
      exact (incl (rootFamily g s N a)).2
  -- the normal splitting
  have hb : (iterData g).I (s * m) - (iterData g).I s ≤
      Module.finrank ℝ (normal (rotL (n := n) m N') m) := by
    have h := (Finsler.FrameIndex.linearIndependent_of_neg
      (hneg _ (hfam 0)).1).fintype_card_le_finrank
    rwa [Fintype.card_fin] at h
  have hdim : Module.finrank ℝ (normal (rotL (n := n) m N') m) =
      Module.finrank ℝ ((Fin ((iterData g).I (s * m) - (iterData g).I s) → ℝ) ×
        (Fin (Module.finrank ℝ (normal (rotL (n := n) m N') m) -
          ((iterData g).I (s * m) - (iterData g).I s)) → ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  let ψ := ContinuousLinearEquiv.ofFinrankEq hdim
  -- the samples of the circle at the level and the iterated root polygons
  have hiterΓ : ∀ a : ℝ, amb (samplePoly K (ofSmooth (shift (iterate g.loop k) a))) =
      reidx hKm (iterA m N' (amb (rootFamily g s N ((k : ℝ) * a)))) := by
    intro a
    have h := sample_eq_iterate g s m hKm a
    rw [hsm] at h
    exact h
  have hΓ𝒰 : ∀ z ∈ Γ, reidx hKm (iterA m N' z) ∈ 𝒰 := by
    intro z hz
    rw [hΓeq] at hz
    obtain ⟨a, rfl⟩ := hz
    have h := hiterΓ (a / k)
    rw [mul_div_cancel₀ a hkR.ne'] at h
    rw [← h]
    apply h𝒰c
    rw [hcircK]
    exact ⟨a / k, rfl⟩
  -- the label in the space of the level
  have hΓτ : ∀ z ∈ Γ, rotA N' (red m N' (Finsler.CircleHalfRotation.halfIndex m s N)) z ∈ Γ := by
    intro z hz
    rw [hΓeq] at hz ⊢
    obtain ⟨a, rfl⟩ := hz
    exact ⟨a + (m * s : ℕ) / 2, Finsler.CircleHalfRotation.root_half_phase g m s N a⟩
  have hshift : reidxShift hKm (Finsler.CircleHalfRotation.halfIndex m s N) =
      (k * N : ZMod K) := by
    have hnum : m * s * N = k * N := by rw [← hsm]; ring
    unfold reidxShift Finsler.CircleHalfRotation.halfIndex
    rw [hnum]
    have hcast : ∀ (A B : ℕ) (h : A = B) (j : ℕ),
        cast (congrArg ZMod h) (j : ZMod A) = (j : ZMod B) := by
      intro A B h j
      cases h
      rfl
    simpa only [Nat.cast_mul] using hcast (m * N') K hKm (k * N)
  obtain ⟨U, W, β, C, T, 𝒲, 𝒲', Z₀, ψ₀, hUτ, hTτ, hWτ, hβτ, h𝒲τ, h𝒲'τ, -, hUo, hU𝒰, hUreg, hWs, hWle, hWlt, hTc, hTU, hβT, hβd,
    hβη, hβle, hβlt, h𝒲o, h𝒲'o, h𝒲𝒲', h𝒲T, hC𝒲', hΓT, hCval, hZ₀o, hZ₀W, hψout, hψval, hP2⟩ :=
    label_pack_half_reidx F hKm hn hG₁ hG₂ ψ (Finsler.CircleHalfRotation.halfIndex m s N)
      (Finsler.CircleHalfRotation.halfIndex_add m s N) S₁.d S₂.d S₁.signs S₂.signs
      (Finsler.CircleLabelFields.field_equivariant S₁) (Finsler.CircleLabelFields.field_equivariant S₂) h𝒪 (fun z hz => hsmooth hz.1.1)
      (fun z hz => hneg z hz.1.1) (fun z hz => hz.2) hΓc hΓ𝒪 hΓτ
      (fun z hz h0 => hiso𝒱 z hz.1.2 h0) hΓval hroot hKr hbandreg hWrest hδ₂ hWΓ
      (fun Q h1 h2 h3 => hrcrit Q ⟨h1, h2, h3⟩) h𝒰 hΓ𝒰
      (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hac₁ ha₁.le two_ne_zero) hm2 |>.trans_eq hcsq)
      (hcsq.symm.trans_lt (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hcb₁ hcm.le two_ne_zero) hm2))
      hΓc₀ hrval hη
  rw [hshift] at hUτ hTτ hWτ hβτ h𝒲τ h𝒲'τ
  -- the root labels are at most the loop crossing of the root band
  have hhc : Continuous fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1 :=
    continuous_const.mul (penW_continuous F hn (1 / (m : ℝ)))
  have hab1 : a₁ ^ 2 ≤ b₁ ^ 2 := pow_le_pow_left₀ ha₁.le hab₁ 2
  have hab1m : (m : ℝ) ^ 2 * a₁ ^ 2 ≤ (m : ℝ) ^ 2 * b₁ ^ 2 :=
    mul_le_mul_of_nonneg_left hab1 hm2.le
  obtain ⟨dr, hdr, hlc⟩ := lens_le_cross ψ₀ hhc
    (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hac₁ ha₁.le two_ne_zero) hm2 |>.trans_eq hcsq)
    (hcsq.symm.trans_lt (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hcb₁ hcm.le two_ne_zero) hm2))
    hKr hZ₀o hWrest hZ₀W hψout hψval hab1m
  have hsub : ∀ x : ℝ, sub (penW F N' (1 / (m : ℝ))) (x ^ 2) = sub (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) ((m : ℝ) ^ 2 * x ^ 2) := by
    intro x
    ext Q
    change pen F N' (1 / m) Q.1 < x ^ 2 ↔ (m : ℝ) ^ 2 * pen F N' (1 / m) Q.1 < (m : ℝ) ^ 2 * x ^ 2
    constructor
    · intro h
      exact mul_lt_mul_of_pos_left h hm2
    · intro h
      exact lt_of_mul_lt_mul_left h hm2.le
  have hbound : ∃ dr : ℝ, 0 < dr ∧ ∀ a c' t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < c' → c' - a < dr →
      ∀ j : ℕ, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
        ((s : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ').loop)))))) j) →
      finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
        baseP (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) {z : Om n N' | z.1 ∈ Z₀} c' ∩ baseO ψ₀ a t ⊆
          baseP (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) {z : Om n N' | z.1 ∈ Z₀} c'))) j) ≤
        finrank (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
          ((s : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ').loop)))))) j) := by
    refine ⟨dr, hdr, fun a c' t ht ha hc' hd j hfinL => ?_⟩
    obtain ⟨e₁⟩ := nonempty_loop_equiv M' hm1.le (fun q hq => hshortR q hq.le) ha₁ hab₁ le_rfl j
    have t₂ := transfer _ (eq_bijective (sub_mono (penW F N' (1 / (m : ℝ))) hab1)
      (sub_mono (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) hab1m) (hsub a₁) (hsub b₁) j)
    have hfinP : Module.Finite (ZMod 2) (crossH (penW F N' (1 / (m : ℝ))) hab1 j) := by
      have := hfinL
      exact Module.Finite.equiv e₁
    have hfinX : Module.Finite (ZMod 2) (crossH (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) hab1m j) := t₂.1.mpr hfinP
    obtain ⟨-, hlle⟩ := hlc a c' t ht ha hc' hd j hfinX
    have hs' : partY (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) ψ₀ {z : Om n N' | z.1 ∈ Z₀} a c' t =
        baseP (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) {z : Om n N' | z.1 ∈ Z₀} c' ∩ baseO ψ₀ a t := by
      ext w
      simp only [partY, baseP, baseO, mem_inter_iff, mem_ofPred_eq]
      tauto
    have t₃ := transfer _ (eq_bijective (partY_sub_partU (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) ψ₀ {z : Om n N' | z.1 ∈ Z₀} a c' t)
      (inter_subset_left : baseP (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) {z : Om n N' | z.1 ∈ Z₀} c' ∩ baseO ψ₀ a t ⊆
        baseP (fun z : Om n N' => (m : ℝ) ^ 2 * pen F N' (1 / m) z.1) {z : Om n N' | z.1 ∈ Z₀} c') hs' rfl j)
    rw [t₃.2]
    exact hlle.trans (t₂.2.trans e₁.finrank_eq.symm).le
  refine ⟨(iterData g).I (s * m) - (iterData g).I s, _, U, W, β, C ∩ U, T, 𝒲, 𝒲', hUτ, hTτ, hWτ, hβτ, h𝒲τ, h𝒲'τ, by rw [hsm],
    hUo, hU𝒰,
    hUreg, hWs, hWle, fun y hy hyC => hWlt y hy fun h => hyC ⟨h, hy⟩, hTc, hTU, hβT, hβd, hβη,
    hβle, fun y hy hyC => hβlt y hy fun h => hyC ⟨h, hTU (hβT hy)⟩, h𝒲o, h𝒲'o, h𝒲𝒲', h𝒲T,
    fun Q hQ => hC𝒲' Q hQ.1, inter_subset_right, ?_, fun y hy => hCval y hy.1, hbound, hP2⟩
  rw [hcircK]
  rintro _ ⟨a, rfl⟩
  rw [hiterΓ a]
  apply hΓT
  rw [hΓeq]
  exact ⟨_, rfl⟩


set_option maxHeartbeats 1600000 in
/-- **The label of a critical circle.** Forget the additional half-equivariance conclusions. -/
theorem circle_label (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K], k * (2 * N) = K →
      ∀ {𝒰 : Set (ZMod K → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
      ∃ (b : ℕ) (r : ℝ → ℝ → ℝ → ℕ → ℕ) (U : Set (ZMod K → Ambient n))
        (W : (ZMod K → Ambient n) → ZMod K → Ambient n)
        (β : (ZMod K → Ambient n) → ℝ) (C T : Set (ZMod K → Ambient n)) (𝒲 𝒲' : Set (Om n K)),
        b = (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k -
          (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I
            (Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L)) ∧
        IsOpen U ∧ U ⊆ 𝒰 ∧ U ⊆ regSet F K 1 ∧ ContDiffOn ℝ ∞ W U ∧
        (∀ y ∈ U, fderiv ℝ (pen F K 1) y (W y) ≤ 0) ∧
        (∀ y ∈ U, y ∉ C → fderiv ℝ (pen F K 1) y (W y) < 0) ∧
        IsCompact T ∧ T ⊆ U ∧ tsupport β ⊆ T ∧ (∀ y, DifferentiableAt ℝ β y) ∧
        (∀ y, |β y| ≤ η) ∧
        (∀ y ∈ tsupport β, fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) ≤ 0) ∧
        (∀ y ∈ tsupport β, y ∉ C → fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) < 0) ∧
        IsOpen 𝒲 ∧ IsOpen 𝒲' ∧ 𝒲' ⊆ 𝒲 ∧ (∀ Q ∈ 𝒲, Q.1 ∈ T) ∧
        (∀ Q : Om n K, Q.1 ∈ C → Q ∈ 𝒲') ∧ C ⊆ U ∧
        (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ T) ∧
        (∀ y ∈ C, pen F K 1 y = c ^ 2 ∧ β y = 0) ∧
        (∃ dr : ℝ, 0 < dr ∧ ∀ a c' t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < c' → c' - a < dr →
          ∀ j : ℕ, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
            ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
              Real.sqrt (Finsler.LoopEnergy.energy F
                (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j) →
          r a c' t j ≤ finrank (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
            ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
              Real.sqrt (Finsler.LoopEnergy.energy F
                (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j)) ∧
        ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
          (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
          {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
          (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
          (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
          (∀ y ∈ T, V y = W y) → (∀ y ∈ T, g y = pen F K 1 y + β y) →
          ∀ {a₀a b₀a : ℝ}, a₀a < c ^ 2 → c ^ 2 < b₀a → Continuous (fun Q : Om n K => g Q.1) →
          IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a} →
          ∀ {R : Set (Om n K)}, IsOpen R → Disjoint 𝒲 R →
          (∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ 𝒲' ∪ R →
            g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
          ∃ d : ℝ, 0 < d ∧ ∀ a c' t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < c' → c' - a < d →
            (∀ j : ℕ, finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
                (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c' t))) (j + b)) =
              r a c' t j) ∧
            (∀ j : ℕ, j < b → ∀ x : H (triv (pairOf (partY_sub_partU
                (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c' t))) j,
              x = 0) := by
  obtain ⟨N₀, hN₀⟩ := circle_label_half F hn hfin hc hℓ hkc
  refine ⟨N₀, fun N hN _ K _ hK 𝒰 h𝒰 h𝒰c η hη => ?_⟩
  obtain ⟨b, r, U, W, β, C, T, 𝒲, 𝒲', -, -, -, -, -, -, properties⟩ :=
    hN₀ N hN hK h𝒰 h𝒰c hη
  exact ⟨b, r, U, W, β, C, T, 𝒲, 𝒲', properties⟩

end

end Finsler.CircleLabel
