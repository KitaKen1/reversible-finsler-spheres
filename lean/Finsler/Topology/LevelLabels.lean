module

public import Finsler.Topology.CircleLabel
public import Finsler.Geometry.LevelCrossing

/-! The crossing of a critical level as a sum of shifted root labels. With finitely many prime
closed geodesic images, let c be the only critical level in [a₀, b₀], 0 < a₀ < c < b₀. The labels
with a critical circle at the level c form a finite set; the circle of such a label consists of
the rotations of the k-fold iterate of its closed geodesic with k √E = c. There are L > 0 and
K_min such that for every number of vertices K ≥ K_min divisible by L and all cuts
a₀ ≤ a < c < b ≤ b₀ there are numbers b_ℓ = I(k) - I(gcd(k, 2L_ℓ)) and dimensions r_ℓ of root
labels, and d > 0, such that for all tight cuts a' < c² < c' with c' - a' < d and times T ≥ 1 the
crossing pair of the penalized energy with K vertices at the cuts a², b² has in every degree q in
which it is finite dimensional the dimension Σ_ℓ r_ℓ(q - b_ℓ) over the labels with b_ℓ ≤ q.
The labels of the level are built by `circle_label` inside pairwise disjoint open sets of
polygons near pairwise disjoint neighbourhoods of the circles, and `level_crossing` adds them.
For tight cuts the root label of a label with k√E = c is at most the ordinary cohomology of the
loop pair of the chosen isolated band around its root level gcd(k, 2L) √E. -/

@[expose] public section

namespace Finsler.LevelLabels

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.Loops
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel
open Finsler.PolygonDescent Finsler.CriticalLevels Finsler.OrientedCritical
open Finsler.CriticalCircles Finsler.SmoothSobolev Finsler.EnergyDiagonal
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.PolygonOriented
open Finsler.GeodesicFrames Finsler.PhaseNullity Finsler.SamplePhase Finsler.AmbientLoopPairs
open Finsler.LevelField Finsler.RootIsolation Finsler.CircleSampling Finsler.CircleRoot
open Finsler.CircleLabel Finsler.LoopCrossingOriented Finsler.LevelCrossing Finsler.LensFamily
open CategoryTheory Finsler.BorelCochain Finsler.BorelLoop Finsler.PairTriple
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

set_option maxHeartbeats 3200000 in
/-- **The crossing of a critical level as a sum of shifted root labels.** -/
theorem level_labels (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hac : a₀ < c) (hcb : c < b₀) (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) :
    ∃ L Kmin : ℕ, 0 < L ∧ ∀ K : ℕ, Kmin ≤ K → L ∣ K → ∀ [NeZero K] {a b : ℝ}
      (hab : a ^ 2 ≤ b ^ 2), a₀ ≤ a → a < c → c < b → b ≤ b₀ →
      ∃ (s : Finset (Set (Sphere n) × Bool)) (bi : Set (Sphere n) × Bool → ℕ)
        (r : Set (Sphere n) × Bool → ℝ → ℝ → ℝ → ℕ → ℕ) (d : ℝ),
        (∀ ℓ ∈ s, ∃ hℓ : ℓ ∈ labels F hfin, ∃ k : ℕ,
          (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
            (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c ∧
          bi ℓ = (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k -
            (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I
              (Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L)) ∧
          (∃ dr : ℝ, 0 < dr ∧ ∀ a' c' t : ℝ, 1 ≤ t → a' < c ^ 2 → c ^ 2 < c' → c' - a' < dr →
            ∀ j : ℕ, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
              ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
                Real.sqrt (Finsler.LoopEnergy.energy F
                  (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j) →
            r ℓ a' c' t j ≤ finrank (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
              ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
                Real.sqrt (Finsler.LoopEnergy.energy F
                  (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j))) ∧
        0 < d ∧ ∀ a' c' t : ℝ, 1 ≤ t → a' < c ^ 2 → c ^ 2 < c' → c' - a' < d → ∀ q : ℕ,
          Module.Finite (ZMod 2) (crossH (penW F K 1) hab q) →
          finrank (ZMod 2) (crossH (penW F K 1) hab q) =
            ∑ ℓ ∈ s, if bi ℓ ≤ q then r ℓ a' c' t (q - bi ℓ) else 0 := by
  classical
  have hc : 0 < c := ha₀.trans hac
  have hab₀ : a₀ ≤ b₀ := (hac.trans hcb).le
  -- the labels with a circle at the level
  set s := (labels F hfin).filter fun ℓ => (circle F c ℓ).Nonempty with hsdef
  have hsl : ∀ ℓ ∈ s, ℓ ∈ labels F hfin := fun ℓ hℓ => (Finset.mem_filter.mp hℓ).1
  have hkex : ∀ ℓ ∈ s, ∃ k : ℕ, ∀ hs : ℓ.1 ∈ primeImages F,
      (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hs).loop) = c := by
    intro ℓ hℓ
    obtain ⟨-, u, hu⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨si, o⟩ := ℓ
    cases o
    · obtain ⟨_, ⟨hs, k, θ, -, hkc, -⟩, -⟩ := hu
      exact ⟨k, fun _ => hkc⟩
    · obtain ⟨hs, k, θ, -, hkc, -⟩ := hu
      exact ⟨k, fun _ => hkc⟩
  choose! kk hkk using hkex
  have hkpos : ∀ ℓ ∈ s, 0 < kk ℓ := by
    intro ℓ hℓ
    have h := hkk ℓ hℓ ((mem_labels F hfin ℓ).mp (hsl ℓ hℓ))
    rcases Nat.eq_zero_or_pos (kk ℓ) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul] at h
      exact absurd h hc.ne
    · exact h0
  -- the labels of the circles for all large numbers of vertices
  have hcl := fun ℓ (hℓ : ℓ ∈ s) => circle_label F hn hfin hc (hsl ℓ hℓ)
    (hkk ℓ hℓ ((mem_labels F hfin ℓ).mp (hsl ℓ hℓ)))
  choose! N₀ hN₀ using hcl
  -- segment data and polygon models in the space of the level
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨δ₁, hδ₁, hC1⟩ := exists_ambientMinEnergy_contDiffAt_one F
  set S := shrink S₀ (lt_min S₀.pos hδ₁) (min_le_left _ _) with hS
  have hSδ : S.δ ≤ δ₁ := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := b₀) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b₀ ^ 2 / (e * S.δ ^ 2))
  have hsf : ∀ ℓ ∈ s, ∃ K₀ : ℕ, ∀ hs : ℓ.1 ∈ primeImages F, ∀ a : ℝ, ∀ K : ℕ, K₀ ≤ K →
      ∀ [NeZero K], SampleFacts S (ofSmooth (shift (labelGeod F ℓ hs).loop a)) K := by
    intro ℓ hℓ
    obtain ⟨K₀, h⟩ := exists_sample_facts_all S
      (labelGeod F ℓ ((mem_labels F hfin ℓ).mp (hsl ℓ hℓ)))
    exact ⟨K₀, fun _ => h⟩
  choose! K₀ hK₀ using hsf
  -- the period of the vertex numbers
  set L : ℕ := 2 * ∏ ℓ ∈ s, kk ℓ with hLdef
  have hL : 0 < L := by
    rw [hLdef]
    exact Nat.mul_pos two_pos (Finset.prod_pos fun ℓ hℓ => hkpos ℓ hℓ)
  have hkL : ∀ ℓ ∈ s, 2 * kk ℓ ∣ L := fun ℓ hℓ =>
    Nat.mul_dvd_mul_left 2 (Finset.dvd_prod_of_mem kk hℓ)
  set Nmax : ℕ := ∑ ℓ ∈ s, (N₀ ℓ + K₀ ℓ) with hNmax
  have hNmax : ∀ ℓ ∈ s, N₀ ℓ + K₀ ℓ ≤ Nmax := fun ℓ hℓ =>
    Finset.single_le_sum (f := fun ℓ => N₀ ℓ + K₀ ℓ) (fun _ _ => Nat.zero_le _) hℓ
  refine ⟨L, L * (Nmax + 1) + N₁ + N₂, hL, fun K hK hLK _ a b hab ha₀a hac' hcb' hbb₀ => ?_⟩
  -- the vertex numbers of the labels
  have hKL : L * (Nmax + 1) ≤ K := by omega
  have hNl : ∀ ℓ ∈ s, kk ℓ * (2 * (K / (2 * kk ℓ))) = K := by
    intro ℓ hℓ
    have h := Nat.div_mul_cancel ((hkL ℓ hℓ).trans hLK)
    calc kk ℓ * (2 * (K / (2 * kk ℓ))) = K / (2 * kk ℓ) * (2 * kk ℓ) := by ring
      _ = K := h
  have hNl' : ∀ ℓ ∈ s, Nmax + 1 ≤ K / (2 * kk ℓ) := by
    intro ℓ hℓ
    obtain ⟨j, hj⟩ := hkL ℓ hℓ
    have hpos : 0 < 2 * kk ℓ := Nat.mul_pos two_pos (hkpos ℓ hℓ)
    rw [Nat.le_div_iff_mul_le hpos]
    calc (Nmax + 1) * (2 * kk ℓ) ≤ (Nmax + 1) * (2 * kk ℓ * j) := by
          apply Nat.mul_le_mul_left
          have : 0 < j := Nat.pos_of_ne_zero fun h0 => by
            rw [h0, mul_zero] at hj
            omega
          nlinarith
      _ = L * (Nmax + 1) := by rw [hj]; ring
      _ ≤ K := hKL
  -- the model in the space of the level
  have hKpos : 0 < K := Nat.pos_of_neZero K
  let MK : PolygonModelData F b₀ K :=
    PolygonModelData.mk S fun u hu s' t hs' ht hst =>
      hN₁ K (by omega) hKpos u hu s' t hs' ht hst
  have hKR : b₀ ^ 2 / (e * S.δ ^ 2) < K :=
    hN₂.trans_le (Nat.cast_le.mpr (by omega))
  have hshortK : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q ≤ b₀ ^ 2 →
      ShortPolygon MK.δ q := fun q hq => short_of_energy_le he S.pos hedge hKR q hq
  have hCK : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < MK.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q h => hC1 P Q (h.trans_le hSδ)
  -- disjoint neighbourhoods of the circles
  obtain ⟨Ul, hUl, hUldis⟩ := exists_disjoint_nhds (labels F hfin) (circle F c)
    (fun ℓ' _ => isCompact_circle F c ℓ') (fun ℓ₁ _ ℓ₂ _ hne => circle_disjoint F c hne)
  -- the margin η
  have ha2 : a ^ 2 < c ^ 2 := pow_lt_pow_left₀ hac' (ha₀.le.trans ha₀a) two_ne_zero
  have hb2 : c ^ 2 < b ^ 2 := pow_lt_pow_left₀ hcb' hc.le two_ne_zero
  set η : ℝ := min (c ^ 2 - a ^ 2) (b ^ 2 - c ^ 2) / 2 with hηdef
  have hη : 0 < η := half_pos (lt_min (by linarith) (by linarith))
  have hη1 : a ^ 2 + η < c ^ 2 := by
    have := min_le_left (c ^ 2 - a ^ 2) (b ^ 2 - c ^ 2)
    rw [hηdef]
    linarith
  have hη2 : c ^ 2 < b ^ 2 - η := by
    have := min_le_right (c ^ 2 - a ^ 2) (b ^ 2 - c ^ 2)
    rw [hηdef]
    linarith
  -- the open sets of the labels
  set 𝒰 : Set (Sphere n) × Bool → Set (ZMod K → Ambient n) := fun ℓ =>
    Subtype.val '' (nearOm MK (Ul ℓ) ∩
      {Q : Om n K | a ^ 2 + η < penW F K 1 Q ∧ penW F K 1 Q < b ^ 2 - η}) with h𝒰def
  have h𝒰o : ∀ ℓ ∈ s, IsOpen (𝒰 ℓ) := fun ℓ hℓ =>
    (isOpen_nonzero (N := K)).isOpenMap_subtype_val _
      ((nearOm_isOpen MK (hUl ℓ (hsl ℓ hℓ)).1).inter
        ((isOpen_lt continuous_const (penW_continuous F hn 1)).inter
          (isOpen_lt (penW_continuous F hn 1) continuous_const)))
  have h𝒰c : ∀ ℓ ∈ s, ∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ 𝒰 ℓ := by
    intro ℓ hℓ u hu
    have hs' := (mem_labels F hfin ℓ).mp (hsl ℓ hℓ)
    have : NeZero (K / (2 * kk ℓ)) := ⟨by have := hNl' ℓ hℓ; omega⟩
    have hf : ∀ x : ℝ, SampleFacts S (ofSmooth (shift (labelGeod F ℓ hs').loop x))
        (2 * (K / (2 * kk ℓ))) := by
      intro x
      exact hK₀ ℓ hℓ hs' x (2 * (K / (2 * kk ℓ)))
        (by have := hNmax ℓ hℓ; have := hNl' ℓ hℓ; omega)
    have h2N : 1 < 2 * (K / (2 * kk ℓ)) := by have := hNl' ℓ hℓ; omega
    rw [circle_eq F hc ℓ hs' (hkk ℓ hℓ hs')] at hu
    obtain ⟨x, rfl⟩ := hu
    have hq := short_iterate S (labelGeod F ℓ hs').loop (kk ℓ) h2N hf (hNl ℓ hℓ) x
    have hbr := broken_iterate S (labelGeod F ℓ hs').loop (kk ℓ) h2N hf (hNl ℓ hℓ) x hq
    have hcirc : ofSmooth (shift (iterate (labelGeod F ℓ hs').loop (kk ℓ)) x) ∈ circle F c ℓ := by
      rw [circle_eq F hc ℓ hs' (hkk ℓ hℓ hs')]
      exact ⟨x, rfl⟩
    refine ⟨incl (samplePoly K (ofSmooth (shift (iterate (labelGeod F ℓ hs').loop (kk ℓ)) x))),
      ⟨?_, ?_⟩, rfl⟩
    · change normalizeP (incl _) ∈ near MK (Ul ℓ)
      rw [normalizeP_incl]
      refine ⟨hq, ?_⟩
      change polySphereLoop F MK.seg hq ∈ Ul ℓ
      rw [hbr]
      exact (hUl ℓ (hsl ℓ hℓ)).2 hcirc
    · have h := energy_broken MK ⟨_, hq⟩
      change Finsler.SobolevEnergy.energy F (polySphereLoop F MK.seg hq) = _ at h
      rw [hbr, energy_of_mem_circle F ℓ _ hcirc] at h
      have h' : PolygonDescent.energy F K
          (samplePoly K (ofSmooth (shift (iterate (labelGeod F ℓ hs').loop (kk ℓ)) x))) =
            c ^ 2 := h.symm
      have h'' : penW F K 1 (incl (samplePoly K
          (ofSmooth (shift (iterate (labelGeod F ℓ hs').loop (kk ℓ)) x)))) = c ^ 2 := by
        rw [penW_incl, h']
      show a ^ 2 + η < penW F K 1 (incl _) ∧ penW F K 1 (incl _) < b ^ 2 - η
      rw [h'']
      exact ⟨hη1, hη2⟩
  have h𝒰dis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (𝒰 i) (𝒰 j) := by
    intro i hi j hj hij
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨Q, hQ, rfl⟩ ⟨Q', hQ', hQQ⟩
    have he : Q' = Q := Subtype.ext hQQ
    subst he
    exact Set.disjoint_left.mp (nearOm_disjoint MK (hUldis (hsl i hi) (hsl j hj) hij)) hQ.1 hQ'.1
  -- the labels of the level
  have hdata := fun ℓ (hℓ : ℓ ∈ s) =>
    @hN₀ ℓ hℓ (K / (2 * kk ℓ)) (by have := hNmax ℓ hℓ; have := hNl' ℓ hℓ; omega)
      ⟨by have := hNl' ℓ hℓ; omega⟩ K _ (hNl ℓ hℓ) (𝒰 ℓ) (h𝒰o ℓ hℓ) (h𝒰c ℓ hℓ) η hη
  choose! bi r U W β C T 𝒲 𝒲' hbi hUo hU𝒰 hUreg hWs hWle hWlt hTc hTU hβT hβd hβη hβle hβlt
    h𝒲o h𝒲'o h𝒲𝒲' h𝒲T hC𝒲 hCU hcircT hCval hbound hP2 using hdata
  have hUdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j) := fun i hi j hj hij =>
    (h𝒰dis i hi j hj hij).mono (hU𝒰 i hi) (hU𝒰 j hj)
  have hTval : ∀ i ∈ s, ∀ y ∈ T i, a ^ 2 + η < pen F K 1 y ∧ pen F K 1 y < b ^ 2 - η := by
    intro i hi y hy
    obtain ⟨Q, ⟨-, h1, h2⟩, rfl⟩ := hU𝒰 i hi (hTU i hi hy)
    exact ⟨h1, h2⟩
  have hcrit : ∀ q : ZMod K → Sphere n, a₀ ^ 2 ≤ PolygonDescent.energy F K q →
      PolygonDescent.energy F K q ≤ b₀ ^ 2 → PolyCritical F K q →
        (incl q : Om n K).1 ∈ ⋃ i ∈ s, T i := by
    intro q h1 h2 h3
    obtain ⟨ℓ, hℓ, hmem, u, hu, hqu⟩ :=
      crit_mem_sampleSet MK hfin ha₀ hab₀ hone hshortK h3 h1 h2
    have hℓs : ℓ ∈ s := Finset.mem_filter.mpr ⟨hℓ, _, hmem⟩
    refine mem_iUnion₂.mpr ⟨ℓ, hℓs, ?_⟩
    change amb q ∈ T ℓ
    rw [← hqu]
    exact hcircT ℓ hℓs u hu
  have hab2 : a₀ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ ha₀.le ha₀a 2
  have hbb2 : b ^ 2 ≤ b₀ ^ 2 := pow_le_pow_left₀ (hc.le.trans hcb'.le) hbb₀ 2
  obtain ⟨d, hd, hcross⟩ := level_crossing F hn hCK hshortK s hUo hUreg hUdis hWs hWle hWlt
    hTc hTU hβT hβd hβle hβlt h𝒲o h𝒲𝒲' h𝒲T hC𝒲 hCU hCval hβη hab2 hbb2 ha2 hb2 hTval hcrit
    bi r hP2 hab
  refine ⟨s, bi, r, d, fun ℓ hℓ => ⟨hsl ℓ hℓ, kk ℓ, hkk ℓ hℓ _, hbi ℓ hℓ, hbound ℓ hℓ⟩, hd,
    hcross⟩

end

end Finsler.LevelLabels
