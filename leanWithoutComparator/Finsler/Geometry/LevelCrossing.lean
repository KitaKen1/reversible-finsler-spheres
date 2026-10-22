module

public import Finsler.Geometry.LevelDescent
public import Finsler.Topology.CutMove

/-! The crossing of a level. Let finitely many labels of the ambient polygons with K vertices be
given as in the descent of a level, with deformations bounded by η which vanish on the sets C_i
where the penalized energy has the value c₀, and with the pieces T_i inside the strip where the
penalized energy lies η-strictly between the wide cuts a_w < c₀ < b_w. Let every label have open
sets 𝒲'_i ⊆ 𝒲_i over T_i containing the polygons over C_i, and the property that for every
descent agreeing with W_i on T_i of a function equal to pen + β_i on T_i which decreases strictly
outside 𝒲'_i and an open set disjoint from 𝒲_i, the lens pairs of 𝒲_i for tight cuts around c₀
have in degree k + b_i the dimension r_i(k) and no cohomology below b_i. Then for all
sufficiently tight cuts a < c₀ < c and times T ≥ 1, the crossing pair of the penalized energy at
the wide cuts, if finite dimensional in degree q, has in degree q the dimension
Σ_i r_i(q - b_i) (over the labels with b_i ≤ q). The cuts move through regular strips, the
deformed energy has the same sublevels as the penalized energy at the wide cuts, and the crossing
of the deformed energy is the sum of its labels. -/

@[expose] public section

namespace Finsler.LevelCrossing

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PolygonDescent
open Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens Finsler.AmbientPenalty
open Finsler.AmbientDescent Finsler.LevelField Finsler.LevelBuild Finsler.LevelDescent
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation Finsler.LensFamily Finsler.CutMove
open Set Filter Module
open scoped Topology ContDiff NNReal

noncomputable section

/-- A bijective linear map preserves finiteness and dimension. -/
theorem transfer {M₁ M₂ : Type} [AddCommGroup M₁] [Module (ZMod 2) M₁] [AddCommGroup M₂]
    [Module (ZMod 2) M₂] (f : M₁ →ₗ[ZMod 2] M₂) (hf : Function.Bijective f) :
    (Module.Finite (ZMod 2) M₁ ↔ Module.Finite (ZMod 2) M₂) ∧
      finrank (ZMod 2) M₁ = finrank (ZMod 2) M₂ :=
  ⟨⟨fun _ => Module.Finite.equiv (LinearEquiv.ofBijective f hf),
    fun _ => Module.Finite.equiv (LinearEquiv.ofBijective f hf).symm⟩,
    (LinearEquiv.ofBijective f hf).finrank_eq⟩

/-- **Moving to tight cuts.** If g and h have the same sublevels at the wide cuts a_w ≤ b_w and
the time-one map of a descent of g decreases g strictly on the compact strips between a_w and a
and between c and b_w, the crossing pair of h at the wide cuts has the cohomology of the crossing
pair of g at the tight cuts. -/
theorem cross_move {W : TopCat.{0}} {g h : W → ℝ} (D : Descent W g) (hgc : Continuous g)
    {aw a c bw : ℝ} (haw : aw ≤ a) (hac : a ≤ c) (hcb : c ≤ bw)
    (hK₁ : IsCompact {w : W | aw ≤ g w ∧ g w ≤ a}) (hK₂ : IsCompact {w : W | c ≤ g w ∧ g w ≤ bw})
    (hs₁ : ∀ w, aw ≤ g w → g w ≤ a → g (D.flow 1 w) < g w)
    (hs₂ : ∀ w, c ≤ g w → g w ≤ bw → g (D.flow 1 w) < g w)
    (hsa : sub h aw = sub g aw) (hsb : sub h bw = sub g bw) (habw : aw ≤ bw) (q : ℕ) :
    (Module.Finite (ZMod 2) (crossH h habw q) ↔ Module.Finite (ZMod 2) (crossH g hac q)) ∧
      finrank (ZMod 2) (crossH h habw q) = finrank (ZMod 2) (crossH g hac q) := by
  obtain ⟨s₂, hs₂0, hpush₂⟩ := exists_push_lt D hgc hK₂ hs₂
  obtain ⟨s₁, hs₁0, hpush₁⟩ := exists_push_lt D hgc hK₁ hs₁
  have t₁ := transfer _ (eq_bijective (sub_mono h habw) (sub_mono g habw) hsa hsb q)
  have t₂ := transfer _ (upper_bijective D (haw.trans hac) hcb hs₂0 hpush₂ q)
  have t₃ := transfer _ (lower_bijective D haw hac hs₁0 hpush₁ q)
  exact ⟨t₁.1.symm.trans (t₂.1.trans t₃.1.symm), t₁.2.symm.trans (t₂.2.trans t₃.2.symm)⟩

/-- The dimension of a family of modules shifted by b. -/
theorem finrank_shift (M : ℕ → Type) [∀ k, AddCommGroup (M k)] [∀ k, Module (ZMod 2) (M k)]
    {b : ℕ} {r : ℕ → ℕ} (h1 : ∀ k, finrank (ZMod 2) (M (k + b)) = r k)
    (h2 : ∀ k, k < b → ∀ x : M k, x = 0) (q : ℕ) :
    finrank (ZMod 2) (M q) = if b ≤ q then r (q - b) else 0 := by
  by_cases hbq : b ≤ q
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hbq
    rw [ite_eq_left hbq, Nat.add_sub_cancel]
    exact h1 k
  · rw [ite_eq_right hbq]
    have : Subsingleton (M q) :=
      ⟨fun x y => (h2 q (not_le.mp hbq) x).trans (h2 q (not_le.mp hbq) y).symm⟩
    exact finrank_zero_of_subsingleton

variable {n : ℕ} {K : ℕ} [NeZero K]

set_option maxHeartbeats 800000 in
/-- **The crossing of a level.** -/
theorem level_crossing (F : ReversibleMetric n) (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q ≤ b₀ → ShortPolygon δ q)
    {ι : Type*} (s : Finset ι) {U : ι → Set (ZMod K → Ambient n)}
    {W : ι → (ZMod K → Ambient n) → ZMod K → Ambient n}
    {β : ι → (ZMod K → Ambient n) → ℝ} {C T : ι → Set (ZMod K → Ambient n)}
    {𝒲 𝒲' : ι → Set (Om n K)}
    (hU : ∀ i ∈ s, IsOpen (U i)) (hUO : ∀ i ∈ s, U i ⊆ regSet F K 1)
    (hUdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (hW : ∀ i ∈ s, ContDiffOn ℝ ∞ (W i) (U i))
    (hWle : ∀ i ∈ s, ∀ y ∈ U i, fderiv ℝ (pen F K 1) y (W i y) ≤ 0)
    (hWlt : ∀ i ∈ s, ∀ y ∈ U i, y ∉ C i → fderiv ℝ (pen F K 1) y (W i y) < 0)
    (hT : ∀ i ∈ s, IsCompact (T i)) (hTU : ∀ i ∈ s, T i ⊆ U i)
    (hβT : ∀ i ∈ s, tsupport (β i) ⊆ T i) (hβd : ∀ i ∈ s, ∀ y, DifferentiableAt ℝ (β i) y)
    (hβle : ∀ i ∈ s, ∀ y ∈ tsupport (β i),
      fderiv ℝ (fun y => pen F K 1 y + β i y) y (W i y) ≤ 0)
    (hβlt : ∀ i ∈ s, ∀ y ∈ tsupport (β i), y ∉ C i →
      fderiv ℝ (fun y => pen F K 1 y + β i y) y (W i y) < 0)
    (h𝒲 : ∀ i ∈ s, IsOpen (𝒲 i)) (h𝒲𝒲' : ∀ i ∈ s, 𝒲' i ⊆ 𝒲 i)
    (h𝒲T : ∀ i ∈ s, ∀ Q ∈ 𝒲 i, Q.1 ∈ T i)
    (hC𝒲 : ∀ i ∈ s, ∀ Q : Om n K, Q.1 ∈ C i → Q ∈ 𝒲' i)
    (hCU : ∀ i ∈ s, C i ⊆ U i) {c₀ : ℝ}
    (hCval : ∀ i ∈ s, ∀ y ∈ C i, pen F K 1 y = c₀ ∧ β i y = 0)
    {η : ℝ} (hβη : ∀ i ∈ s, ∀ y, |β i y| ≤ η)
    {aw bw : ℝ} (ha₀ : a₀ ≤ aw) (hb₀ : bw ≤ b₀) (hac₀ : aw < c₀) (hc₀b : c₀ < bw)
    (hTval : ∀ i ∈ s, ∀ y ∈ T i, aw + η < pen F K 1 y ∧ pen F K 1 y < bw - η)
    (hcrit : ∀ q : ZMod K → Sphere n, a₀ ≤ PolygonDescent.energy F K q →
      PolygonDescent.energy F K q ≤ b₀ → PolyCritical F K q →
        (incl q : Om n K).1 ∈ ⋃ i ∈ s, T i)
    (b : ι → ℕ) (r : ι → ℝ → ℝ → ℝ → ℕ → ℕ)
    (hP2 : ∀ i ∈ s, ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
        (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
        {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
        (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
        (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
        (∀ y ∈ T i, V y = W i y) → (∀ y ∈ T i, g y = pen F K 1 y + β i y) →
        ∀ {a₀a b₀a : ℝ}, a₀a < c₀ → c₀ < b₀a → Continuous (fun Q : Om n K => g Q.1) →
        IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a} →
        ∀ {R : Set (Om n K)}, IsOpen R → Disjoint (𝒲 i) R →
        (∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ 𝒲' i ∪ R →
          g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
        ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d →
          (∀ k : ℕ, finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
              (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) (𝒲 i) a c t))) (k + b i)) =
            r i a c t k) ∧
          (∀ k : ℕ, k < b i → ∀ x : H (triv (pairOf (partY_sub_partU
              (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) (𝒲 i) a c t))) k,
            x = 0))
    (habw : aw ≤ bw) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d → ∀ q : ℕ,
      Module.Finite (ZMod 2) (crossH (penW F K 1) habw q) →
      finrank (ZMod 2) (crossH (penW F K 1) habw q) =
        ∑ i ∈ s, if b i ≤ q then r i a c t (q - b i) else 0 := by
  classical
  -- the descent of the level
  obtain ⟨V, KL, hL, hV0, hg, hsupp, hle, hVT, hlt⟩ := exists_level_descent F hn hδ hshort s
    hU hUO hUdis hW hWle hWlt hT hTU hβT hβd hβle hβlt hcrit
  -- the deformations
  have hη : ∀ i ∈ s, 0 ≤ η := fun i hi => (abs_nonneg _).trans (hβη i hi 0)
  have hβzero : ∀ i ∈ s, ∀ y, y ∉ T i → β i y = 0 := fun i hi y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hβT i hi h))
  have hTdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ y ∈ T i, y ∉ T j := fun i hi j hj hij y hy hy' =>
    Set.disjoint_left.mp (hUdis i hi j hj hij) (hTU i hi hy) (hTU j hj hy')
  have hsumT : ∀ i ∈ s, ∀ y ∈ T i, ∑ j ∈ s, β j y = β i y := fun i hi y hy =>
    Finset.sum_eq_single_of_mem i hi fun j hj hji =>
      hβzero j hj y (hTdis i hi j hj (Ne.symm hji) y hy)
  have hsum0 : ∀ y, (∀ i ∈ s, y ∉ T i) → ∑ j ∈ s, β j y = 0 := fun y hy =>
    Finset.sum_eq_zero fun j hj => hβzero j hj y (hy j hj)
  have hsumC : ∀ i ∈ s, ∀ y ∈ C i, pen F K 1 y + ∑ j ∈ s, β j y = c₀ := by
    intro i hi y hy
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => hβzero j hj y (fun hy' =>
      Set.disjoint_left.mp (hUdis i hi j hj (Ne.symm hji)) (hCU i hi hy) (hTU j hj hy')),
      (hCval i hi y hy).1, (hCval i hi y hy).2, add_zero]
  have hcase : ∀ y : ZMod K → Ambient n, (∑ j ∈ s, β j y = 0) ∨
      (aw < pen F K 1 y + ∑ j ∈ s, β j y ∧ pen F K 1 y + ∑ j ∈ s, β j y < bw ∧
        aw < pen F K 1 y ∧ pen F K 1 y < bw) := by
    intro y
    by_cases h : ∃ i ∈ s, y ∈ T i
    · obtain ⟨i, hi, hy⟩ := h
      right
      rw [hsumT i hi y hy]
      have h1 := hTval i hi y hy
      have h2 := abs_le.mp (hβη i hi y)
      have h3 := hη i hi
      exact ⟨by linarith only [h1.1, h2.1], by linarith only [h1.2, h2.2],
        by linarith only [h1.1, h3], by linarith only [h1.2, h3]⟩
    · left
      exact hsum0 y fun i hi hy => h ⟨i, hi, hy⟩
  -- the deformed energy has the sublevels of the penalized energy at the wide cuts
  have hsa : sub (penW F K 1) aw = sub (fun Q : Om n K => pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1) aw := by
    ext Q
    change pen F K 1 Q.1 < aw ↔ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 < aw
    rcases hcase Q.1 with h | h
    · rw [h, add_zero]
    · constructor <;> intro h' <;> linarith only [h', h.1, h.2.2.1]
  have hsb : sub (penW F K 1) bw = sub (fun Q : Om n K => pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1) bw := by
    ext Q
    change pen F K 1 Q.1 < bw ↔ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 < bw
    rcases hcase Q.1 with h | h
    · rw [h, add_zero]
    · exact ⟨fun _ => h.2.1, fun _ => h.2.2.2⟩
  -- the band of the deformed energy lies in the band of the penalized energy
  have hband : ∀ Q : Om n K, aw ≤ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 →
      pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ≤ bw → a₀ ≤ penW F K 1 Q ∧ penW F K 1 Q ≤ b₀ := by
    intro Q h1 h2
    change a₀ ≤ pen F K 1 Q.1 ∧ pen F K 1 Q.1 ≤ b₀
    rcases hcase Q.1 with h | h
    · rw [h, add_zero] at h1 h2
      exact ⟨ha₀.trans h1, h2.trans hb₀⟩
    · exact ⟨by linarith only [ha₀, h.2.2.1], by linarith only [hb₀, h.2.2.2]⟩
  have hnotC : ∀ Q : Om n K, pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ≠ c₀ → ∀ i ∈ s, Q.1 ∉ C i :=
    fun Q hQ i hi hC => hQ (hsumC i hi Q.1 hC)
  have hstrict : ∀ Q : Om n K, aw ≤ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 →
      pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ≤ bw → (∀ i ∈ s, Q.1 ∉ C i) →
      pen F K 1 ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 +
          ∑ j ∈ s, β j ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 <
        pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 := fun Q h1 h2 h3 =>
    hlt Q (hband Q h1 h2).1 (hband Q h1 h2).2 h3
  -- continuity and compact bands
  have hgc : Continuous fun Q : Om n K => pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 :=
    (penW_continuous F hn 1).add (continuous_finsetSum s fun j hj =>
      ((show Differentiable ℝ (β j) from fun y => hβd j hj y).continuous.comp
        continuous_subtype_val))
  have hKband : ∀ x y : ℝ, aw ≤ x → y ≤ bw →
      IsCompact {Q : Om n K | x ≤ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ∧
        pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ≤ y} := fun x y hx hy =>
    (band_isCompact F hn one_pos a₀ b₀).of_isClosed_subset
      ((isClosed_le continuous_const hgc).inter (isClosed_le hgc continuous_const))
      (fun Q hQ => hband Q (hx.trans hQ.1) (hQ.2.trans hy))
  -- the labels of the crossing
  have hpd : (↑s : Set ι).PairwiseDisjoint 𝒲 := fun i hi j hj hij =>
    Set.disjoint_left.mpr fun Q hQi hQj => hTdis i hi j hj hij Q.1 (h𝒲T i hi Q hQi)
      (h𝒲T j hj Q hQj)
  have hstrictF : ∀ Q : Om n K, aw ≤ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 →
      pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ≤ bw → Q ∉ ⋃ i ∈ s, 𝒲 i →
      pen F K 1 ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 +
          ∑ j ∈ s, β j ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 <
        pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 := fun Q h1 h2 hQ =>
    hstrict Q h1 h2 fun i hi hC => hQ (mem_iUnion₂.mpr ⟨i, hi, h𝒲𝒲' i hi (hC𝒲 i hi Q hC)⟩)
  obtain ⟨dF, hdF, hfam⟩ := exists_family_decomposition (descentOf hL hV0 hg hsupp hle) hgc
    (hKband aw bw le_rfl le_rfl) s h𝒲 hpd hstrictF
  -- each label is a shifted root label
  have hP2' : ∀ i ∈ s, ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d →
      (∀ k : ℕ, finrank (ZMod 2) (lensH (descentOf hL hV0 hg hsupp hle) (𝒲 i) a c t (k + b i)) =
        r i a c t k) ∧
      (∀ k : ℕ, k < b i → ∀ x : lensH (descentOf hL hV0 hg hsupp hle) (𝒲 i) a c t k, x = 0) := by
    intro i hi
    have hRo : IsOpen (⋃ j ∈ s.erase i, 𝒲 j) :=
      isOpen_biUnion fun j hj => h𝒲 j (Finset.mem_of_mem_erase hj)
    have hRd : Disjoint (𝒲 i) (⋃ j ∈ s.erase i, 𝒲 j) :=
      Set.disjoint_iUnion₂_right.mpr fun j hj => Set.disjoint_left.mpr fun Q hQi hQj =>
        hTdis i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm Q.1
          (h𝒲T i hi Q hQi) (h𝒲T j (Finset.mem_of_mem_erase hj) Q hQj)
    have hsR : ∀ Q : Om n K, aw ≤ pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 →
        pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 ≤ bw → Q ∉ 𝒲' i ∪ ⋃ j ∈ s.erase i, 𝒲 j →
        pen F K 1 ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 +
            ∑ j ∈ s, β j ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 <
          pen F K 1 Q.1 + ∑ j ∈ s, β j Q.1 := by
      intro Q h1 h2 hQ
      refine hstrict Q h1 h2 fun j hj hC => hQ ?_
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hC𝒲 j hj Q hC)
      · exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩,
          h𝒲𝒲' j hj (hC𝒲 j hj Q hC)⟩)
    exact hP2 i hi hL hV0 hg hsupp hle (hVT i hi)
      (fun y hy => by rw [hsumT i hi y hy])
      hac₀ hc₀b hgc (hKband aw bw le_rfl le_rfl) hRo hRd hsR
  choose! dd hdd hP using hP2'
  -- a common width
  set Dset : Finset ℝ := insert 1 (s.image dd) with hDset
  have hDne : Dset.Nonempty := Finset.insert_nonempty _ _
  have hd₁ : 0 < Dset.min' hDne := (Finset.lt_min'_iff Dset hDne).mpr fun x hx => by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact one_pos
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hdd i hi
  have hd₁i : ∀ i ∈ s, Dset.min' hDne ≤ dd i := fun i hi =>
    Finset.min'_le Dset _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem dd hi))
  refine ⟨min (dF / 2) (min (c₀ - aw) (min (bw - c₀) (Dset.min' hDne))),
    lt_min (half_pos hdF) (lt_min (by linarith only [hac₀]) (lt_min (by linarith only [hc₀b]) hd₁)),
    fun a c t ht ha hc hca q hfin => ?_⟩
  have hca1 : c - a < dF / 2 := lt_of_lt_of_le hca (min_le_left _ _)
  have hca2 : c - a < c₀ - aw := lt_of_lt_of_le hca ((min_le_right _ _).trans (min_le_left _ _))
  have hca3 : c - a < bw - c₀ :=
    lt_of_lt_of_le hca ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hca4 : c - a < Dset.min' hDne :=
    lt_of_lt_of_le hca ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have haw : aw < a := by linarith only [hca2, hc]
  have hcbw : c < bw := by linarith only [hca3, ha]
  have hac : a ≤ c := by linarith only [ha, hc]
  -- moving the cuts
  have hmove := cross_move (descentOf hL hV0 hg hsupp hle) hgc haw.le hac hcbw.le
    (hKband aw a le_rfl (hac.trans hcbw.le)) (hKband c bw (haw.le.trans hac) le_rfl)
    (fun Q h1 h2 => hstrict Q h1 (h2.trans (hac.trans hcbw.le))
      (hnotC Q (fun h => by linarith only [h, h2, ha])))
    (fun Q h1 h2 => hstrict Q (haw.le.trans (hac.trans h1)) h2
      (hnotC Q (fun h => by linarith only [h, h1, hc])))
    hsa hsb habw q
  -- the crossing at the tight cuts is the sum of its labels
  have ha'a : max aw (c - dF / 2) < a := max_lt haw (by linarith only [hca1])
  have hca' : c - max aw (c - dF / 2) < dF := by
    have := le_max_right aw (c - dF / 2)
    linarith only [this, hdF]
  obtain ⟨-, hsum, hlab⟩ := hfam (max aw (c - dF / 2)) a c t hac (le_max_left _ _) ha'a hcbw.le
    hca' ht q
  rw [hmove.2, (hsum (hlab (hmove.1.mp hfin))).2]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨h1, h2⟩ := hP i hi a c t ht ha hc (lt_of_lt_of_le hca4 (hd₁i i hi))
  exact finrank_shift (fun k => lensH (descentOf hL hV0 hg hsupp hle) (𝒲 i) a c t k) h1 h2 q

end

end Finsler.LevelCrossing
