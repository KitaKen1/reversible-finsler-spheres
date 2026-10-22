module

public import Finsler.Topology.LensParts
public import Finsler.Topology.LensTrap

/-! Lens pairs of finitely many pairwise disjoint open sets. For a function with a descent, cuts
a, b and a time T, the lens pair of the union of finitely many pairwise disjoint open sets has no
cohomology in a degree in which the lens pairs of the sets have none; if the cohomologies of the
lens pairs of the sets are finite dimensional, so is that of the union, and its dimension is the
sum of their dimensions; conversely the lens pair of each set has finite dimensional cohomology
if the union has. If every point below b which is not taken below a' in time T lies in the union,
the same holds for the cohomology of the sublevel of b relative to the sublevel of a: a crossing
is the sum of its labels. On a compact band this applies to every descent whose time-one map
decreases the function strictly outside the union, for all sufficiently tight cuts. -/

@[expose] public section

namespace Finsler.LensFamily

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation Finsler.LensParts Finsler.LensTrap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) {a b T : ℝ}

/-- The cohomology of the lens pair of a set. -/
abbrev lensH (𝒲 : Set W) (a b T : ℝ) (n : ℕ) :=
  H (triv (pairOf (partY_sub_partU g D 𝒲 a b T))) n

theorem sub_mono (g : W → ℝ) {a b : ℝ} (hab : a ≤ b) : sub g a ⊆ sub g b :=
  fun _ hw => lt_of_lt_of_le hw hab

/-- The cohomology of the sublevel of b relative to the sublevel of a. -/
abbrev crossH (g : W → ℝ) {a b : ℝ} (hab : a ≤ b) (n : ℕ) :=
  H (triv (pairOf (sub_mono g hab))) n

variable {ι : Type*} (𝒲 : ι → Set W)

/-- A set of a pairwise disjoint family is disjoint from the union of the others. -/
theorem disjoint_biUnion [DecidableEq ι] {s : Finset ι} {j : ι} (hj : j ∉ s)
    (hdis : ((insert j s : Finset ι) : Set ι).PairwiseDisjoint 𝒲) :
    Disjoint (𝒲 j) (⋃ i ∈ s, 𝒲 i) := by
  rw [Set.disjoint_iUnion₂_right]
  intro i hi
  exact hdis (Finset.mem_coe.mpr (Finset.mem_insert_self j s))
    (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) (fun h => hj (h ▸ hi))

/-- The lens pair of a finite union of pairwise disjoint open sets has no cohomology in a degree
in which the lens pairs of the sets have none. -/
theorem family_eq_zero (s : Finset ι) (n : ℕ) :
    ∀ 𝒰 : Set W, 𝒰 = ⋃ i ∈ s, 𝒲 i → (∀ i ∈ s, IsOpen (𝒲 i)) →
      (s : Set ι).PairwiseDisjoint 𝒲 →
      (∀ i ∈ s, ∀ x : H (triv (pairOf (partY_sub_partU g D (𝒲 i) a b T))) n, x = 0) →
      ∀ x : H (triv (pairOf (partY_sub_partU g D 𝒰 a b T))) n, x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro 𝒰 h𝒰 _ _ _ x
    have h : 𝒰 = ∅ := h𝒰.trans (by simp)
    subst h
    exact empty_eq_zero D n x
  | insert j s hj ih =>
    intro 𝒰 h𝒰 hopen hdis hz x
    have h : 𝒰 = 𝒲 j ∪ ⋃ i ∈ s, 𝒲 i := h𝒰.trans (Finset.set_biUnion_insert j s 𝒲)
    subst h
    exact union_eq_zero D (hopen j (Finset.mem_insert_self j s))
      (isOpen_biUnion fun i hi => hopen i (Finset.mem_insert_of_mem hi))
      (disjoint_biUnion 𝒲 hj hdis) n (hz j (Finset.mem_insert_self j s))
      (ih _ rfl (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
        (hdis.subset (Finset.coe_subset.mpr (Finset.subset_insert j s)))
        (fun i hi => hz i (Finset.mem_insert_of_mem hi))) x

/-- The cohomology of the lens pair of a finite union of pairwise disjoint open sets is finite
dimensional if the cohomologies of the lens pairs of the sets are, and its dimension is the sum
of their dimensions. -/
theorem family_finrank (s : Finset ι) (n : ℕ) :
    ∀ 𝒰 : Set W, 𝒰 = ⋃ i ∈ s, 𝒲 i → (∀ i ∈ s, IsOpen (𝒲 i)) →
      (s : Set ι).PairwiseDisjoint 𝒲 →
      (∀ i ∈ s, Module.Finite (ZMod 2)
        (H (triv (pairOf (partY_sub_partU g D (𝒲 i) a b T))) n)) →
      Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D 𝒰 a b T))) n) ∧
        Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU g D 𝒰 a b T))) n) =
          ∑ i ∈ s, Module.finrank (ZMod 2)
            (H (triv (pairOf (partY_sub_partU g D (𝒲 i) a b T))) n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro 𝒰 h𝒰 _ _ _
    have h : 𝒰 = ∅ := h𝒰.trans (by simp)
    subst h
    have : Subsingleton (H (triv (pairOf (partY_sub_partU g D (∅ : Set W) a b T))) n) :=
      ⟨fun x y => (empty_eq_zero D n x).trans (empty_eq_zero D n y).symm⟩
    exact ⟨inferInstance, by rw [Finset.sum_empty]; exact Module.finrank_zero_of_subsingleton⟩
  | insert j s hj ih =>
    intro 𝒰 h𝒰 hopen hdis hfin
    have h : 𝒰 = 𝒲 j ∪ ⋃ i ∈ s, 𝒲 i := h𝒰.trans (Finset.set_biUnion_insert j s 𝒲)
    subst h
    obtain ⟨hF, hr⟩ := ih _ rfl (fun i hi => hopen i (Finset.mem_insert_of_mem hi))
      (hdis.subset (Finset.coe_subset.mpr (Finset.subset_insert j s)))
      (fun i hi => hfin i (Finset.mem_insert_of_mem hi))
    have := hfin j (Finset.mem_insert_self j s)
    have := hF
    let e := unionEquiv D (a := a) (b := b) (T := T) (hopen j (Finset.mem_insert_self j s))
      (isOpen_biUnion fun i hi => hopen i (Finset.mem_insert_of_mem hi))
      (disjoint_biUnion 𝒲 hj hdis) n
    refine ⟨Module.Finite.equiv e.symm, ?_⟩
    rw [e.finrank_eq, Module.finrank_prod, hr, Finset.sum_insert hj]

/-- The lens pair of one of two disjoint open sets has finite dimensional cohomology if the
lens pair of the union has. -/
theorem finite_left {𝒲₁ 𝒲₂ : Set W} (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂)
    (n : ℕ)
    (hfin : Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D (𝒲₁ ∪ 𝒲₂) a b T))) n)) :
    Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n) := by
  let e := unionEquiv D (a := a) (b := b) (T := T) h₁ h₂ hdis n
  have := hfin
  have : Module.Finite (ZMod 2)
      (H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n ×
        H (triv (pairOf (partY_sub_partU g D 𝒲₂ a b T))) n) := Module.Finite.equiv e
  exact Module.Finite.of_surjective
    (LinearMap.fst (ZMod 2) (H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n)
      (H (triv (pairOf (partY_sub_partU g D 𝒲₂ a b T))) n)) LinearMap.fst_surjective

/-- Each set of a finite pairwise disjoint family of open sets has a lens pair with finite
dimensional cohomology if the lens pair of the union has. -/
theorem family_finite (s : Finset ι) (n : ℕ) (hopen : ∀ i ∈ s, IsOpen (𝒲 i))
    (hdis : (s : Set ι).PairwiseDisjoint 𝒲)
    (hfin : Module.Finite (ZMod 2)
      (H (triv (pairOf (partY_sub_partU g D (⋃ i ∈ s, 𝒲 i) a b T))) n))
    {j : ι} (hj : j ∈ s) :
    Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D (𝒲 j) a b T))) n) := by
  classical
  have hs : insert j (s.erase j) = s := Finset.insert_erase hj
  have hU : (⋃ i ∈ s, 𝒲 i) = 𝒲 j ∪ ⋃ i ∈ s.erase j, 𝒲 i := by
    rw [← Finset.set_biUnion_insert j (s.erase j) 𝒲, hs]
  have hd : Disjoint (𝒲 j) (⋃ i ∈ s.erase j, 𝒲 i) :=
    disjoint_biUnion 𝒲 (Finset.notMem_erase j s) (by rw [hs]; exact hdis)
  have hopen' : IsOpen (⋃ i ∈ s.erase j, 𝒲 i) :=
    isOpen_biUnion fun i hi => hopen i (Finset.mem_of_mem_erase hi)
  have key : ∀ 𝒰 : Set W, 𝒰 = 𝒲 j ∪ ⋃ i ∈ s.erase j, 𝒲 i →
      Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D 𝒰 a b T))) n) →
      Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D (𝒲 j) a b T))) n) := by
    intro 𝒰 h𝒰 hF
    subst h𝒰
    exact finite_left D (hopen j hj) hopen' hd n hF
  exact key _ hU hfin

variable {𝒲}

/-- A crossing has no cohomology in a degree in which its labels have none. -/
theorem crossing_eq_zero {a' : ℝ} (s : Finset ι) (hg : Continuous g) (hab : a ≤ b) (ha : a' < a)
    (hT : 0 ≤ T) (hopen : ∀ i ∈ s, IsOpen (𝒲 i)) (hdis : (s : Set ι).PairwiseDisjoint 𝒲)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ ⋃ i ∈ s, 𝒲 i) (n : ℕ)
    (hz : ∀ i ∈ s, ∀ x : H (triv (pairOf (partY_sub_partU g D (𝒲 i) a b T))) n, x = 0)
    (x : H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n) :
    x = 0 := by
  let e := crossingEquiv D hg hab ha hT htrap n
  have h0 : e x = 0 := family_eq_zero D 𝒲 s n _ rfl hopen hdis hz _
  calc x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm 0 := by rw [h0]
    _ = 0 := e.symm.map_zero

/-- The dimension of the cohomology of a crossing is the sum of the dimensions of its labels. -/
theorem crossing_finrank {a' : ℝ} (s : Finset ι) (hg : Continuous g) (hab : a ≤ b) (ha : a' < a)
    (hT : 0 ≤ T) (hopen : ∀ i ∈ s, IsOpen (𝒲 i)) (hdis : (s : Set ι).PairwiseDisjoint 𝒲)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ ⋃ i ∈ s, 𝒲 i) (n : ℕ)
    (hfin : ∀ i ∈ s, Module.Finite (ZMod 2)
      (H (triv (pairOf (partY_sub_partU g D (𝒲 i) a b T))) n)) :
    Module.Finite (ZMod 2)
        (H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n) ∧
      Module.finrank (ZMod 2)
          (H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n) =
        ∑ i ∈ s, Module.finrank (ZMod 2)
          (H (triv (pairOf (partY_sub_partU g D (𝒲 i) a b T))) n) := by
  let e := crossingEquiv D hg hab ha hT htrap n
  obtain ⟨hF, hr⟩ := family_finrank D 𝒲 s n _ rfl hopen hdis hfin
  have := hF
  exact ⟨Module.Finite.equiv e.symm, by rw [e.finrank_eq, hr]⟩

/-- The labels of a crossing with finite dimensional cohomology have finite dimensional
cohomology. -/
theorem label_finite {a' : ℝ} (s : Finset ι) (hg : Continuous g) (hab : a ≤ b) (ha : a' < a)
    (hT : 0 ≤ T) (hopen : ∀ i ∈ s, IsOpen (𝒲 i)) (hdis : (s : Set ι).PairwiseDisjoint 𝒲)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ ⋃ i ∈ s, 𝒲 i) (n : ℕ)
    (hfin : Module.Finite (ZMod 2)
      (H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n))
    {j : ι} (hj : j ∈ s) :
    Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU g D (𝒲 j) a b T))) n) := by
  let e := crossingEquiv D hg hab ha hT htrap n
  have := hfin
  exact family_finite D 𝒲 s n hopen hdis (Module.Finite.equiv e) hj

/-- On a compact band, a descent whose time-one map decreases the function strictly outside the
union of finitely many pairwise disjoint open sets splits every sufficiently tight crossing into
the lens pairs of these sets: vanishing, finiteness and dimensions. -/
theorem exists_family_decomposition (hg : Continuous g) {a₀ b₀ : ℝ}
    (hK : IsCompact {w : W | a₀ ≤ g w ∧ g w ≤ b₀}) (s : Finset ι)
    (hopen : ∀ i ∈ s, IsOpen (𝒲 i)) (hdis : (s : Set ι).PairwiseDisjoint 𝒲)
    (hstrict : ∀ w, a₀ ≤ g w → g w ≤ b₀ → w ∉ ⋃ i ∈ s, 𝒲 i → g (D.flow 1 w) < g w) :
    ∃ d : ℝ, 0 < d ∧ ∀ (a' a b T : ℝ) (hab : a ≤ b), a₀ ≤ a' → a' < a → b ≤ b₀ →
      b - a' < d → 1 ≤ T → ∀ n : ℕ,
        ((∀ i ∈ s, ∀ x : lensH D (𝒲 i) a b T n, x = 0) → ∀ x : crossH g hab n, x = 0) ∧
        ((∀ i ∈ s, Module.Finite (ZMod 2) (lensH D (𝒲 i) a b T n)) →
          Module.Finite (ZMod 2) (crossH g hab n) ∧
            Module.finrank (ZMod 2) (crossH g hab n) =
              ∑ i ∈ s, Module.finrank (ZMod 2) (lensH D (𝒲 i) a b T n)) ∧
        (Module.Finite (ZMod 2) (crossH g hab n) →
          ∀ i ∈ s, Module.Finite (ZMod 2) (lensH D (𝒲 i) a b T n)) := by
  obtain ⟨d, hd, htr⟩ := exists_trap D hg (isOpen_biUnion hopen) hK hstrict
  refine ⟨d, hd, ?_⟩
  intro a' a b T hab ha0 ha hb0 hwidth hT1 n
  have hT : 0 ≤ T := zero_le_one.trans hT1
  have htrap := htr a' b T ha0 hb0 hwidth hT1
  exact ⟨fun hz => crossing_eq_zero D s hg hab ha hT hopen hdis htrap n hz,
    fun hf => crossing_finrank D s hg hab ha hT hopen hdis htrap n hf,
    fun hf i hi => label_finite D s hg hab ha hT hopen hdis htrap n hf hi⟩

end

end Finsler.LensFamily
