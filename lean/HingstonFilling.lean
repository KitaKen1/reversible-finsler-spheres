import HingstonPause

/-!
# Sliding the doubled base interval to its boundary

The enlarged Hingston family has two independent base intervals. Sliding the
second coordinate to its right endpoint moves the diagonal family into the
lower energy sublevel and preserves the parameter boundary throughout.
The construction uses actual H¹ loops and relative singular homology.
The local family and its energy bounds remain explicit hypotheses.
-/

namespace Finsler.HingstonFilling

open CategoryTheory CategoryTheory.Limits
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.SobolevEnergy
open Finsler.SobolevSpherePath
open HingstonBlocks HingstonConnectors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

/-- A pair map whose entire ambient image is in the target subspace induces
the zero map on relative singular homology. -/
theorem homologyMap_eq_zero_of_factor {P Q : TopPair} (f : P ⟶ Q)
    (g : P.fst ⟶ Q.snd) (hf : TopPair.Hom.fst f = g ≫ Q.map)
    (K : Type) [Field K] (q : ℕ) :
    TopPair.singularHomologyMap f (ModuleCat.of K K) q = 0 := by
  have h : TopPair.singularChainComplexMap f (ModuleCat.of K K) = 0 := by
    apply (cancel_epi (P.singularChainComplexπ (ModuleCat.of K K))).mp
    have hf' : SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) (ModuleCat.of K K) =
        SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K) ≫
          SSet.chainComplexMap (TopCat.toSSet.map Q.map) (ModuleCat.of K K) := by
      rw [hf, Functor.map_comp]
      exact Functor.map_comp _ _ _
    rw [← TopPair.singularChainComplexπ_pair_naturality, hf', Category.assoc,
      Q.chainComplexMap_comp_singularChainComplexπ, comp_zero, comp_zero]
  change HomologicalComplex.homologyMap
    (TopPair.singularChainComplexMap f (ModuleCat.of K K)) q = 0
  rw [h, HomologicalComplex.homologyMap_zero]

abbrev I := ↥(_root_.unitInterval)

/-- The second interval coordinate moves linearly to its right endpoint. -/
def slide : C(I × I, I) := by
  refine ⟨fun z => ⟨(1 - (z.1 : ℝ)) * (z.2 : ℝ) + z.1,
    by constructor <;> nlinarith [z.1.property.1, z.1.property.2,
      z.2.property.1, z.2.property.2]⟩, ?_⟩
  exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).add
        (continuous_subtype_val.comp continuous_fst)).subtype_mk _

@[simp] theorem slide_zero (x : I) : slide (0, x) = x := by
  apply Subtype.ext
  simp [slide]

@[simp] theorem slide_one (x : I) : slide (1, x) = 1 := by
  apply Subtype.ext
  simp [slide]

section Slide
variable {Z : Type} [TopologicalSpace Z] (BZ : Set Z)

/-- The diagonal parameter boundary: an interval endpoint or a transverse face. -/
def boundary : Set (I × Z) := {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ BZ}

/-- The boundary of the enlarged parameter domain has both interval faces. -/
def enlargedBoundary : Set (I × I × Z) :=
  {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 1 ∨ z.2.2 ∈ BZ}

variable {n : ℕ} (F : ReversibleMetric n)
  (ψ : C(I × I × Z, SphereLoop n)) {l L : ℝ}
  (hlL : l ≤ L)
  (hψ : ∀ z, ψ z ∈ BorelLoop.lev F L)
  (hB : ∀ z ∈ enlargedBoundary BZ, ψ z ∈ BorelLoop.lev F l)

private def slideInput : C(I × (I × Z), I × I × Z) :=
  ⟨fun z => (z.2.1, slide (z.1, z.2.1), z.2.2),
    (continuous_fst.comp continuous_snd).prodMk
      ((slide.continuous.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
          (continuous_snd.comp continuous_snd))⟩

private theorem slideInput_boundary (t : I) (x : I × Z) (hx : x ∈ boundary BZ) :
    slideInput (t, x) ∈ enlargedBoundary BZ := by
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Each time of the explicit slide gives a map into the actual energy pair. -/
def slidePairMap (t : I) :
    TopPair.ofSubset (X := TopCat.of (I × Z)) (boundary BZ) ⟶
      BorelLoop.pairOf (BorelLoop.lev_mono F hlL) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x => ⟨ψ (slideInput (t, x)), hψ _⟩,
      (((ψ.comp slideInput).continuous).comp
        (continuous_const.prodMk continuous_id)).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun x : boundary BZ =>
      ⟨ψ (slideInput (t, x.val)), hB _ (slideInput_boundary BZ t x.val x.property)⟩,
      (((ψ.comp slideInput).continuous).comp
        (continuous_const.prodMk continuous_subtype_val)).subtype_mk _⟩)
    (by ext x; rfl)

/-- Homotopy of pairs from the diagonal family to the right base face. -/
def slidePairHomotopy :
    TopPair.Homotopy (slidePairMap BZ F ψ hlL hψ hB 0)
      (slidePairMap BZ F ψ hlL hψ hB 1) where
  fst := {
    toFun z := ⟨ψ (slideInput z), hψ _⟩
    continuous_toFun := (ψ.comp slideInput).continuous.subtype_mk _
    map_zero_left _ := rfl
    map_one_left _ := rfl }
  snd := {
    toFun z := ⟨ψ (slideInput (z.1, z.2.val)),
      hB _ (slideInput_boundary BZ z.1 z.2.val z.2.property)⟩
    continuous_toFun := ((ψ.comp slideInput).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left _ := rfl
    map_one_left _ := rfl }

theorem slidePairMap_zero (x : I × Z) :
    (TopPair.Hom.fst (slidePairMap BZ F ψ hlL hψ hB 0) x).val = ψ (x.1, x.1, x.2) := by
  change ψ (x.1, slide (0, x.1), x.2) = _
  rw [slide_zero]

theorem slidePairMap_one (x : I × Z) :
    (TopPair.Hom.fst (slidePairMap BZ F ψ hlL hψ hB 1) x).val = ψ (x.1, 1, x.2) := by
  change ψ (x.1, slide (1, x.1), x.2) = _
  rw [slide_one]

/-- The diagonal family dies in relative homology in every degree: the
explicit homotopy moves its whole image into the lower energy sublevel. -/
theorem slide_homology_eq_zero (K : Type) [Field K] (q : ℕ) :
    TopPair.singularHomologyMap (slidePairMap BZ F ψ hlL hψ hB 0)
      (ModuleCat.of K K) q = 0 := by
  rw [(slidePairHomotopy BZ F ψ hlL hψ hB).congr_singularHomologyMap (ModuleCat.of K K) q]
  let g : TopCat.of (I × Z) ⟶ TopCat.of (BorelLoop.lev F l) :=
    TopCat.ofHom ⟨fun x => ⟨ψ (x.1, 1, x.2),
      hB _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩,
      (ψ.continuous.comp (continuous_fst.prodMk
        (continuous_const.prodMk continuous_snd))).subtype_mk _⟩
  apply homologyMap_eq_zero_of_factor _ g _ K q
  ext x
  apply Subtype.ext
  exact slidePairMap_one BZ F ψ hlL hψ hB x

end Slide

section PauseSlide
variable {n : ℕ} {Z : Type} [TopologicalSpace Z]
  (BZ : Set Z) (F : ReversibleMetric n)
  {a b c l L : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
  (hl : 0 < l) (hL : 0 < L) (hlL : l ≤ L)
  (ψ : C(I × I × Z, SphereLoop n))
  (g : C(I × Z, H1JoinContinuity.composable n))
  (hmatch : ∀ x : I × Z, ψ (x.1, x.1, x.2) = HingstonPause.value ha hb ⟨c, hc⟩ (g x))
  (hψ : ∀ z, ψ z ∈ BorelLoop.lev F L)
  (hB : ∀ z ∈ enlargedBoundary BZ, ψ z ∈ BorelLoop.lev F l)

include hmatch hψ in
private theorem diagonal_mem (x : I × Z) :
    HingstonPause.value ha hb ⟨c, hc⟩ (g x) ∈ BorelLoop.lev F L := by
  rw [← hmatch]
  exact hψ _

include hmatch hB in
private theorem diagonal_boundary_mem (x : I × Z) (hx : x ∈ boundary BZ) :
    HingstonPause.value ha hb ⟨c, hc⟩ (g x) ∈ BorelLoop.lev F l := by
  rw [← hmatch]
  apply hB
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The ordinary weighted join as a map of the parameter/boundary pair into
the two actual energy cuts. Its bounds follow by removing diagonal pauses. -/
def ordinaryPairMap :
    TopPair.ofSubset (X := TopCat.of (I × Z)) (boundary BZ) ⟶
      BorelLoop.pairOf (BorelLoop.lev_mono F hlL) :=
  HingstonPause.familyPairMap ha hb hc F g hl hL hlL
    (diagonal_mem F ha hb hc ψ g hmatch hψ)
    (diagonal_boundary_mem BZ F ha hb hc ψ g hmatch hB) 1

theorem ordinaryPairMap_apply (x : I × Z) :
    (TopPair.Hom.fst (ordinaryPairMap BZ F ha hb hc hl hL hlL ψ g hmatch hψ hB) x).val =
      H1LoopJoin.join (a / (a + b)) (div_pos ha (add_pos ha hb))
        ((div_lt_one (add_pos ha hb)).mpr (by linarith))
        (g x).val.1 (g x).val.2 (g x).property :=
  HingstonPause.familyPairMap_one ha hb hc F g hl hL hlL
    (diagonal_mem F ha hb hc ψ g hmatch hψ)
    (diagonal_boundary_mem BZ F ha hb hc ψ g hmatch hB) x

/-- Pause removal and the explicit base slide together kill the ordinary
repeated family in relative homology, in every degree. -/
theorem ordinary_homology_eq_zero (K : Type) [Field K] (q : ℕ) :
    TopPair.singularHomologyMap
      (ordinaryPairMap BZ F ha hb hc hl hL hlL ψ g hmatch hψ hB)
      (ModuleCat.of K K) q = 0 := by
  unfold ordinaryPairMap
  rw [← HingstonPause.family_homology_eq]
  have heq : HingstonPause.familyPairMap ha hb hc F g hl hL hlL
      (diagonal_mem F ha hb hc ψ g hmatch hψ)
      (diagonal_boundary_mem BZ F ha hb hc ψ g hmatch hB) 0 =
        slidePairMap BZ F ψ hlL hψ hB 0 := by
    ext : 1
    · ext x
      apply Subtype.ext
      change HingstonPause.homotopy ha hb hc (0, g x.val) =
        ψ (x.val.1, slide (0, x.val.1), x.val.2)
      rw [(HingstonPause.homotopy ha hb hc).apply_zero, slide_zero, hmatch]
      rfl
    · ext x
      apply Subtype.ext
      change HingstonPause.homotopy ha hb hc (0, g x) =
        ψ (x.1, slide (0, x.1), x.2)
      rw [(HingstonPause.homotopy ha hb hc).apply_zero, slide_zero, hmatch]
      rfl
  rw [heq]
  exact slide_homology_eq_zero BZ F ψ hlL hψ hB K q

end PauseSlide

section Blocks
variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
  (F : ReversibleMetric n) (φ : C(I × Y, SphereLoop n))
  (hbase : ∀ x y z, basepoint (φ (x, y)) = basepoint (φ (x, z)))
  {ρ : ℝ} (hρ : ρ ≤ shortRadius F)
  (hnear : ∀ x x' y y', ‖basepoint (φ (x', y')) - basepoint (φ (x, y))‖ < ρ)
  (r s : ℕ)

abbrev Transverse (Y : Type) (r s : ℕ) := (Fin (r + 1) → Y) × (Fin (s + 1) → Y)

/-- Quantitative conditions on the original local family. These are genuine
energy inequalities, not assumptions about the desired homology map. -/
structure EnergyBounds (F : ReversibleMetric n) (φ : C(I × Y, SphereLoop n))
    (BY : Set Y) (l ε c : ℝ) (r s : ℕ) where
  transverseDeficit : ℝ
  baseDeficit : ℝ
  transverse_pos : 0 < transverseDeficit
  base_pos : 0 < baseDeficit
  energy_le : ∀ x y, energy F (φ (x, y)) ≤ l ^ 2
  transverse_le : ∀ x y, y ∈ BY → energy F (φ (x, y)) ≤ l ^ 2 - transverseDeficit
  endpoint_le : ∀ x, x = 0 ∨ x = 1 → ∀ y,
    energy F (φ (x, y)) ≤ l ^ 2 - baseDeficit
  transverse_gap : overhead (l ^ 2) c < transverseDeficit
  left_gap : overhead (l ^ 2) c < ((r : ℝ) + 1) * baseDeficit
  right_gap : overhead (l ^ 2) c < ((s : ℝ) + 1) * baseDeficit
  upper_gap : overhead (l ^ 2) c < 2 * l * ε

/-- A transverse face is a boundary coordinate in either group. -/
def transverseBoundary (BY : Set Y) : Set (Transverse Y r s) :=
  {z | (∃ i, z.1 i ∈ BY) ∨ ∃ j, z.2 j ∈ BY}

/-- Assemble two independently based groups from the original local family. -/
def enlargedBlocks : C(I × I × Transverse Y r s, NearBlocks F r s) := by
  let left : C(I × I × Transverse Y r s, Blocks n r) :=
    (familyBlocks φ hbase r).comp ⟨fun z => (z.1, z.2.2.1),
      continuous_fst.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd))⟩
  let right : C(I × I × Transverse Y r s, Blocks n s) :=
    (familyBlocks φ hbase s).comp ⟨fun z => (z.2.1, z.2.2.2),
      (continuous_fst.comp continuous_snd).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_snd))⟩
  refine ⟨fun z => ⟨(left z, right z),
    (hnear z.1 z.2.1 (z.2.2.1 0) (z.2.2.2 0)).trans_le hρ⟩, ?_⟩
  exact (left.continuous.prodMk right.continuous).subtype_mk _

variable {c : ℝ} (hc : 0 < c)

/-- The actual enlarged loop family, with two shortest connecting paths. -/
def enlargedFamily : C(I × I × Transverse Y r s, SphereLoop n) :=
  (blockLoop hc F r s).comp (enlargedBlocks F φ hbase hρ hnear r s)

omit hρ hnear hc in
/-- On the diagonal the two repeated groups share a basepoint. -/
def diagonalPair : C(I × Transverse Y r s, H1JoinContinuity.composable n) := by
  let left : C(I × Transverse Y r s, SphereLoop n) :=
    (family φ hbase r).comp ⟨fun z => (z.1, z.2.1),
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)⟩
  let right : C(I × Transverse Y r s, SphereLoop n) :=
    (family φ hbase s).comp ⟨fun z => (z.1, z.2.2),
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)⟩
  have hsame (z : I × Transverse Y r s) : basepoint (left z) = basepoint (right z) := by
    change basepoint (HingstonBlocks.concat _) = basepoint (HingstonBlocks.concat _)
    rw [basepoint_concat, basepoint_concat]
    exact hbase z.1 (z.2.1 0) (z.2.2 0)
  exact ⟨fun z => ⟨(left z, right z), hsame z⟩,
    (left.continuous.prodMk right.continuous).subtype_mk _⟩

/-- The diagonal of the actual connector construction is exactly the start
of the energy-decreasing pause homotopy. -/
theorem enlargedFamily_diagonal (x : I × Transverse Y r s) :
    enlargedFamily F φ hbase hρ hnear r s hc (x.1, x.1, x.2) =
      HingstonPause.value (by positivity : 0 < (r : ℝ) + 1)
        (by positivity : 0 < (s : ℝ) + 1) ⟨c, hc.le⟩ (diagonalPair φ hbase r s x) := by
  have heq : blockPair F r s (enlargedBlocks F φ hbase hρ hnear r s (x.1, x.1, x.2)) =
      diagonalPairs F (diagonalPair φ hbase r s x) := Subtype.ext rfl
  change shortLoop _ _ hc F _ = _
  rw [heq, HingstonPause.shortLoop_diagonal_eq]

variable
  (hpath : ∀ p : NearPairs F, ‖basepoint p.val.2 - basepoint p.val.1‖ < ρ →
    pathEnergy F (shortData F p).val.2.2 ≤ c ^ 2)

include hpath in
private theorem enlarged_path_bound (z : I × I × Transverse Y r s) :
    pathEnergy F (shortData F (blockPair F r s
      (enlargedBlocks F φ hbase hρ hnear r s z))).val.2.2 ≤ c ^ 2 := by
  apply hpath
  change ‖basepoint (HingstonBlocks.concat _) - basepoint (HingstonBlocks.concat _)‖ < ρ
  rw [basepoint_concat, basepoint_concat]
  exact hnear z.1 z.2.1 (z.2.2.1 0) (z.2.2.2 0)

variable {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε)
  (henergy : ∀ x y, energy F (φ (x, y)) ≤ l ^ 2)

include hl hε henergy hpath in
/-- The enlarged family's entire image lies below the upper length cut. -/
theorem enlargedFamily_mem_lev (hgap : overhead (l ^ 2) c < 2 * l * ε)
    (z : I × I × Transverse Y r s) :
    enlargedFamily F φ hbase hρ hnear r s hc z ∈
      BorelLoop.lev F (((r : ℝ) + 1 + ((s : ℝ) + 1)) * l + ε) := by
  apply blockLoop_mem_lev hc F _ hl hε hgap
  · intro i; exact henergy z.1 (z.2.2.1 i)
  · intro i; exact henergy z.2.1 (z.2.2.2 i)
  · exact enlarged_path_bound F φ hbase hρ hnear r s hpath z

include hl henergy hpath in
/-- Every base face and transverse face is below the repeated critical cut.
This checks all five boundary alternatives on actual connected loops. -/
theorem enlargedFamily_boundary_mem (BY : Set Y) {δT δB : ℝ}
    (hδT : 0 ≤ δT) (hδB : 0 ≤ δB)
    (htrans : ∀ x y, y ∈ BY → energy F (φ (x, y)) ≤ l ^ 2 - δT)
    (hends : ∀ x, x = 0 ∨ x = 1 → ∀ y, energy F (φ (x, y)) ≤ l ^ 2 - δB)
    (hgapT : overhead (l ^ 2) c < δT)
    (hgapR : overhead (l ^ 2) c < ((r : ℝ) + 1) * δB)
    (hgapS : overhead (l ^ 2) c < ((s : ℝ) + 1) * δB)
    (z : I × I × Transverse Y r s)
    (hz : z ∈ enlargedBoundary (transverseBoundary r s BY)) :
    enlargedFamily F φ hbase hρ hnear r s hc z ∈
      BorelLoop.lev F (((r : ℝ) + 1 + ((s : ℝ) + 1)) * l) := by
  let p := enlargedBlocks F φ hbase hρ hnear r s z
  have hu : ∀ i, energy F (p.val.1.val i) ≤ l ^ 2 := fun i => henergy z.1 (z.2.2.1 i)
  have hv : ∀ i, energy F (p.val.2.val i) ≤ l ^ 2 := fun i => henergy z.2.1 (z.2.2.2 i)
  have hp := enlarged_path_bound F φ hbase hρ hnear r s hpath z
  apply (Birkhoff.mem_lev_iff (by positivity) _).mpr
  rw [mul_pow]
  change energy F (blockLoop hc F r s p) < _
  have hbaseFace (h : (z.1 = 0 ∨ z.1 = 1) ∨ (z.2.1 = 0 ∨ z.2.1 = 1)) := by
    apply blockLoop_base_boundary_lt hc F p hδB hgapR hgapS hu hv _ hp
    rcases h with h | h
    · exact Or.inl (fun i => hends z.1 h (z.2.2.1 i))
    · exact Or.inr (fun i => hends z.2.1 h (z.2.2.2 i))
  rcases hz with h | h | h | h | h
  · exact hbaseFace (Or.inl (Or.inl h))
  · exact hbaseFace (Or.inl (Or.inr h))
  · exact hbaseFace (Or.inr (Or.inl h))
  · exact hbaseFace (Or.inr (Or.inr h))
  · apply blockLoop_boundary_lt hc F p hδT hgapT hu hv _ hp
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i, htrans z.1 (z.2.2.1 i) hi⟩
    · exact Or.inr ⟨i, htrans z.2.1 (z.2.2.2 i) hi⟩

variable (BY : Set Y) (bounds : EnergyBounds F φ BY l ε c r s)

/-- The ordinary repeated family after pause removal, now with all upper
and lower cut bounds discharged by the connector estimates. -/
def blockPairMap :
    TopPair.ofSubset (X := TopCat.of (I × Transverse Y r s))
      (boundary (transverseBoundary r s BY)) ⟶
    BorelLoop.pairOf (BorelLoop.lev_mono F
      (show ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l ≤
        ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l + ε from le_add_of_nonneg_right hε.le)) :=
  ordinaryPairMap (transverseBoundary r s BY) F (by positivity) (by positivity) hc.le
    (by positivity) (by positivity) (le_add_of_nonneg_right hε.le)
    (enlargedFamily F φ hbase hρ hnear r s hc) (diagonalPair φ hbase r s)
    (enlargedFamily_diagonal F φ hbase hρ hnear r s hc)
    (enlargedFamily_mem_lev F φ hbase hρ hnear r s hc hpath hl hε
      bounds.energy_le bounds.upper_gap)
    (enlargedFamily_boundary_mem F φ hbase hρ hnear r s hc hpath hl bounds.energy_le BY
      bounds.transverse_pos.le bounds.base_pos.le bounds.transverse_le bounds.endpoint_le
      bounds.transverse_gap bounds.left_gap bounds.right_gap)

/-- The constructed map kills every relative class of the actual parameter
pair. No filling map or homology-death assumption is required as an input. -/
theorem block_homology_eq_zero (K : Type) [Field K] (q : ℕ) :
    TopPair.singularHomologyMap
      (blockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds)
      (ModuleCat.of K K) q = 0 := by
  unfold blockPairMap
  apply ordinary_homology_eq_zero

/-- The filling applies to the ordinary weighted join of the two repeated
groups, with its original parametrization. -/
theorem blockPairMap_apply (x : I × Transverse Y r s) :
    (TopPair.Hom.fst
      (blockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds) x).val =
    H1LoopJoin.join (((r : ℝ) + 1) / ((r : ℝ) + 1 + ((s : ℝ) + 1)))
      (by positivity) ((div_lt_one (by positivity)).mpr
        (by have := Nat.cast_nonneg (α := ℝ) s; linarith))
      (diagonalPair φ hbase r s x).val.1 (diagonalPair φ hbase r s x).val.2
      (diagonalPair φ hbase r s x).property := by
  unfold blockPairMap
  exact ordinaryPairMap_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- On the repeated center the map is exactly the `(r+1)+(s+1)` iterate.
This checks the actual loop, not just its energy or its geometric image. -/
theorem blockPairMap_center (x : I) (y : Y) :
    (TopPair.Hom.fst
      (blockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds)
        (x, (fun _ => y), (fun _ => y))).val =
      SobolevIteration.iterateSphere (φ (x, y)) ((r + 1) + (s + 1)) (by omega) := by
  have hp : diagonalPair φ hbase r s (x, (fun _ => y), (fun _ => y)) =
      HingstonPause.iteratePair (φ (x, y)) (r + 1) (s + 1) (by omega) (by omega) := by
    apply Subtype.ext
    exact Prod.ext (family_diagonal φ hbase (x, y) r) (family_diagonal φ hbase (x, y) s)
  rw [blockPairMap_apply, hp]
  simpa only [HingstonPause.iteratePair, Nat.cast_add, Nat.cast_one] using
    join_iterates (φ (x, y)) (r + 1) (s + 1) (by omega) (by omega)

/-- The ordinary family has no connector overhead: its energy is at most
the repeated critical energy everywhere on the parameter domain. -/
theorem energy_blockPairMap_le (x : I × Transverse Y r s) :
    energy F (TopPair.Hom.fst
      (blockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds) x).val ≤
      (((r : ℝ) + 1 + ((s : ℝ) + 1)) * l) ^ 2 := by
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have hs : 0 < (s : ℝ) + 1 := by positivity
  let p := diagonalPair φ hbase r s x
  have hu : energy F p.val.1 / ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) * l ^ 2 := by
    apply (div_le_iff₀ hr).mpr
    have h := energy_concat_le F (familyBlocks φ hbase r (x.1, x.2.1))
      (fun i => bounds.energy_le x.1 (x.2.1 i))
    change energy F p.val.1 ≤ ((r : ℝ) + 1) ^ 2 * l ^ 2 at h
    nlinarith
  have hv : energy F p.val.2 / ((s : ℝ) + 1) ≤ ((s : ℝ) + 1) * l ^ 2 := by
    apply (div_le_iff₀ hs).mpr
    have h := energy_concat_le F (familyBlocks φ hbase s (x.1, x.2.2))
      (fun i => bounds.energy_le x.1 (x.2.2 i))
    change energy F p.val.2 ≤ ((s : ℝ) + 1) ^ 2 * l ^ 2 at h
    nlinarith
  rw [blockPairMap_apply, ← HingstonPause.value_zero hr hs, HingstonPause.energy_value]
  change ((r : ℝ) + 1 + ((s : ℝ) + 1) + 2 * 0) *
    (energy F p.val.1 / ((r : ℝ) + 1) + energy F p.val.2 / ((s : ℝ) + 1)) ≤ _
  simp only [mul_zero, add_zero]
  calc
    _ ≤ ((r : ℝ) + 1 + ((s : ℝ) + 1)) *
        (((r : ℝ) + 1 + ((s : ℝ) + 1)) * l ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ = _ := by ring

variable {a : ℝ} (ha : ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l < a)

/-- The same ordinary family in any cut strictly above the repeated critical
length. This supplies the lower map for critical-value extraction. -/
def lowerBlockPairMap :
    TopPair.ofSubset (X := TopCat.of (I × Transverse Y r s))
      (boundary (transverseBoundary r s BY)) ⟶
      BorelLoop.pairOf (BorelLoop.lev_mono F ha.le) := by
  let f := blockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds
  have hlow (x : I × Transverse Y r s) :
      (TopPair.Hom.fst f x).val ∈ BorelLoop.lev F a := by
    apply (Birkhoff.mem_lev_iff (lt_trans (by positivity) ha) _).mpr
    exact (energy_blockPairMap_le F φ hbase hρ hnear r s hc hpath hl hε BY bounds x).trans_lt
      ((sq_lt_sq₀ (by positivity) (le_of_lt (lt_trans (by positivity) ha))).mpr ha)
  let g : TopCat.of (boundary (transverseBoundary r s BY)) ⟶
      TopCat.of (BorelLoop.lev F (((r : ℝ) + 1 + ((s : ℝ) + 1)) * l)) := TopPair.Hom.snd f
  exact TopPair.ofHom
    (TopCat.ofHom ⟨fun x => ⟨(TopPair.Hom.fst f x).val, hlow x⟩,
      (continuous_subtype_val.comp (TopPair.Hom.fst f).hom.continuous).subtype_mk _⟩)
    g (by ext x; rfl)

/-- Raising the cut recovers exactly the map whose homology vanishes. -/
theorem lowerBlockPairMap_comp (hab : a ≤ ((r : ℝ) + 1 + ((s : ℝ) + 1)) * l + ε) :
    lowerBlockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds ha ≫
      BorelCrossing.incPair (BorelLoop.lev_mono F ha.le) (BorelLoop.lev_mono F hab) =
      blockPairMap F φ hbase hρ hnear r s hc hpath hl hε BY bounds := by
  ext : 2 <;> rfl

end Blocks

end
end Finsler.HingstonFilling
