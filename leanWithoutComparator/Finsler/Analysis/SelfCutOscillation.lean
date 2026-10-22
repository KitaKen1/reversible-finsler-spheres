module

public import Finsler.Topology.SelfCutEndpoints
public import Finsler.Analysis.SelfCutLengthControl
public import Finsler.Geometry.NormalizationContinuity

/-! Whole-parent tested-length oscillation is obtainable by actual
barycentric subdivision. Nonzero T capping supplies a point outside the
short-loop subspace, and fine-parent oscillation transfers its lower length
bound to every point of that parent. This does not yet assert a filtered
bound for the full time-cross/Thom chain operation. -/

@[expose] public section
namespace Finsler.SelfCutOscillation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SobolevLength Finsler.RelativeCapAssociativity
open Set Filter
open scoped Topology Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {n : ℕ}

theorem continuous_length (F : ReversibleMetric n) : Continuous (length F) := by
  apply continuous_iff_seqContinuous.mpr
  intro v u hu
  exact NormalizationContinuity.tendsto_length_seq F hu

def testedLength (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) :
    neighborhood n r → ℝ := fun z => length F (tested n hr z)

theorem continuous_testedLength (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) :
    Continuous (testedLength F hr) :=
  (continuous_length F).comp (tested n hr).continuous

def oscillationCover (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (ε : ℝ)
    (z : neighborhood n r) : Set (neighborhood n r) :=
  {w | |testedLength F hr w - testedLength F hr z| < ε / 2}

theorem oscillationCover_open (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    (ε : ℝ) (z : neighborhood n r) : IsOpen (oscillationCover F hr ε z) :=
  isOpen_lt (((continuous_testedLength F hr).sub continuous_const).abs) continuous_const

theorem oscillationCover_covers (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ⋃ z, oscillationCover F hr ε z = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact mem_iUnion.mpr ⟨z, by simp [oscillationCover, hε]⟩

theorem oscillationCover_bound (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    (ε : ℝ) {z v w : neighborhood n r}
    (hv : v ∈ oscillationCover F hr ε z) (hw : w ∈ oscillationCover F hr ε z) :
    |testedLength F hr v - testedLength F hr w| < ε := by
  have h := abs_sub_le (testedLength F hr v) (testedLength F hr z) (testedLength F hr w)
  rw [abs_sub_comm (testedLength F hr z)] at h
  change |testedLength F hr v - testedLength F hr z| < ε / 2 at hv
  change |testedLength F hr w - testedLength F hr z| < ε / 2 at hw
  linarith

theorem exists_fine_subdivision (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of (neighborhood n r)) _⦋k⦌) :
    ∃ N, ∀ M ≥ N,
      (TopCat.toSSet.obj (TopCat.of (neighborhood n r))).ιChainComplex σ ≫
        (End.of (TauCeti.singularSubdivisionChainMap coeff
          (TopCat.of (neighborhood n r))) ^ M).f k ∈
          supported (TopCat.of (neighborhood n r)) (oscillationCover F hr ε) k := by
  obtain ⟨N, hN⟩ := TauCeti.exists_iterate_singularSubdivision_factor_small coeff
    (oscillationCover F hr ε) (oscillationCover_open F hr ε)
    (oscillationCover_covers F hr hε) σ
  exact ⟨N, fun M hM => (TauCeti.mem_smallSingularChains_iff _).mpr (hN M hM)⟩

def short (F : ReversibleMetric n) (L : ℝ) : Set (SphereLoop n) := {u | length F u < L}

def shortTested (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1) (L : ℝ) :
    Set (neighborhood n r) := {z | testedLength F hr z < L}

theorem testedCocycle_short (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    (p : ℕ) (L : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0) :
    cochainPullback
      (SupportedCap.subspaceMap (TopCat.of (neighborhood n r)) (shortTested F hr L)) p
        (NormalizedSelfCut.testedCocycle n p hr T) = 0 := by
  let g : TopCat.of (shortTested F hr L) ⟶ TopCat.of (short F L) :=
    TopCat.ofHom ⟨fun z => ⟨tested n hr z.val, z.property⟩,
      ((tested n hr).continuous.comp continuous_subtype_val).subtype_mk _⟩
  have he : SupportedCap.subspaceMap (TopCat.of (neighborhood n r)) (shortTested F hr L) ≫
      TopCat.ofHom (tested n hr) =
    g ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L) := by
    ext z : 1
    rfl
  rw [NormalizedSelfCut.testedCocycle, ← SupportedCapNaturality.pullback_comp,
    he, SupportedCapNaturality.pullback_comp, hT]
  simp [cochainPullback]

theorem nonzero_cap_witness (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    (p q : ℕ) (L : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0)
    (σ : TopCat.toSSet.obj (TopCat.of (neighborhood n r)) _⦋p + q⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (neighborhood n r))).ιChainComplex σ ≫
      absoluteChain (TopCat.of (neighborhood n r)) p q (p + q) rfl
        (NormalizedSelfCut.testedCocycle n p hr T) ≠ 0) :
    ∃ z ∈ Set.range ((TopCat.of (neighborhood n r)).toSSetObjEquiv _ σ),
      L ≤ testedLength F hr z := by
  by_contra h
  push Not at h
  have hs : σ ∈ ((TopCat.of (neighborhood n r)).smallSingularSubcomplex
      (fun _ : Unit => shortTested F hr L)).obj (Opposite.op ⦋p + q⦌) := by
    apply (TopCat.mem_smallSingularSubcomplex_iff (TopCat.of (neighborhood n r))
      (fun _ : Unit => shortTested F hr L) σ).mpr
    exact ⟨(), fun z hz => h z hz⟩
  have hc : (TopCat.toSSet.obj (TopCat.of (neighborhood n r))).ιChainComplex σ ∈
      supported (TopCat.of (neighborhood n r)) (fun _ : Unit => shortTested F hr L) (p + q) :=
    TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff)
    (U := fun _ : Unit => shortTested F hr L) ⟨σ, hs⟩
  exact hσ (SupportedCapAnnihilation.cap_zero_of_supported
    (X := TopCat.of (neighborhood n r)) (shortTested F hr L) p q
    (NormalizedSelfCut.testedCocycle n p hr T) (testedCocycle_short F hr p L T hT) hc)

theorem parent_tested_lower (F : ReversibleMetric n) {r : ℝ} (hr : r ≤ 1)
    {ε L : ℝ} {P : Set (neighborhood n r)}
    (hP : ∀ v ∈ P, ∀ w ∈ P, |testedLength F hr v - testedLength F hr w| < ε)
    (hw : ∃ w ∈ P, L ≤ testedLength F hr w) :
    ∀ z ∈ P, L - ε ≤ testedLength F hr z := by
  obtain ⟨w, hw, hL⟩ := hw
  intro z hz
  have h := (abs_lt.mp (hP z hz w hw)).1
  linarith

theorem parent_retained_lt (F : ReversibleMetric n) {r ε a L : ℝ}
    (hr : r ≤ 1) (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (p q : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (short F L))
      p T = 0)
    (σ : TopCat.toSSet.obj (TopCat.of (neighborhood n r)) _⦋p + q⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (neighborhood n r))).ιChainComplex σ ≫
      absoluteChain (TopCat.of (neighborhood n r)) p q (p + q) rfl
        (NormalizedSelfCut.testedCocycle n p hr T) ≠ 0)
    (hfine : ∃ z, Set.range ((TopCat.of (neighborhood n r)).toSSetObjEquiv _ σ) ⊆
      oscillationCover F hr ε z)
    (ha : ∀ z ∈ Set.range ((TopCat.of (neighborhood n r)).toSSetObjEquiv _ σ),
      length F z.val.2 < a) :
    ∀ z ∈ Set.range ((TopCat.of (neighborhood n r)).toSSetObjEquiv _ σ),
      length F (retained n hr z) < a - L + 3 * ε := by
  obtain ⟨center, hcenter⟩ := hfine
  have hlower := parent_tested_lower F hr
    (fun v hv w hw => oscillationCover_bound F hr ε (hcenter hv) (hcenter hw))
    (nonzero_cap_witness F hr p q L T hT σ hσ)
  intro z hz
  exact SelfCutLengthControl.filtered_retained_lt F hε (toTube n hr z)
    (z.property.trans_le hrr) (ha z hz) (hlower z hz)

end
end Finsler.SelfCutOscillation
