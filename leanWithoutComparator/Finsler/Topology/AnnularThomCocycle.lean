module

public import Finsler.Topology.NearDiagonalCohomology
public import Finsler.Topology.NormalizedThomComparison

/-! An actual normalized diagonal cocycle vanishing both outside the
outer tube and throughout a closed positive inner tube. Its actual far-
relative Thom identification is separate; absolute-class equality alone
is not used as a substitute for that identification. -/

@[expose] public section
namespace Finsler.AnnularThomCocycle

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelEvaluation
open Finsler.DiagonalCohomology
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

local instance (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient n) 1)
local instance (n : ℕ) : CompactSpace (product n) :=
  inferInstanceAs (CompactSpace (Sphere n × Sphere n))
local instance (n : ℕ) : T2Space (product n) :=
  inferInstanceAs (T2Space (Sphere n × Sphere n))

def parts (n : ℕ) (δ ρ : ℝ) (i : Bool) : Set (product n) :=
  if i then NearDiagonalCohomology.near n δ else DiagonalAvoidanceCocycle.far n ρ

def pair (n : ℕ) (δ ρ : ℝ) : TopPair.{0} := TopPair.ofSubset (⋃ i, parts n δ ρ i)

def inclusion (n : ℕ) (δ ρ : ℝ) : TopCat.of (⋃ i, parts n δ ρ i) ⟶ product n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem parts_compact (n : ℕ) (δ ρ : ℝ) (i : Bool) : IsCompact (parts n δ ρ i) := by
  cases i
  · exact (DiagonalAvoidanceCocycle.far_closed n ρ).isCompact
  · exact NearDiagonalCohomology.near_compact n δ

theorem parts_disjoint (n : ℕ) {δ ρ : ℝ} (h : δ < ρ) :
    Disjoint (parts n δ ρ false) (parts n δ ρ true) := by
  apply Set.disjoint_left.mpr
  intro z hf hn
  change ρ ≤ ‖(z.2 : Ambient n) - z.1‖ at hf
  change ‖(z.2 : Ambient n) - z.1‖ ≤ δ at hn
  linarith

theorem restriction_zero (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    (cohPullback (inclusion n δ ρ) n).hom (ambientClass n hn) = 0 := by
  apply CohomologyClopen.union_eq_zero (parts n δ ρ) (parts_compact n δ ρ) (parts_disjoint n h.2.2) n
  intro i
  rw [← Cup.pullback_comp]
  have he : CohomologyClopen.unionInclusion (parts n δ ρ) i ≫ inclusion n δ ρ =
      SupportedCap.subspaceMap (product n) (parts n δ ρ i) := by
    ext z : 1
    rfl
  rw [he]
  cases i
  · exact DiagonalAvoidanceCocycle.far_restriction_zero n hn (h.1.trans h.2.2)
  · exact NearDiagonalCohomology.restriction_zero n hn h.2.1

theorem exists_relative (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    ∃ a : (pair n δ ρ).singularCohomology coeff (ZMod 2) coeff n,
      (relativeToPool (pair n δ ρ) n).hom a = ambientClass n hn := by
  obtain ⟨a, ha⟩ := CochainComparison.relative_lift (pair n δ ρ) n
    (ambientClass n hn) (restriction_zero n hn h)
  refine ⟨a, ?_⟩
  change (cohomologyEquiv (product n) n).symm
    (((pair n δ ρ).singularCohomologyπ coeff (ZMod 2) coeff n).hom a) = _
  exact (congrArg (cohomologyEquiv (product n) n).symm ha).trans
    ((cohomologyEquiv (product n) n).symm_apply_apply _)

def relativeClass (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    (pair n δ ρ).singularCohomology coeff (ZMod 2) coeff n := (exists_relative n hn h).choose

def relativeCocycle (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    RelativeCupCochain.relative (pair n δ ρ) n :=
  CochainClass.representative (RelativeCup.cx (pair n δ ρ)) n (relativeClass n hn h)

def raw (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (product n) n :=
  RelativeCupCochain.toAmbient (pair n δ ρ) n (relativeCocycle n hn h)

theorem raw_closed (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainCoboundary (ZMod 2) (product n) n (raw n hn h) = 0 :=
  RelativeCup.toAmbient_closed (pair n δ ρ) n (relativeCocycle n hn h)
    (CochainClass.representative_closed (RelativeCup.cx (pair n δ ρ)) n (relativeClass n hn h))

theorem raw_class (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    CochainClass.classOf (cochainCxZMod2 (product n)) n (raw n hn h) (raw_closed n hn h) = ambientClass n hn := by
  have hc := CochainClass.classOf_representative (RelativeCup.cx (pair n δ ρ)) n (relativeClass n hn h)
  have he := RelativeCup.relativeToPool_classOf (pair n δ ρ) n (relativeCocycle n hn h)
    (CochainClass.representative_closed (RelativeCup.cx (pair n δ ρ)) n (relativeClass n hn h))
  exact he.symm.trans ((congrArg (relativeToPool (pair n δ ρ) n).hom hc).trans
    (exists_relative n hn h).choose_spec)

def ambient (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (product n) n := SingularNormalization.normalize (product n) n (raw n hn h)

theorem ambient_closed (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainCoboundary (ZMod 2) (product n) n (ambient n hn h) = 0 :=
  SingularNormalization.normalize_closed _ n _ (raw_closed n hn h)

theorem ambient_normalized (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    AlgebraicTopology.DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (product n))
      (ambient n hn h) := SingularNormalization.normalize_degeneracies _ n _

theorem ambient_class (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    CochainClass.classOf (cochainCxZMod2 (product n)) n (ambient n hn h) (ambient_closed n hn h) = ambientClass n hn :=
  (SingularNormalization.normalize_class_pos (product n) n hn (raw n hn h) (raw_closed n hn h)).trans
    (raw_class n hn h)

theorem supported (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (inclusion n δ ρ) n (ambient n hn h) = 0 :=
  SingularNormalization.normalize_supported _ n _
    (RelativeCupCochain.restriction_toAmbient (pair n δ ρ) n (relativeCocycle n hn h))

theorem pullback_zero_of_range (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) {X : TopCat.{0}} (f : X ⟶ product n)
    (hf : ∀ x, f x ∈ ⋃ i, parts n δ ρ i) : cochainPullback f n (ambient n hn h) = 0 := by
  let g : X ⟶ TopCat.of (⋃ i, parts n δ ρ i) :=
    TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ inclusion n δ ρ := by ext x : 1; rfl
  rw [he, SupportedCapNaturality.pullback_comp, supported]
  simp only [cochainPullback, map_zero]

theorem near_zero (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (NearDiagonalCohomology.inclusion n δ) n (ambient n hn h) = 0 :=
  pullback_zero_of_range n hn h (NearDiagonalCohomology.inclusion n δ)
    (fun z => mem_iUnion.mpr ⟨true, z.property⟩)

theorem far_zero (n : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (FarDiagonalCohomology.farPair n ρ).map n (ambient n hn h) = 0 :=
  pullback_zero_of_range n hn h (FarDiagonalCohomology.farPair n ρ).map
    (fun z => mem_iUnion.mpr ⟨false, z.property⟩)

end
end Finsler.AnnularThomCocycle
