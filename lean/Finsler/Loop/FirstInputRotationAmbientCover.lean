module

public import Finsler.Loop.FirstInputRotationFilteredCap
public import Finsler.Loop.SmallCapSubspaceLift
public import Finsler.Topology.AnnularSupportedCut

/-! Localize the genuine ambient rotating Thom cap into the proper
cut rectangle cover. Open extensions of its relative rectangles and
the actual annular far-zero set give a full ambient cover. -/

@[expose] public section
namespace Finsler.FirstInputRotationAmbientCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationFilteredCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)

abbrev ambient : TopCat.{0} :=
  TopCat.of (_root_.unitInterval × (ClosedInterval × CompactNearJoinParameters.tube α β R))

def gap (z : ambient α β R) : ℝ := distance n (z.2.1, α z.2.2.val.1)

theorem continuous_gap : Continuous (gap α β R) := by
  apply (continuous_distance n).comp
  have hf : Continuous (fun z : ambient α β R => α z.2.2.val.1) := by fun_prop
  exact (continuous_fst.comp continuous_snd).prodMk hf

def proper : Set (ambient α β R) := {z | gap α β R z ≤ r}

def properHomeo : (space α β R r) ≃ₜ proper α β R r where
  toFun z := ⟨(z.1, z.2.val), z.2.property⟩
  invFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def properIso : space α β R r ≅ TopCat.of (proper α β R r) :=
  TopCat.isoOfHomeo (properHomeo α β R r)

def source : space α β R r ⟶ ambient α β R :=
  SmallCapSubspaceLift.source (ambient α β R) (space α β R r) (proper α β R r) (properIso α β R r)

variable (hR : R ≤ 1 / 2)

def ambientEvaluation : ambient α β R ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.2.1,
    FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (z.1, z.2.2)),
    (continuous_fst.comp continuous_snd).prodMk
      ((FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num))).continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩

theorem evaluation_gap (z : ambient α β R) :
    distance n (ambientEvaluation α β R hR z) = gap α β R z :=
  FirstInputRotationFamily.time_distance α β R (hR.trans_lt (by norm_num)) z.2.1 z.1 z.2.2

theorem source_evaluation (hr : r < 1) :
    source α β R r ≫ ambientEvaluation α β R hR = evaluation α β R r hR hr := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

def ambientThom (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (ambient α β R) n :=
  cochainPullback (ambientEvaluation α β R hR) n (AnnularSelfCut.cocycle n hn h)

theorem ambientThom_closed (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainCoboundary (ZMod 2) (ambient α β R) n (ambientThom α β R hR hn h) = 0 :=
  pullback_closed _ n _ (AnnularSelfCut.cocycle_closed n hn h)

theorem thom_source (hr : r < 1) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (source α β R r) n (ambientThom α β R hR hn h) = thom α β R r hR hr hn h := by
  rw [ambientThom, ← pullback_comp, source_evaluation α β R r hR hr]
  rfl

variable (η : ℝ)

def oldCover (i : space α β R r) : Set (proper α β R r) :=
  (properIso α β R r).inv ⁻¹' rectangle α β R r η i

theorem oldCover_open (i : space α β R r) : IsOpen (oldCover α β R r η i) :=
  (rectangle_open α β R r η i).preimage (properIso α β R r).inv.hom.continuous

theorem exists_extension (i : space α β R r) :
    ∃ O : Set (ambient α β R), IsOpen O ∧ Subtype.val ⁻¹' O = oldCover α β R r η i :=
  isOpen_induced_iff.mp (oldCover_open α β R r η i)

def extension (i : space α β R r) : Set (ambient α β R) :=
  (exists_extension α β R r η i).choose

theorem extension_open (i : space α β R r) : IsOpen (extension α β R r η i) :=
  (exists_extension α β R r η i).choose_spec.1

theorem extension_preimage (i : space α β R r) :
    Subtype.val ⁻¹' extension α β R r η i = oldCover α β R r η i :=
  (exists_extension α β R r η i).choose_spec.2

def far (ρ : ℝ) : Set (ambient α β R) := {z | ρ < gap α β R z}

def cover (ρ : ℝ) : Option (space α β R r) → Set (ambient α β R) := fun i =>
  match i with
  | none => far α β R ρ
  | some i => extension α β R r η i ∩ {z | gap α β R z < r}

theorem cover_open (ρ : ℝ) (i : Option (space α β R r)) :
    IsOpen (cover α β R r η ρ i) := by
  cases i with
  | none => exact isOpen_lt continuous_const (continuous_gap α β R)
  | some i =>
    exact (extension_open α β R r η i).inter (isOpen_lt (continuous_gap α β R) continuous_const)

theorem cover_univ (hη : 0 < η) {ρ : ℝ} (hρr : ρ < r) :
    ⋃ i, cover α β R r η ρ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : gap α β R z < r
  · let zB : proper α β R r := ⟨z, hz.le⟩
    let y := (properIso α β R r).inv zB
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      ((rectangle_univ α β R r hη).symm ▸ Set.mem_univ y)
    refine Set.mem_iUnion.mpr ⟨some i, ?_, hz⟩
    have hi' : zB ∈ oldCover α β R r η i := hi
    rw [← extension_preimage α β R r η i] at hi'
    exact hi'
  · exact Set.mem_iUnion.mpr ⟨none, hρr.trans_le (le_of_not_gt hz)⟩

theorem near_image (ρ : ℝ) (i : space α β R r) :
    cover α β R r η ρ (some i) ⊆ source α β R r '' rectangle α β R r η i := by
  intro z hz
  have hzr : gap α β R z < r := hz.2
  let zB : proper α β R r := ⟨z, hzr.le⟩
  have hi : (properIso α β R r).inv zB ∈ rectangle α β R r η i := by
    change zB ∈ oldCover α β R r η i
    rw [← extension_preimage α β R r η i]
    exact hz.1
  refine ⟨(properIso α β R r).inv zB, hi, ?_⟩
  have he := ConcreteCategory.congr_hom (properIso α β R r).inv_hom_id zB
  exact congrArg Subtype.val he

theorem thom_far_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (ambient α β R) (far α β R ρ)) n
      (ambientThom α β R hR hn h) = 0 := by
  apply pullback_support (ambientEvaluation α β R hR) (far α β R ρ) (exterior n ρ)
    _ n (AnnularSelfCut.cocycle n hn h) (AnnularSupportedCut.cocycle_supported n hn h)
  intro z hz
  change ρ < distance n (ambientEvaluation α β R hR z)
  rw [evaluation_gap]
  exact hz

theorem parent_control (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (q : ℕ)
    (σ : ((ambient α β R).smallSingularSubcomplex (cover α β R r η ρ) : SSet) _⦋n + q⦌)
    (hc : (TopCat.toSSet.obj (ambient α β R)).ιChainComplex σ.val ≫
      absoluteChain (ambient α β R) n q (n + q) rfl (ambientThom α β R hR hn h) ≠ 0) :
    ∃ i, Set.range ((ambient α β R).toSSetObjEquiv _ σ.val) ⊆
      source α β R r '' rectangle α β R r η i := by
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (ambient α β R)
    (cover α β R r η ρ) σ.val).mp σ.property
  cases i with
  | none => exact (hc (SupportedCap.cap_zero_on_simplex _ _ n q (n + q) rfl
      (ambientThom α β R hR hn h) (thom_far_zero α β R hR hn h) σ.val hi)).elim
  | some i => exact ⟨i, hi.trans (near_image α β R r η ρ i)⟩

def cap (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    DegreeLoweringHomology.Map (small (ambient α β R) (cover α β R r η ρ))
      (small (space α β R r) (rectangle α β R r η)) n :=
  SmallCapSubspaceLift.operation (ambient α β R) (space α β R r) (proper α β R r) (properIso α β R r)
    (cover α β R r η ρ) (rectangle α β R r η) n (ambientThom α β R hR hn h)
    (fun q σ hc => parent_control α β R r hR η hn h q σ hc)
    (ambientThom_closed α β R hR hn h)

theorem cap_source (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (q : ℕ) :
    (cap α β R r hR η hn h).component q ≫
      (inclusion (space α β R r) (rectangle α β R r η) ≫ push (source α β R r)).f q =
        (inclusion (ambient α β R) (cover α β R r η ρ)).f (n + q) ≫
          absoluteChain (ambient α β R) n q (n + q) rfl (ambientThom α β R hR hn h) :=
  SmallCapSubspaceLift.component_inclusion (ambient α β R) (space α β R r)
    (proper α β R r) (properIso α β R r) (cover α β R r η ρ) (rectangle α β R r η)
    n (ambientThom α β R hR hn h) (fun q σ hc => parent_control α β R r hR η hn h q σ hc) q

end
end Finsler.FirstInputRotationAmbientCover
