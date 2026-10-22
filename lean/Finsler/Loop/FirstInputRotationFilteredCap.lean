module

public import Finsler.Loop.FirstInputRotationCochains
public import Finsler.Topology.SequentialCapWitness
public import Finsler.Topology.JoinedFilteredCap

/-! The actual closed rotating two-cap lifts into a bounded proper
cut domain. The fixed retained output stays below A-L+5epsilon on the
whole parent, not merely on the tested face. -/

@[expose] public section
namespace Finsler.FirstInputRotationFilteredCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCochains
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)

def rectangle (η : ℝ) (center : space α β R r) : Set (space α β R r) :=
  PairDistanceCover.cover id η center.1 ×ˢ PairDistanceCover.cover id η center.2

theorem rectangle_open (η : ℝ) (center : space α β R r) :
    IsOpen (rectangle α β R r η center) :=
  (PairDistanceCover.cover_open id continuous_id η center.1).prod
    (PairDistanceCover.cover_open id continuous_id η center.2)

theorem rectangle_univ {η : ℝ} (hη : 0 < η) :
    ⋃ center, rectangle α β R r η center = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  refine Set.mem_iUnion.mpr ⟨z, ?_⟩
  constructor <;> simpa only [PairDistanceCover.cover, Set.mem_ofPred_eq, id_eq, dist_self] using hη

variable (hR : R ≤ 1 / 2) (hr : r < 1)

def domain (F : ReversibleMetric n) (B : ℝ) : Set (space α β R r) :=
  {z | SobolevLength.length F (outputMap α β R r hR hr z) < B}

def source (F : ReversibleMetric n) (B : ℝ) :
    TopCat.of (domain α β R r hR hr F B) ⟶ space α β R r :=
  SupportedCap.subspaceMap (space α β R r) (domain α β R r hR hr F B)

def retained (F : ReversibleMetric n) (B : ℝ) :
    TopCat.of (domain α β R r hR hr F B) ⟶
      TopCat.of (JoinedFilteredCap.sublevel F B) :=
  TopCat.ofHom ⟨fun z => ⟨outputMap α β R r hR hr z.val, z.property⟩,
    ((outputMap α β R r hR hr).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def Adequate (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (F : ReversibleMetric n) (B η : ℝ) : Prop :=
  ∀ q (σ : ((space α β R r).smallSingularSubcomplex (rectangle α β R r η) : SSet) _⦋n + (p + q)⦌),
    (TopCat.toSSet.obj (space α β R r)).ιChainComplex σ.val ≫
      PartialDoubleCap.cap (space α β R r) n p q (thom α β R r hR hr hn h)
        (tested α β R r hR hr p T) ≠ 0 →
      Set.range ((space α β R r).toSSetObjEquiv _ σ.val) ⊆ domain α β R r hR hr F B

variable (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (F : ReversibleMetric n) (B η : ℝ)
  (hgood : Adequate α β R r hR hr hn h p T F B η)

def component (q : ℕ) :
    (small (space α β R r) (rectangle α β R r η)).X (n + (p + q)) ⟶
      (chains (TopCat.of (domain α β R r hR hr F B))).X q :=
  PartialDoubleCap.localized (space α β R r) (rectangle α β R r η)
    (domain α β R r hR hr F B) n p (thom α β R r hR hr hn h)
    (tested α β R r hR hr p T) hgood q

theorem component_inclusion (q : ℕ) :
    component α β R r hR hr hn h p T F B η hgood q ≫
        (push (source α β R r hR hr F B)).f q =
      (inclusion (space α β R r) (rectangle α β R r η)).f (n + (p + q)) ≫
        PartialDoubleCap.cap (space α β R r) n p q (thom α β R r hR hr hn h)
          (tested α β R r hR hr p T) :=
  PartialDoubleCap.localized_inclusion _ _ _ _ _ _ _ _ q

theorem component_boundary
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    component α β R r hR hr hn h p T F B η hgood (q + 1) ≫
        (chains (TopCat.of (domain α β R r hR hr F B))).d (q + 1) q =
      (small (space α β R r) (rectangle α β R r η)).d
        (n + (p + (q + 1))) (n + (p + q)) ≫
          component α β R r hR hr hn h p T F B η hgood q := by
  let j := push (source α β R r hR hr F B)
  haveI : Mono (j.f q) := SupportedCap.subspacePush_mono _ _ q
  apply (cancel_mono (j.f q)).mp
  rw [Category.assoc, ← j.comm, ← Category.assoc, component_inclusion]
  simp only [Category.assoc]
  rw [component_inclusion]
  simpa only [Category.assoc] using
    double_cap_boundary α β R r hR hr (rectangle α β R r η) hn h p T hT q

def operation (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    DegreeLoweringHomology.Map (small (space α β R r) (rectangle α β R r η))
      (chains (TopCat.of (domain α β R r hR hr F B))) (n + p) :=
  NestedCapHomology.operation n p (component α β R r hR hr hn h p T F B η hgood)
    (component_boundary α β R r hR hr hn h p T F B η hgood hT)

def retainedOperation (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    DegreeLoweringHomology.Map (small (space α β R r) (rectangle α β R r η))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (n + p) :=
  (operation α β R r hR hr hn h p T F B η hgood hT).post
    (push (retained α β R r hR hr F B))

theorem retained_source :
    retained α β R r hR hr F B ≫ SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
      (JoinedFilteredCap.sublevel F B) =
        source α β R r hR hr F B ≫ outputMap α β R r hR hr := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem retained_component_inclusion
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    (retainedOperation α β R r hR hr hn h p T F B η hgood hT).component q ≫
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
          (JoinedFilteredCap.sublevel F B))).f q =
      eqToHom (congrArg (small (space α β R r) (rectangle α β R r η)).X (Nat.add_assoc n p q)) ≫
        (inclusion (space α β R r) (rectangle α β R r η)).f (n + (p + q)) ≫
          PartialDoubleCap.cap (space α β R r) n p q (thom α β R r hR hr hn h)
            (tested α β R r hR hr p T) ≫ (push (outputMap α β R r hR hr)).f q := by
  have he := congrArg (fun f => (push f).f q) (retained_source α β R r hR hr F B)
  simp only [push_comp, HomologicalComplex.comp_f] at he
  change (eqToHom _ ≫ component α β R r hR hr hn h p T F B η hgood q ≫
    (push (retained α β R r hR hr F B)).f q) ≫ _ = _
  simp only [Category.assoc]
  rw [he, ← Category.assoc (component α β R r hR hr hn h p T F B η hgood q), component_inclusion]
  simp only [Category.assoc]

theorem exists_uniform [CompactSpace P] [CompactSpace Q]
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ κ > 0, κ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < κ →
      ∃ η > 0, η ≤ b ∧ ∀ (hn : 1 ≤ n) (δ ρ : ℝ) (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
        (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        Adequate α β R r hR hr hn h p T F (A - L + 5 * ε) η := by
  obtain ⟨κ, hκ, hκ1, hscale⟩ :=
    FirstInputRotationAdequacy.exists_uniform_scale α β r hr F hε hb hradius
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro R hR hRκ
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRκ
  refine ⟨η, hη, hηb, ?_⟩
  intro hn δ ρ h p L A T hshort hA q σ hc
  let X := space α β R r
  obtain ⟨center, hcenter⟩ := (TopCat.mem_smallSingularSubcomplex_iff X
    (rectangle α β R r η) σ.val).mp σ.property
  have hseq := SequentialCapWitness.sequential_nonzero_faces X n p q
    (thom α β R r hR hr hn h) (tested α β R r hR hr p T) σ.val
    (by simpa only [PartialDoubleCap.cap, Category.assoc] using hc)
  have hrange := (SequentialCapWitness.sequential_faces_range X n p q σ.val).2
  have hbgt : ∀ z ∈ Set.range (X.toSSetObjEquiv _ σ.val),
      FirstInputRotationAdequacy.budget α β R r F z < A := by
    intro z hz
    exact hA z.2.val.2
  exact had center.1 center.2 (Set.range (X.toSSetObjEquiv _ σ.val)) hcenter
    p L A T hshort hbgt
    (SequentialCapWitness.front X p q (SequentialCapWitness.back X n (p + q) σ.val))
    hrange hseq.2

end
end Finsler.FirstInputRotationFilteredCap
