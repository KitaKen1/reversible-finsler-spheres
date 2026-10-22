module

public import Finsler.Loop.FirstInputRotationAdequacy
public import Finsler.Topology.PartialDoubleCapFiltered
public import Finsler.Topology.NestedCapHomology
public import Finsler.Topology.SupportedCapHomology

/-! Genuine closed Thom and tested pullbacks on the proper rotating
cut domain. These are defined throughout that domain; no closure of an
ambient tested zero extension is assumed. -/

@[expose] public section
namespace Finsler.FirstInputRotationCochains

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1SelfCutNeighborhood Finsler.SupportedSelfCut
open Finsler.SelfCutThomCocycle
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1)

abbrev space : TopCat.{0} :=
  TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r)

def evaluation : space α β R r ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (FirstInputRotatingCut.rotation α β R r hR hr z).val,
    continuous_subtype_val.comp (FirstInputRotatingCut.rotation α β R r hR hr).continuous⟩

def testedMap : space α β R r ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom (FirstInputRotationAdequacy.tested α β R r hR hr)

def outputMap : space α β R r ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom (FirstInputRotationAdequacy.output α β R r hR hr)

def thom (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (space α β R r) n :=
  cochainPullback (evaluation α β R r hR hr) n (AnnularSelfCut.cocycle n hn h)

def tested (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (space α β R r) p :=
  cochainPullback (testedMap α β R r hR hr) p T

theorem thom_closed (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainCoboundary (ZMod 2) (space α β R r) n (thom α β R r hR hr hn h) = 0 :=
  pullback_closed (evaluation α β R r hR hr) n _ (AnnularSelfCut.cocycle_closed n hn h)

theorem tested_closed (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (space α β R r) p (tested α β R r hR hr p T) = 0 :=
  pullback_closed (testedMap α β R r hR hr) p T hT

theorem evaluation_distance (s : _root_.unitInterval) (z : FirstInputRotatingCut.source α β R r) :
    distance n (evaluation α β R r hR hr (s, z)) = distance n (z.val.1, α z.val.2.val.1) := by
  change distance n (z.val.1,
    FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (s, z.val.2)) = _
  exact FirstInputRotationFamily.time_distance α β R (hR.trans_lt (by norm_num)) z.val.1 s z.val.2

def collar (δ : ℝ) : Set (space α β R r) :=
  {z | distance n (z.2.val.1, α z.2.val.2.val.1) ≤ δ}

theorem thom_inner_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (space α β R r) (collar α β R r δ)) n
      (thom α β R r hR hr hn h) = 0 := by
  apply pullback_support (evaluation α β R r hR hr) (collar α β R r δ)
    {z | distance n z ≤ δ} _ n (AnnularSelfCut.cocycle n hn h)
    (AnnularSelfCut.cocycle_small_zero n hn h)
  intro z hz
  change distance n (evaluation α β R r hR hr z) ≤ δ
  rw [evaluation_distance]
  exact hz

theorem double_cap_boundary {ι : Type*} (V : ι → Set (space α β R r))
    (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) (q : ℕ) :
    ((inclusion (space α β R r) V).f (n + (p + (q + 1))) ≫
      PartialDoubleCap.cap (space α β R r) n p (q + 1)
        (thom α β R r hR hr hn h) (tested α β R r hR hr p T)) ≫
        (chains (space α β R r)).d (q + 1) q =
      (small (space α β R r) V).d (n + (p + (q + 1))) (n + (p + q)) ≫
        ((inclusion (space α β R r) V).f (n + (p + q)) ≫
          PartialDoubleCap.cap (space α β R r) n p q
            (thom α β R r hR hr hn h) (tested α β R r hR hr p T)) := by
  let X := space α β R r
  let f := SupportedCapHomology.absoluteOperation X n
    (thom α β R r hR hr hn h) (thom_closed α β R r hR hr hn h)
  let g := SupportedCapHomology.absoluteOperation X p
    (tested α β R r hR hr p T) (tested_closed α β R r hR hr p T hT)
  have hf : f.component (p + (q + 1)) ≫ (chains X).d (p + (q + 1)) (p + q) =
      (chains X).d (n + (p + (q + 1))) (n + (p + q)) ≫ f.component (p + q) := by
    rw [← Nat.add_assoc p q 1]
    exact f.comm (p + q)
  change ((inclusion X V).f _ ≫ (f.component (p + (q + 1)) ≫ g.component (q + 1))) ≫
    (chains X).d _ _ = (small X V).d _ _ ≫
      ((inclusion X V).f _ ≫ (f.component (p + q) ≫ g.component q))
  simp only [Category.assoc]
  rw [g.comm, ← Category.assoc (f.component _), hf]
  simp only [← Category.assoc]
  rw [(inclusion X V).comm]

end
end Finsler.FirstInputRotationCochains
