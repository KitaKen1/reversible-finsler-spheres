module

public import Finsler.Topology.SecondHalfCutFactor
public import Finsler.Topology.JoinDirectionComparison
public import Finsler.Topology.SelfCutParameterFamily

/-! The original first-corrected join on P × (cut-time × Q).
Its second loop is literally beta, without a first-input correction.
Use the existing actual partial cut domain so bounded product lifts
can target it directly. The retained map factors through the actual
native second-input cut domain, before passing to homology. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfFamily

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.H1JoinContinuity Finsler.H1FiberBase Finsler.SelfCutThomCocycle
open Finsler.SupportedSelfCut Finsler.CochainComparison
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)

def nearMap : C(K, JoinDirectionComparison.nearPairs n) :=
  ⟨fun z => ⟨(α z.val.1, β z.val.2.2), hK z⟩,
    ((α.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (β.continuous.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))).subtype_mk _⟩

def joinedInputs : C(K, composable n) :=
  JoinDirectionComparison.firstPair.comp (nearMap α β K hK)

def family : TopCat.of K ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => JoinedHalfCollars.second (z.val.2.1, joinedInputs α β K hK z),
    JoinedHalfCollars.continuous_second.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).prodMk
        (joinedInputs α β K hK).continuous)⟩

def projection : TopCat.of K ⟶ TopCat.of (ClosedInterval × Q) :=
  TopCat.ofHom ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

def native : TopCat.of (ClosedInterval × Q) ⟶ parameters n := AnnularSelfCut.familyMap β

theorem family_actual (z : K) : family α β K hK z =
    (JoinedHalfCollars.secondTime z.val.2.1,
      JoinDirectionComparison.firstJoin (1 / 2) (by norm_num) (by norm_num)
        (α z.val.1) (β z.val.2.2)) := rfl

theorem evaluation_factor : family α β K hK ≫ selfEvaluation n =
    projection K ≫ native β ≫ selfEvaluation n := by
  ext z : 1
  exact Prod.ext
    (SecondHalfCutFactor.joined_point (joinedInputs α β K hK z))
    (SecondHalfCutFactor.joined_endpoint (z.val.2.1, joinedInputs α β K hK z))

theorem annular_thom_factor (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (family α β K hK) n (AnnularSelfCut.cocycle n hn h) =
      cochainPullback (projection K ≫ native β) n (AnnularSelfCut.cocycle n hn h) := by
  simp only [AnnularSelfCut.cocycle, ← SupportedCapNaturality.pullback_comp,
    ← Category.assoc, evaluation_factor]

theorem distance_eq (z : K) : distance n (family α β K hK z) = distance n (native β z.val.2) :=
  JoinedHalfCollars.second_distance (z.val.2.1, joinedInputs α β K hK z)

def domain (r : ℝ) : Set (P × (ClosedInterval × Q)) :=
  SelfCutParameterFamily.domain K (fun _ : PUnit.{1} => family α β K hK) (fun _ => r) PUnit.unit

def cutMap (r : ℝ) : TopCat.of (domain α β K hK r) ⟶ TopCat.of (neighborhood n r) :=
  SelfCutParameterFamily.toCut K (fun _ : PUnit.{1} => family α β K hK) (fun _ => r) PUnit.unit

def nativeDomain (r : ℝ) : Set (ClosedInterval × Q) := native β ⁻¹' neighborhood n r

theorem native_mem {r : ℝ} (z : domain α β K hK r) : z.val.2 ∈ nativeDomain β r := by
  have hz : distance n (family α β K hK ⟨z.val, z.property.1⟩) < r :=
    (cutMap α β K hK r z).property
  exact lt_of_eq_of_lt (distance_eq α β K hK ⟨z.val, z.property.1⟩).symm hz

def nativeProjection {r : ℝ} : C(domain α β K hK r, nativeDomain β r) :=
  ⟨fun z => ⟨z.val.2, native_mem α β K hK z⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

def nativeCut (r : ℝ) : TopCat.of (nativeDomain β r) ⟶ TopCat.of (neighborhood n r) :=
  TopCat.ofHom ⟨fun z => ⟨native β z.val, z.property⟩,
    ((native β).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem native_projection_source (r : ℝ) :
    TopCat.ofHom (nativeProjection α β K hK (r := r)) ≫
      SupportedCap.subspaceMap (TopCat.of (ClosedInterval × Q)) (nativeDomain β r) =
        SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q))) (domain α β K hK r) ≫
          CartesianMonoidalCategory.snd (TopCat.of P) (TopCat.of (ClosedInterval × Q)) := by
  ext z : 1
  rfl

theorem retained_factor {r : ℝ} (hr : r ≤ 1) :
    cutMap α β K hK r ≫ TopCat.ofHom (retained n hr) =
      TopCat.ofHom (nativeProjection α β K hK (r := r)) ≫ nativeCut β r ≫
        TopCat.ofHom (retained n hr) := by
  ext z : 1
  let w : SecondHalfCutFactor.domain (n := n) r :=
    ⟨(z.val.2.1, joinedInputs α β K hK ⟨z.val, z.property.1⟩), (cutMap α β K hK r z).property⟩
  exact SecondHalfCutFactor.retained_eq hr w

theorem cut_evaluation_factor (r : ℝ) :
    cutMap α β K hK r ≫ SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n =
      TopCat.ofHom (nativeProjection α β K hK (r := r)) ≫ nativeCut β r ≫
        SupportedCap.subspaceMap (parameters n) (neighborhood n r) ≫ selfEvaluation n := by
  ext z : 1
  exact Prod.ext
    (SecondHalfCutFactor.joined_point (joinedInputs α β K hK ⟨z.val, z.property.1⟩))
    (SecondHalfCutFactor.joined_endpoint
      (z.val.2.1, joinedInputs α β K hK ⟨z.val, z.property.1⟩))

end
end Finsler.OriginalSecondHalfFamily
