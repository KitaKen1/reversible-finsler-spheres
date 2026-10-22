module

public import Finsler.Topology.JoinedHalfCollars

/-! In the second half of the actual joined H1 loop, self-evaluation and
the retained cut loop factor literally through the second input. The
tested loop need not do so. Shuffle degeneracy still needs its degree
condition and an actual normalized cut cochain. -/

@[expose] public section
namespace Finsler.SecondHalfCutFactor

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevAffine
open Finsler.SobolevConcat Finsler.CompactH1Alignment Finsler.H1LoopJoin
open Finsler.SobolevSpherePath
open Finsler.H1JoinContinuity Finsler.H1FiberBase Finsler.H1SelfCutNeighborhood
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.JoinedHalfCollars

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {n : ℕ}

theorem suffix_path (u v : Space n) (t : ClosedInterval)
    (hm : continuousRepresentative u 1 = continuousRepresentative v 0) :
    restrict (concat u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num))
      (secondTime t).property one_mem_unit (secondTime t).property.2 =
      restrict v t.property one_mem_unit t.property.2 := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ _ _ _ hτ, representative_restrict _ _ _ _ hτ]
  have hθ := aff_mem_Icc (secondTime t).property one_mem_unit hτ
  have hhalf : (1 / 2 : ℝ) ≤ (secondTime t : ℝ) := by
    change 1 / 2 ≤ (1 + (t : ℝ)) / 2
    linarith [t.property.1]
  have hθ' : aff (secondTime t) 1 τ ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    refine ⟨?_, hθ.2⟩
    have hnonneg : 0 ≤ (1 - (secondTime t : ℝ)) * τ :=
      mul_nonneg (sub_nonneg.mpr (secondTime t).property.2) hτ.1
    change 1 / 2 ≤ (secondTime t : ℝ) + (1 - (secondTime t : ℝ)) * τ
    linarith
  rw [representative_concat_right u v (by norm_num) (by norm_num) hm hθ']
  congr 1
  norm_num [rightMap, aff, secondTime]
  <;> ring

theorem joined_point (z : composable n) : point (pairJoin z) = point z.val.2 := by
  apply Subtype.ext
  exact (basepoint_join (1 / 2) (by norm_num) (by norm_num) _ _ z.property).trans z.property

theorem joined_endpoint (z : ClosedInterval × composable n) :
    endpoint (second z) = endpoint (z.1, z.2.val.2) := by
  apply Subtype.ext
  exact second_evaluate _ _ z.1 (end_match _ _ z.2.property)

theorem evaluation_factor {X : Type} [TopologicalSpace X] (u : C(X, composable n)) :
    secondFamily u ≫ selfEvaluation n =
      AnnularSelfCut.familyMap (rightLoop u) ≫ selfEvaluation n := by
  ext z : 1
  exact Prod.ext (joined_point (u z.2)) (joined_endpoint (z.1, u z.2))

theorem annular_thom_factor {X : Type} [TopologicalSpace X] (u : C(X, composable n))
    (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (secondFamily u) n (AnnularSelfCut.cocycle n hn h) =
      cochainPullback (AnnularSelfCut.familyMap (rightLoop u)) n
        (AnnularSelfCut.cocycle n hn h) := by
  simp only [AnnularSelfCut.cocycle, ← SupportedCapNaturality.pullback_comp, evaluation_factor]

def domain (r : ℝ) : Set (ClosedInterval × composable n) :=
  second ⁻¹' neighborhood n r

def joined {r : ℝ} : C(domain (n := n) r, neighborhood n r) :=
  ⟨fun z => ⟨second z.val, z.property⟩,
    (continuous_second.comp continuous_subtype_val).subtype_mk _⟩

theorem native_mem {r : ℝ} (z : domain (n := n) r) :
    (z.val.1, z.val.2.val.2) ∈ neighborhood n r := by
  have hz : distance n (second z.val) < r := z.property
  exact lt_of_eq_of_lt (second_distance z.val).symm hz

def native {r : ℝ} : C(domain (n := n) r, neighborhood n r) :=
  ⟨fun z => ⟨(z.val.1, z.val.2.val.2), native_mem z⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)))).subtype_mk _⟩

theorem retained_eq {r : ℝ} (hr : r ≤ 1) (z : domain (n := n) r) :
    retained n hr (joined z) = retained n hr (native z) := by
  apply sphereLoop_data_injective
  change concat (H1ShortArc.arc (point (pairJoin z.val.2)) (endpoint (second z.val)))
    (suffixPath (toTube n hr (joined z))) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) = _
  have hs : suffixPath (toTube n hr (joined z)) = suffixPath (toTube n hr (native z)) :=
    suffix_path _ _ z.val.1 (end_match _ _ z.val.2.property)
  rw [joined_point, joined_endpoint, hs]
  rfl

theorem retained_factor {r : ℝ} (hr : r ≤ 1) :
    TopCat.ofHom (joined (n := n) (r := r)) ≫ TopCat.ofHom (retained n hr) =
      TopCat.ofHom (native (n := n) (r := r)) ≫ TopCat.ofHom (retained n hr) := by
  ext z : 1
  exact retained_eq hr z

end
end Finsler.SecondHalfCutFactor
