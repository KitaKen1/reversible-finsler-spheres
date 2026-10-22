module

public import Finsler.Topology.AmbientLensPieces
public import Finsler.Topology.LevelBounds

/-! obtain finite-dimensional ordinary lens groups from the
actual loop comparison, and pass finiteness to a local label by surjectivity. -/

@[expose] public section

namespace Finsler.AmbientLensFinite

open CategoryTheory Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.AmbientPenalty Finsler.AmbientK Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.BorelComparison Finsler.FlowLens Finsler.LensFamily
open Finsler.PairTriple Finsler.BorelLens Finsler.BorelDeformation Finsler.LensK
open Finsler.PairCutTransportK Finsler.AmbientInclusionK Finsler.SampleK
open Finsler.LensLabels Finsler.LocalCoverK Finsler.LevelBounds Finsler.CriticalLevels
open Finsler.LensContinuation

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (M : ℕ) [NeZero M] (F : ReversibleMetric n) {lam : ℝ}
variable {g : Om n (2 * M) → ℝ} (D : Descent (Om n (2 * M)) g)
variable {l u a b T τ : ℝ} (hl : 0 < l) (hlu : l ≤ u)
variable (hla : l ^ 2 ≤ a) (hab : a ≤ b) (hbu : b ≤ u ^ 2) (hT : 0 ≤ T)
variable (hsa : sub (penW F (2 * M) lam) (l ^ 2) = sub g (l ^ 2))
variable (hsb : sub (penW F (2 * M) lam) (u ^ 2) = sub g (u ^ 2))
variable (hτ : 0 ≤ τ) (hpush : ∀ Q, g Q < u ^ 2 → g (D.flow τ Q) < b)

/-- The actual map from loops to the deformed ambient lens pair. -/
def loopLensPair : pairOf (lev_mono F hlu) ⟶ pairOf (lensY_subset D a b T) :=
  samplePair (F := F) (M := M) hl hlu ≫ inclEnergyPair M F lam (pow_le_pow_left₀ hl.le hlu 2) ≫
    toTightPair D hla hab hbu hsa hsb hτ hpush ≫
      inclPair (sub_mono g hab) (lensY_subset D a b T) (sub_subset_lensY D hab hT) subset_rfl

variable (hlam : 0 ≤ lam) {τl : ℝ} (hτl : 0 ≤ τl)
variable (hpushl : ∀ Q, g Q < a → g (D.flow τl Q) < l ^ 2)

include hlam hτl hpushl in
theorem loopLensPair_native (q : ℕ)
    (hs : Function.Bijective (nativePull (samplePair (F := F) (M := M) hl hlu) q)) :
    Function.Bijective (nativePull
      (loopLensPair M F D hl hlu hla hab hbu hT hsa hsb hτ hpush) q) := by
  unfold loopLensPair
  apply native_comp_bijective _ _ q hs
  apply native_comp_bijective _ _ q (incl_native_bijective M F hlam _ q)
  exact native_comp_bijective _ _ q
    (toTight_native D hla hab hbu hsa hsb hτ hpush hτl hpushl q)
    (bijective_nativePull_inclPair _ _ _ _ (lensDeformation D hT) q)

include hlam hτl hpushl hla hab hbu hT hsa hsb hτ hpush in
/-- Regular wide loop cuts supply finite-dimensionality before using any finrank-zero claim. -/
theorem lens_finite (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (hlreg : l ∉ crit F) (hureg : u ∉ crit F)
    (hs : ∀ q, Function.Bijective (nativePull (samplePair (F := F) (M := M) hl hlu) q)) (q : ℕ) :
    Module.Finite (ZMod 2) (H (triv (pairOf (lensY_subset D a b T))) q) := by
  obtain ⟨_, hfinite, _⟩ := cross_finite F hn hfin hl hlu hlreg hureg
  letI := hfinite q
  let f := loopLensPair M F D hl hlu hla hab hbu hT hsa hsb hτ hpush
  have hf : ∀ j, Function.Bijective (nativePull f j) := fun j =>
    loopLensPair_native M F D hl hlu hla hab hbu hT hsa hsb hτ hpush hlam hτl hpushl j (hs j)
  exact Module.Finite.of_injective (Hmap (trivHom f) q)
    (BorelInvariance.bijective_Hmap (Category.comp_id _) (Category.comp_id _) f
      (by simp) hf q).injective

include hlam hτl hpushl hla hbu hT hsa hsb hτ hpush in
theorem crossing_finite (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (hlreg : l ∉ crit F) (hureg : u ∉ crit F)
    (hs : ∀ q, Function.Bijective (nativePull (samplePair (F := F) (M := M) hl hlu) q)) (q : ℕ) :
    Module.Finite (ZMod 2) (H (triv (pairOf (sub_mono g hab))) q) := by
  letI := lens_finite M F D hl hlu hla hab hbu hT hsa hsb hτ hpush hlam hτl hpushl
    hn hfin hlreg hureg hs q
  exact Module.Finite.of_surjective
    (Hmap (trivHom (inclPair (sub_mono g hab) (lensY_subset D a b T)
      (sub_subset_lensY D hab hT) subset_rfl)) q)
    (lens_bijective D hab hT q).surjective

section Local

variable {W : TopCat.{0}} {f : W → ℝ} (E : Descent W f) {a' a b T : ℝ}
variable {U V : Set W}

/-- A local lens is a quotient of the finite-dimensional whole crossing, not merely a group
whose finrank is bounded by that of the crossing. -/
theorem local_lens_finite (hf : Continuous f) (hab : a ≤ b) (ha' : a' < a) (hT : 0 ≤ T)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (htrap : ∀ w, f w < b → a' ≤ f (E.flow T w) → w ∈ U ∪ V) (q : ℕ)
    [Module.Finite (ZMod 2)
      (H (triv (pairOf ((sub_subset_lensY E hab hT).trans (lensY_subset E a b T)))) q)] :
    Module.Finite (ZMod 2) (H (triv (pairOf (partY_sub_partU f E U a b T))) q) := by
  let e := labelEquiv E hf hab ha' hT hU hV hdis htrap q
  let m := (LinearMap.fst (ZMod 2) _ _).comp e.toLinearMap
  exact Module.Finite.of_surjective m (fun y => label_surjective E hf hab ha' hT hU hV hdis htrap q y)

end Local

end

end Finsler.AmbientLensFinite
