module

public import Finsler.Residual.Window
public import Finsler.Topology.FiniteCut
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Bounded-length filling (Claude, UF prototype, piece BLF), in the degrees above n + 1.

At a regular cut t_a the ordinary cohomology of (t_a, M) is finite dimensional in every degree and
vanishes above some degree k (`FiniteCut.exists_finite_H`). Through the singular comparison, the
relative-to-absolute isomorphism, Kronecker duality and the length/energy isomorphism the homology
of the length sublevel t_a has the same properties in the degrees above n + 1. A finite dimensional
space of globally null classes dies at one common length (each class dies somewhere, by the colimit
description of the loop space homology), so all globally null classes of t_a in the degrees above
n + 1 die at one length B₀ (`blf_high`). -/

@[expose] public section

namespace Finsler.UFBLF

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.BorelCochain
open Finsler.SplitPairHomologyKernel

noncomputable section
set_option autoImplicit false

/-- **Uniform death of a finite dimensional family.** -/
theorem uniform_death {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (K : Submodule (ZMod 2) V)
    [Module.Finite (ZMod 2) K] (W : ℝ → Type*) [∀ b, AddCommGroup (W b)] [∀ b, Module (ZMod 2) (W b)]
    (f : ∀ b, V →ₗ[ZMod 2] W b) (L₀ : ℝ)
    (hmono : ∀ b b' v, L₀ ≤ b → b ≤ b' → f b v = 0 → f b' v = 0)
    (hdie : ∀ v ∈ K, ∃ b, L₀ ≤ b ∧ f b v = 0) :
    ∃ B, L₀ ≤ B ∧ ∀ v ∈ K, f B v = 0 := by
  classical
  obtain ⟨S, hS⟩ : K.FG := Module.Finite.iff_fg.mp inferInstance
  have hgen : ∀ v : S, ∃ b, L₀ ≤ b ∧ f b v = 0 := fun v =>
    hdie v (hS ▸ Submodule.subset_span v.2)
  choose bv hbv using hgen
  obtain ⟨B', hB'⟩ := (Set.finite_range bv).bddAbove
  refine ⟨max L₀ B', le_max_left _ _, fun v hv => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    exact hmono (bv ⟨x, hx⟩) _ x (hbv ⟨x, hx⟩).1
      ((hB' ⟨⟨x, hx⟩, rfl⟩).trans (le_max_right _ _)) (hbv ⟨x, hx⟩).2
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

variable (m : ℕ) (F : ReversibleMetric (m + 1))

/-- The comparison as a linear map. -/
def toAbsLin (a : ℝ) (i : ℕ) : H (levComplex F a) i →ₗ[ZMod 2] cohomologyZMod2 (TopCat.of (lev F a)) i :=
  (relativeToPool (levPair F a) i).hom ∘ₗ
    (Finsler.BorelComparison.ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) i).toLinearMap

theorem toAbsLin_apply (a : ℝ) (i : ℕ) (y : H (levComplex F a) i) :
    toAbsLin m F a i y = HRBridge.toAbsLev m F a i y := rfl

/-- In the degrees above n + 1 the ordinary cohomology of (t_a, M) is the absolute cohomology of t_a. -/
def absEquiv (a : ℝ) (i : ℕ) (hi : (m + 1) + 1 < i) :
    H (levComplex F a) i ≃ₗ[ZMod 2] cohomologyZMod2 (TopCat.of (lev F a)) i :=
  LinearEquiv.ofBijective (toAbsLin m F a i)
    ⟨fun y y' h => HRBridge.toAbsLev_injective m F a i hi h, fun w => by
      obtain ⟨y, hy⟩ := UFWindow.toAbsLev_surjective m F a i hi w
      exact ⟨y, hy⟩⟩

/-- Kronecker duality as a linear equivalence. -/
def kron (X : TopCat.{0}) (q : ℕ) :
    cohomologyZMod2 X q ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (homologyZMod2 X q) :=
  LinearEquiv.ofBijective (kroneckerMap X q).hom (kroneckerMap_bijective X q)

/-- **Finiteness and vanishing of the homology of a regular length sublevel** above degree n + 1. -/
theorem length_homology_finite (hfin : (Finsler.Geodesics.primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ Finsler.CriticalLevels.crit F) :
    ∃ k : ℕ, ∀ i : ℕ, (m + 1) + 1 < i →
      Module.Finite (ZMod 2) (homologyZMod2 (lengthSpace F a) i) ∧
        (k ≤ i → ∀ y : homologyZMod2 (lengthSpace F a) i, y = 0) := by
  obtain ⟨k, hfd, hz⟩ := Finsler.FiniteCut.exists_finite_H F (by omega) hfin ha hac
  refine ⟨k, fun i hi => ?_⟩
  let e1 := absEquiv m F a i hi
  let e2 := kron (TopCat.of (lev F a)) i
  let e3 := (StrictLengthEnergyBridge.homologyIso F a ha i).toLinearEquiv
  have hf1 : Module.Finite (ZMod 2) (cohomologyZMod2 (TopCat.of (lev F a)) i) := Module.Finite.equiv e1
  have hf2 : Module.Finite (ZMod 2) (Module.Dual (ZMod 2) (homologyZMod2 (TopCat.of (lev F a)) i)) :=
    Module.Finite.equiv e2
  have hf3 : Module.Finite (ZMod 2) (homologyZMod2 (TopCat.of (lev F a)) i) :=
    (Module.finite_dual_iff (ZMod 2)).mp hf2
  have hf3' : Module.Finite (ZMod 2) ((SmallChainCarrier.chains (energySpace F a)).homology i) := hf3
  refine ⟨Module.Finite.equiv e3.symm, fun hki y => ?_⟩
  have hs1 : Subsingleton (cohomologyZMod2 (TopCat.of (lev F a)) i) :=
    ⟨fun u v => e1.symm.injective ((hz i hki _).trans (hz i hki _).symm)⟩
  have hs2 : Subsingleton (Module.Dual (ZMod 2) (homologyZMod2 (TopCat.of (lev F a)) i)) :=
    ⟨fun u v => e2.symm.injective (Subsingleton.elim _ _)⟩
  have hs3 : Subsingleton (homologyZMod2 (TopCat.of (lev F a)) i) :=
    (Module.subsingleton_dual_iff (ZMod 2)).mp hs2
  have hs3' : Subsingleton ((SmallChainCarrier.chains (energySpace F a)).homology i) := hs3
  exact e3.injective (Subsingleton.elim _ _)

/-- A class dying at B dies at every larger length. -/
theorem enl_zero_mono {a b b' : ℝ} (hab : a ≤ b) (hbb' : b ≤ b') (i : ℕ)
    (y : homologyZMod2 (lengthSpace F a) i)
    (h : (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hab) i).hom y = 0) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.cut F (hab.trans hbb')) i).hom y = 0 := by
  have h1 := push_comp_apply (LengthFilteredLoopRotation.cut F hab) (LengthFilteredLoopRotation.cut F hbb') i y
  rw [h, map_zero] at h1
  exact h1.symm.trans rfl

/-- **Bounded-length filling** in the degrees above n + 1. -/
theorem blf_high (hfin : (Finsler.Geodesics.primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ Finsler.CriticalLevels.crit F) :
    ∃ B : ℝ, ∃ hB : a ≤ B, ∀ i : ℕ, (m + 1) + 1 < i → ∀ y : homologyZMod2 (lengthSpace F a) i,
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom y = 0 →
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hB) i).hom y = 0 := by
  obtain ⟨k, hk⟩ := length_homology_finite m F hfin ha hac
  have per : ∀ i : ℕ, ∃ B : ℝ, a ≤ B ∧ ∀ (hi : (m + 1) + 1 < i) (y : homologyZMod2 (lengthSpace F a) i),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom y = 0 →
        ∀ hB : a ≤ B, (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hB) i).hom y = 0 := by
    intro i
    by_cases hi : (m + 1) + 1 < i
    · have := (hk i hi).1
      let K := LinearMap.ker (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom
      obtain ⟨B, hB, hBK⟩ := uniform_death K
        (fun b => homologyZMod2 (lengthSpace F (max a b)) i)
        (fun b => (homologyPushZMod2 (LengthFilteredLoopRotation.cut F (le_max_left a b)) i).hom) a
        (fun b b' v hb hbb' h => enl_zero_mono m F (le_max_left a b) (max_le_max le_rfl hbb') i v h)
        (fun v hv => by
          obtain ⟨B, haB, h0B, he⟩ := StrictLengthHomologyStabilization.exists_equal F i v
            (0 : homologyZMod2 (lengthSpace F a) i) (by rw [map_zero]; exact hv)
          rw [map_zero] at he
          exact ⟨B, haB, enl_zero_mono m F haB (le_max_right a B) i v he⟩)
      refine ⟨max a B, le_max_left _ _, fun _ y hy hB' => ?_⟩
      exact hBK y hy
    · exact ⟨a, le_rfl, fun hi' => absurd hi' hi⟩
  choose Bi hBi hBik using per
  obtain ⟨B', hB'⟩ := (Set.finite_range (fun j : Fin k => Bi j)).bddAbove
  refine ⟨max a B', le_max_left _ _, fun i hi y hy => ?_⟩
  by_cases hik : i < k
  · have hle : Bi i ≤ max a B' := (hB' ⟨⟨i, hik⟩, rfl⟩).trans (le_max_right _ _)
    exact enl_zero_mono m F (hBi i) hle i y (hBik i hi y hy (hBi i))
  · rw [(hk i hi).2 (by omega) y, map_zero]

/-- Every regular sublevel is tame (official `FiniteCut.tame_lev`). -/
theorem tame_regular (hfin : (Finsler.Geodesics.primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ Finsler.CriticalLevels.crit F) :
    ∃ k : ℕ, Finsler.TameHomology.Tame (TopCat.of ↥(lev F a)) k := by
  obtain ⟨b, hab, hreg⟩ := Finsler.FiniteCut.exists_regular_above F hfin hac
  obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F (by omega) a b b ha hab.le le_rfl hreg
  exact Finsler.FiniteCut.tame_lev F (by omega) ha hab D

/-- **Finite homology of a regular length sublevel in every degree.** -/
theorem length_homology_tame (hfin : (Finsler.Geodesics.primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ Finsler.CriticalLevels.crit F) :
    ∃ k : ℕ, ∀ i : ℕ, Module.Finite (ZMod 2) (homologyZMod2 (lengthSpace F a) i) ∧
      (k ≤ i → ∀ y : homologyZMod2 (lengthSpace F a) i, y = 0) := by
  obtain ⟨k, hk⟩ := tame_regular m F hfin ha hac
  refine ⟨k, fun i => ?_⟩
  let e3 := (StrictLengthEnergyBridge.homologyIso F a ha i).toLinearEquiv
  have hf : Module.Finite (ZMod 2) ((SmallChainCarrier.chains (energySpace F a)).homology i) := hk.finite i
  refine ⟨Module.Finite.equiv e3.symm, fun hki y => ?_⟩
  have hs : Subsingleton ((SmallChainCarrier.chains (energySpace F a)).homology i) :=
    ModuleCat.subsingleton_of_isZero (hk.zero i hki)
  exact e3.injective (Subsingleton.elim _ _)

/-- **Bounded-length filling in every degree.** -/
theorem blf_all (hfin : (Finsler.Geodesics.primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ Finsler.CriticalLevels.crit F) :
    ∃ B : ℝ, ∃ hB : a ≤ B, ∀ i : ℕ, ∀ y : homologyZMod2 (lengthSpace F a) i,
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom y = 0 →
        (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hB) i).hom y = 0 := by
  obtain ⟨k, hk⟩ := length_homology_tame m F hfin ha hac
  have per : ∀ i : ℕ, ∃ B : ℝ, a ≤ B ∧ ∀ (y : homologyZMod2 (lengthSpace F a) i),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom y = 0 →
        ∀ hB : a ≤ B, (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hB) i).hom y = 0 := by
    intro i
    have := (hk i).1
    let K := LinearMap.ker (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom
    obtain ⟨B, hB, hBK⟩ := uniform_death K
      (fun b => homologyZMod2 (lengthSpace F (max a b)) i)
      (fun b => (homologyPushZMod2 (LengthFilteredLoopRotation.cut F (le_max_left a b)) i).hom) a
      (fun b b' v hb hbb' h => enl_zero_mono m F (le_max_left a b) (max_le_max le_rfl hbb') i v h)
      (fun v hv => by
        obtain ⟨B, haB, h0B, he⟩ := StrictLengthHomologyStabilization.exists_equal F i v
          (0 : homologyZMod2 (lengthSpace F a) i) (by rw [map_zero]; exact hv)
        rw [map_zero] at he
        exact ⟨B, haB, enl_zero_mono m F haB (le_max_right a B) i v he⟩)
    exact ⟨max a B, le_max_left _ _, fun y hy hB' => hBK y hy⟩
  choose Bi hBi hBik using per
  obtain ⟨B', hB'⟩ := (Set.finite_range (fun j : Fin k => Bi j)).bddAbove
  refine ⟨max a B', le_max_left _ _, fun i y hy => ?_⟩
  by_cases hik : i < k
  · have hle : Bi i ≤ max a B' := (hB' ⟨⟨i, hik⟩, rfl⟩).trans (le_max_right _ _)
    exact enl_zero_mono m F (hBi i) hle i y (hBik i y hy (hBi i))
  · rw [(hk i).2 (by omega) y, map_zero]

end

end Finsler.UFBLF
