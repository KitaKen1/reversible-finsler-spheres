module

public import Finsler.Topology.FiniteCut
public import Finsler.Topology.PairTriple
public import Finsler.Topology.BorelComparison
public import Finsler.Topology.RelativeKronecker
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-! Ordinary cohomology of a space and its mod 2 singular homology; spheres.

For a space X, the ordinary cohomology of the pair (X, ∅) (as the pair of univ and univ ∩ ∅) is the
dual of the relative homology, which is the homology of X (the empty part has no homology).
Hence in every degree in which the homology of X is finite dimensional, so is the cohomology, with
the same dimension. For the unit sphere of an inner product space of dimension m + 1 with m ≥ 1 the
homology has dimension one in the degrees 0 and m and vanishes otherwise (Tau Ceti). -/

@[expose] public section

namespace Finsler.TrivHq

open CategoryTheory Limits AlgebraicTopology Finsler.TameHomology Finsler.BorelCochain
open Finsler.BorelPair Finsler.PairTriple Finsler.BorelComparison Finsler.BorelLoop
open Finsler.RelativeCohomology
open Set Topology Module Metric

noncomputable section

/-- The empty space has no homology. -/
theorem isZero_Hq_of_isEmpty (X : TopCat.{0}) [IsEmpty X] (k : ℕ) : IsZero (Hq X k) := by
  cases k with
  | zero =>
    have hπ : IsEmpty (ZerothHomotopy X) :=
      ⟨fun c ↦ ZerothHomotopy.rec (motive := fun _ ↦ False) (fun x ↦ isEmptyElim x) c⟩
    exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun c ↦ isEmptyElim c)).of_iso
      (X.singularHomology₀Iso coeff)
  | succ k =>
    exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ (k + 1) coeff X
      k.succ_ne_zero

/-- The pair (X, ∅). -/
abbrev emptyPair (X : TopCat.{0}) : TopPair.{0} :=
  pairOf (inter_subset_left : (univ : Set X) ∩ ∅ ⊆ univ)

theorem isEmpty_snd (X : TopCat.{0}) : IsEmpty (emptyPair X).snd := ⟨fun x => x.2.2⟩

/-- The relative homology of (X, ∅) is the homology of the ambient space. -/
def relEquiv (X : TopCat.{0}) (k : ℕ) :
    Hq (emptyPair X).fst k ≃ₗ[ZMod 2] Hrel (emptyPair X) k := by
  haveI := isEmpty_snd X
  have hmono : Mono ((emptyPair X).singularHomologyπ coeff k) :=
    ((emptyPair X).singularHomology_exact_space coeff k).mono_g
      ((isZero_Hq_of_isEmpty (emptyPair X).snd k).eq_of_src _ _)
  have hepi : Epi ((emptyPair X).singularHomologyπ coeff k) := by
    cases k with
    | zero => infer_instance
    | succ q =>
      exact ((emptyPair X).singularHomology_exact_relative coeff (q + 1) q rfl).epi_f
        ((isZero_Hq_of_isEmpty (emptyPair X).snd q).eq_of_tgt _ _)
  exact LinearEquiv.ofBijective ((emptyPair X).singularHomologyπ coeff k).hom
    ⟨(ModuleCat.mono_iff_injective _).mp hmono, (ModuleCat.epi_iff_surjective _).mp hepi⟩

/-- The homology of univ is the homology of the space. -/
def univEquiv (X : TopCat.{0}) (k : ℕ) : Hq (emptyPair X).fst k ≃ₗ[ZMod 2] Hq X k :=
  (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (Homeomorph.Set.univ X))).toLinearEquiv

/-- The cohomology of (X, ∅) is the dual of the homology of X. -/
def dualEquiv (X : TopCat.{0}) (k : ℕ) :
    H (triv (emptyPair X)) k ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Hrel (emptyPair X) k) :=
  (ordinaryEquiv (emptyPair X) (𝟙 _) (Category.comp_id _) k).trans
    (RelativeKronecker.equiv (emptyPair X) k)

/-- **Cohomology and homology of a space.** -/
theorem finite_finrank (X : TopCat.{0}) (k : ℕ) (hf : Module.Finite (ZMod 2) (Hq X k)) :
    Module.Finite (ZMod 2) (H (triv (emptyPair X)) k) ∧
      finrank (ZMod 2) (H (triv (emptyPair X)) k) = finrank (ZMod 2) (Hq X k) := by
  let e₁ := (univEquiv X k).symm.trans (relEquiv X k)
  haveI : Module.Finite (ZMod 2) (Hrel (emptyPair X) k) := Module.Finite.equiv e₁
  haveI : Module.Finite (ZMod 2) (H (triv (emptyPair X)) k) :=
    Module.Finite.equiv (dualEquiv X k).symm
  refine ⟨inferInstance, ?_⟩
  rw [(dualEquiv X k).finrank_eq, Subspace.dual_finrank_eq, ← e₁.finrank_eq]

/-! ### Spheres -/

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sphere_Hq_zero {m : ℕ} (h : finrank ℝ E = m + 1) (hm : 1 ≤ m) {k : ℕ} (hk0 : k ≠ 0)
    (hkm : k ≠ m) : IsZero (Hq (TopCat.of (sphere (0 : E) 1)) k) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  exact (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne coeff h hkm).of_iso
    ((TauCeti.reducedSingularHomologySuccIso coeff q).app _).symm

theorem sphere_Hq_top {m : ℕ} (h : finrank ℝ E = m + 1) (hm : 1 ≤ m) :
    Module.Finite (ZMod 2) (Hq (TopCat.of (sphere (0 : E) 1)) m) ∧
      finrank (ZMod 2) (Hq (TopCat.of (sphere (0 : E) 1)) m) = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  let e := (((TauCeti.reducedSingularHomologySuccIso coeff q).app
    (TopCat.of (sphere (0 : E) 1))).symm ≪≫ TauCeti.reducedSingularHomologySphereIso coeff h).toLinearEquiv
  haveI : Module.Finite (ZMod 2) (Hq (TopCat.of (sphere (0 : E) 1)) (q + 1)) :=
    Module.Finite.equiv e.symm
  refine ⟨inferInstance, ?_⟩
  rw [e.finrank_eq]
  exact Module.finrank_self (ZMod 2)

theorem sphere_Hq_zero_deg {m : ℕ} (h : finrank ℝ E = m + 1) (hm : 1 ≤ m) :
    Module.Finite (ZMod 2) (Hq (TopCat.of (sphere (0 : E) 1)) 0) ∧
      finrank (ZMod 2) (Hq (TopCat.of (sphere (0 : E) 1)) 0) = 1 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
  obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : PathConnectedSpace (sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, h]
      exact_mod_cast (by omega : 1 < m + 1)) 0 zero_le_one)
  let X := TopCat.of (sphere (0 : E) 1)
  have hz := TauCeti.isZero_reducedSingularHomologyFunctor_zero coeff X
  have hmono : Mono (X.singularHomology₀ε coeff) :=
    Preadditive.mono_of_isZero_kernel _ (by
      rw [← TauCeti.reducedSingularHomologyFunctor_zero_obj]
      exact hz)
  have hsec := TauCeti.singularHomology₀Section_singularHomology₀ε coeff (X := X) p
  have hepi : Epi (X.singularHomology₀ε coeff) := by
    refine ⟨fun {Z} g h hgh => ?_⟩
    have := congrArg (fun φ => TauCeti.singularHomology₀Section coeff p ≫ φ) hgh
    simp only [← Category.assoc, hsec, Category.id_comp] at this
    exact this
  let e := LinearEquiv.ofBijective (X.singularHomology₀ε coeff).hom
    ⟨(ModuleCat.mono_iff_injective _).mp hmono, (ModuleCat.epi_iff_surjective _).mp hepi⟩
  haveI : Module.Finite (ZMod 2) (Hq X 0) := Module.Finite.equiv e.symm
  refine ⟨inferInstance, ?_⟩
  rw [e.finrank_eq]
  exact Module.finrank_self (ZMod 2)

end Sphere

end

end Finsler.TrivHq
