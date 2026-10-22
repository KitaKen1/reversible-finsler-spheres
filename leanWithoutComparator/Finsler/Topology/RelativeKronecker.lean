module

public import Finsler.Topology.Kronecker
public import Finsler.Topology.RelativeCup
public import TauCeti.Algebra.Homology.Kronecker

/-! The actual relative universal-coefficient comparison over F₂.
Apply Tau Ceti's general Kronecker equivalence to the relative singular chain
complex; no finite-dimensionality or comparison hypothesis is added. -/

@[expose] public section

namespace Finsler.RelativeKronecker

open CategoryTheory SphereOddDegree Finsler.CochainComparison

noncomputable section

local instance : Module.Injective (ZMod 2) (ZMod 2) := moduleInjective_ZMod2 _
local instance : CategoryTheory.Injective coeff :=
  Module.injective_object_of_injective_module (ZMod 2) (ZMod 2)

abbrev chains (P : TopPair.{0}) := P.singularChainComplex coeff

def comparison (P : TopPair.{0}) (n : ℕ) :
    RelativeCup.cohomology P n →ₗ[ZMod 2] RelativeDual.relative (ZMod 2) P n :=
  ModuleCat.homLinearEquiv.toLinearMap.comp
    (TauCeti.ChainComplex.kronecker (ZMod 2) (chains P) coeff n)

def equiv (P : TopPair.{0}) (n : ℕ) :
    RelativeCup.cohomology P n ≃ₗ[ZMod 2] RelativeDual.relative (ZMod 2) P n :=
  (TauCeti.ChainComplex.kroneckerEquiv (ZMod 2) (chains P) coeff n).trans
    ModuleCat.homLinearEquiv

theorem equiv_apply (P : TopPair.{0}) (n : ℕ) (a : RelativeCup.cohomology P n) :
    equiv P n a = comparison P n a := by
  exact congrArg (fun g => g.hom) (TauCeti.ChainComplex.kroneckerEquiv_apply n a)

theorem comparison_bijective (P : TopPair.{0}) (n : ℕ) :
    Function.Bijective (comparison P n) := by
  have h : (equiv P n : RelativeCup.cohomology P n → RelativeDual.relative (ZMod 2) P n) =
      comparison P n := funext (equiv_apply P n)
  rw [← h]
  exact (equiv P n).bijective

theorem naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (a : RelativeCup.cohomology Q n) :
    comparison P n
        ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom a) =
      (comparison Q n a).comp (P.singularHomologyMap f coeff n).hom := by
  exact congrArg (fun g => g.hom)
    (TauCeti.ChainComplex.kronecker_naturality (TopPair.singularChainComplexMap f coeff) n a)

theorem equiv_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (a : RelativeCup.cohomology Q n) :
    equiv P n
        ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom a) =
      (equiv Q n a).comp (P.singularHomologyMap f coeff n).hom := by
  rw [equiv_apply, equiv_apply]
  exact naturality f n a

theorem equiv_inv_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (φ : RelativeDual.relative (ZMod 2) Q n) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n).hom
        ((equiv Q n).symm φ) =
      (equiv P n).symm (φ.comp (P.singularHomologyMap f coeff n).hom) := by
  apply (equiv P n).injective
  rw [LinearEquiv.apply_symm_apply, equiv_natural, LinearEquiv.apply_symm_apply]

/-- Evaluation on actual classes of cocycles and cycles. -/
theorem comparison_classOf (P : TopPair.{0}) (n : ℕ)
    (ψ : RelativeCupCochain.relative P n) (hψ : RelativeCupCochain.differential P n ψ = 0)
    (z : (chains P).cycles n) :
    comparison P n (CochainClass.classOf (RelativeCup.cx P) n ψ hψ)
        (((chains P).homologyπ n).hom z) = ψ.hom (((chains P).iCycles n).hom z) := by
  have h := TauCeti.ChainComplex.kronecker_homologyπ n
    ((RelativeCup.cx P).cyclesMk ψ (n + 1) (CochainClass.next_eq n) hψ)
  have hz := ConcreteCategory.congr_hom h z
  exact hz.trans (congrArg (fun g => g.hom (((chains P).iCycles n).hom z))
    ((RelativeCup.cx P).i_cyclesMk _ _ _ _))

def absoluteComparison (X : TopCat.{0}) (n : ℕ) :
    (native X).homology n →ₗ[ZMod 2] Module.Dual (ZMod 2) (homologyZMod2 X n) :=
  ModuleCat.homLinearEquiv.toLinearMap.comp
    (TauCeti.ChainComplex.kronecker (ZMod 2) (chainCxZMod2 X) coeff n)

theorem absolute_classOf (X : TopCat.{0}) (n : ℕ)
    (φ : (native X).X n) (hφ : ((native X).d n (n + 1)).hom φ = 0)
    (z : (chainCxZMod2 X).cycles n) :
    absoluteComparison X n (CochainClass.classOf (native X) n φ hφ)
        (((chainCxZMod2 X).homologyπ n).hom z) =
      φ.hom (((chainCxZMod2 X).iCycles n).hom z) := by
  have h := TauCeti.ChainComplex.kronecker_homologyπ n
    ((native X).cyclesMk φ (n + 1) (CochainClass.next_eq n) hφ)
  have hz := ConcreteCategory.congr_hom h z
  exact hz.trans (congrArg (fun g => g.hom (((chainCxZMod2 X).iCycles n).hom z))
    ((native X).i_cyclesMk _ _ _ _))

theorem absolute_cochain_comparison (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    cohomologyEquiv X n (CochainClass.classOf (cochainCxZMod2 X) n φ hφ) =
      CochainClass.classOf (native X) n φ hφ :=
  CochainClass.classOf_map (cochainCxZMod2 X) (cochainIso X).hom n φ hφ hφ

/-- Tau Ceti's general evaluation agrees with Lean Pool's classifier on the
actual absolute comparison, proved by evaluating on homology cycles. -/
theorem absolute_pool_comparison (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    absoluteComparison X n (cohomologyEquiv X n a) = (kroneckerMap X n).hom a := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X n a
  have hc := absolute_cochain_comparison X n φ hφ
  change cohomologyEquiv X n (cocycleClass X n φ hφ) = _ at hc
  rw [hc, kroneckerMap_cocycleClass]
  ext z
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective ((chainCxZMod2 X).homologyπ n)).mp inferInstance z
  exact (absolute_classOf X n φ hφ c).trans (kroneckerFunctional_apply X n φ hφ c).symm

theorem fromRelative_native (P : TopPair.{0}) (n : ℕ) (a : RelativeCup.cohomology P n) :
    absoluteComparison P.fst n ((P.singularCohomologyπ coeff (ZMod 2) coeff n).hom a) =
      RelativeDual.fromRelative (ZMod 2) P n (comparison P n a) := by
  exact congrArg (fun g => g.hom)
    (TauCeti.ChainComplex.kronecker_naturality (P.singularChainComplexπ coeff) n a)

/-- The native relative UCT square commutes with the previously used absolute
Lean Pool classifier and with the actual relative-to-absolute map. -/
theorem fromRelative_comparison (P : TopPair.{0}) (n : ℕ) (a : RelativeCup.cohomology P n) :
    RelativeDual.fromRelative (ZMod 2) P n (comparison P n a) =
      (kroneckerMap P.fst n).hom ((relativeToPool P n).hom a) := by
  have h := absolute_pool_comparison P.fst n ((relativeToPool P n).hom a)
  have he : cohomologyEquiv P.fst n ((relativeToPool P n).hom a) =
      (P.singularCohomologyπ coeff (ZMod 2) coeff n).hom a :=
    (cohomologyEquiv P.fst n).apply_symm_apply _
  rw [he] at h
  exact (fromRelative_native P n a).symm.trans h

/-- The native relative pairing transported to the actual dual of relative
homology. This is an operation, not an extra hypothesis about dual classes. -/
def cupDual (P : TopPair.{0}) (p q : ℕ) (a : cohomologyZMod2 P.fst p)
    (φ : RelativeDual.relative (ZMod 2) P q) : RelativeDual.relative (ZMod 2) P (p + q) :=
  equiv P (p + q) (RelativeCup.cup P p q a ((equiv P q).symm φ))

theorem cupDual_comparison (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (b : RelativeCup.cohomology P q) :
    cupDual P p q a (equiv P q b) = equiv P (p + q) (RelativeCup.cup P p q a b) := by
  unfold cupDual
  rw [LinearEquiv.symm_apply_apply]

theorem cupDual_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (a : cohomologyZMod2 Q.fst p) (φ : RelativeDual.relative (ZMod 2) Q q) :
    (cupDual Q p q a φ).comp (P.singularHomologyMap f coeff (p + q)).hom =
      cupDual P p q ((cohPullback (TopPair.Hom.fst f) p).hom a)
        (φ.comp (P.singularHomologyMap f coeff q).hom) := by
  have h := equiv_natural f (p + q) (RelativeCup.cup Q p q a ((equiv Q q).symm φ))
  have hc := RelativeCup.naturality f p q a ((equiv Q q).symm φ)
  exact h.symm.trans (congrArg (equiv P (p + q))
    (hc.trans (congrArg (RelativeCup.cup P p q ((cohPullback (TopPair.Hom.fst f) p).hom a))
      (equiv_inv_natural f q φ))))

theorem cupDual_add_left (P : TopPair.{0}) (p q : ℕ)
    (a a' : cohomologyZMod2 P.fst p) (φ : RelativeDual.relative (ZMod 2) P q) :
    cupDual P p q (a + a') φ = cupDual P p q a φ + cupDual P p q a' φ := by
  unfold cupDual
  rw [RelativeCup.add_left, map_add]

theorem cupDual_add_right (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (φ φ' : RelativeDual.relative (ZMod 2) P q) :
    cupDual P p q a (φ + φ') = cupDual P p q a φ + cupDual P p q a φ' := by
  unfold cupDual
  rw [map_add, RelativeCup.add_right, map_add]

theorem cupDual_smul_left (P : TopPair.{0}) (p q : ℕ) (r : ZMod 2)
    (a : cohomologyZMod2 P.fst p) (φ : RelativeDual.relative (ZMod 2) P q) :
    cupDual P p q (r • a) φ = r • cupDual P p q a φ := by
  unfold cupDual
  rw [RelativeCup.smul_left, map_smul]

theorem cupDual_smul_right (P : TopPair.{0}) (p q : ℕ) (r : ZMod 2)
    (a : cohomologyZMod2 P.fst p) (φ : RelativeDual.relative (ZMod 2) P q) :
    cupDual P p q a (r • φ) = r • cupDual P p q a φ := by
  unfold cupDual
  rw [map_smul, RelativeCup.smul_right, map_smul]

theorem cupDual_zero_left (P : TopPair.{0}) (p q : ℕ)
    (φ : RelativeDual.relative (ZMod 2) P q) : cupDual P p q 0 φ = 0 := by
  unfold cupDual
  rw [RelativeCup.zero_left, map_zero]

theorem cupDual_zero_right (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) : cupDual P p q a 0 = 0 := by
  unfold cupDual
  rw [map_zero, RelativeCup.zero_right, map_zero]

theorem cupDual_fromRelative (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (φ : RelativeDual.relative (ZMod 2) P q) :
    RelativeDual.fromRelative (ZMod 2) P (p + q) (cupDual P p q a φ) =
      (kroneckerMap P.fst (p + q)).hom
        (cupZMod2 a ((relativeToPool P q).hom ((equiv P q).symm φ))) := by
  have h := fromRelative_comparison P (p + q) (RelativeCup.cup P p q a ((equiv P q).symm φ))
  rw [RelativeCup.relativeToPool_cup] at h
  have he := equiv_apply P (p + q) (RelativeCup.cup P p q a ((equiv P q).symm φ))
  exact (congrArg (RelativeDual.fromRelative (ZMod 2) P (p + q)) he).trans h

theorem cupDual_classOf (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (ψ : RelativeCupCochain.relative P q) (hψ : RelativeCupCochain.differential P q ψ = 0)
    (z : (chains P).cycles (p + q)) :
    cupDual P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)
        (comparison P q (CochainClass.classOf (RelativeCup.cx P) q ψ hψ))
        (((chains P).homologyπ (p + q)).hom z) =
      (RelativeCupCochain.cup P p q φ ψ).hom (((chains P).iCycles (p + q)).hom z) := by
  have hψe := equiv_apply P q (CochainClass.classOf (RelativeCup.cx P) q ψ hψ)
  have hcp := cupDual_comparison P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)
    (CochainClass.classOf (RelativeCup.cx P) q ψ hψ)
  have hc := RelativeCup.cup_mk P p q φ hφ ψ hψ
  have hh := RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ
  have he := equiv_apply P (p + q)
    (CochainClass.classOf (RelativeCup.cx P) (p + q) (RelativeCupCochain.cup P p q φ ψ) hh)
  have heq := (congrArg (cupDual P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)) hψe).symm.trans
    (hcp.trans ((congrArg (equiv P (p + q)) hc).trans he))
  exact (congrArg (fun g => g (((chains P).homologyπ (p + q)).hom z)) heq).trans
    (comparison_classOf P (p + q) (RelativeCupCochain.cup P p q φ ψ) hh z)

end

end Finsler.RelativeKronecker
