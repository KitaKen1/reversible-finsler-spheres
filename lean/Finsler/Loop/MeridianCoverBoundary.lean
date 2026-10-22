module

public import Finsler.Loop.MeridianIntersectionMaps
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! The actual cover-prism boundary is the difference of the fixed
and varying intersection maps. The Mayer–Vietoris sequence is the
existing TauCeti singular short exact sequence. -/
@[expose] public section
namespace Finsler.MeridianCoverBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.MeridianQuarterHomotopies
open Finsler.MeridianIntersectionMaps Finsler.MeridianCoverPrisms
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

abbrev square {n : ℕ} (P : Sphere n) :=
  TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (upper P) (lower P)
abbrev sequence {n : ℕ} (P : Sphere n) :=
  ((square P).map ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff)).shortComplex

theorem shortExact {n : ℕ} (P : Sphere n) : (sequence P).ShortExact := by
  have : Mono (intoUpper P) := (TopCat.mono_iff_injective _).mpr
    (Set.inclusion_injective Set.inter_subset_left)
  have : Mono (TopCat.toSSet.map (intoUpper P)) := Functor.map_mono _ _
  exact SSet.shortExact_mayerVietorisShortComplex
    (t := TopCat.toSSet.map (intoUpper P)) coeff (square P)

def intersectionChain {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  (chains (parameters P)).iCycles q ≫ ((push (fixed P v₀)).f q - (push (varying P)).f q)
def intersectionCycles {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  HomologicalComplex.cyclesMap (push (fixed P v₀)) q -
    HomologicalComplex.cyclesMap (push (varying P)) q

theorem intersectionCycles_i {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    intersectionCycles P v₀ q ≫ (sequence P).X₁.iCycles q = intersectionChain P v₀ q := by
  dsimp only [intersectionCycles, intersectionChain]
  change _ ≫ (chains (TopCat.of ↥(upper P ∩ lower P))).iCycles q = _
  rw [Preadditive.sub_comp, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, Preadditive.comp_sub]

def liftChain {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    (chains (parameters P)).cycles q ⟶ (sequence P).X₂.X (q + 1) :=
  ((chains (parameters P)).iCycles q ≫ upperChain P v₀ q) ≫
    (biprod.inl : chains (TopCat.of (upper P)) ⟶ _).f (q + 1) +
  ((chains (parameters P)).iCycles q ≫ lowerChain P v₀ q) ≫
    (biprod.inr : chains (TopCat.of (lower P)) ⟶ _).f (q + 1)

theorem boundary_upper {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    ((chains (parameters P)).iCycles q ≫ upperChain P v₀ q) ≫ (chains (TopCat.of (upper P))).d (q + 1) q =
      intersectionChain P v₀ q ≫ (push (intoUpper P)).f q := by
  rw [upper_boundary, upper_fixed, upper_varying, push_comp, push_comp]
  simp only [HomologicalComplex.comp_f, intersectionChain, Preadditive.sub_comp, Category.assoc]

theorem boundary_lower {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    ((chains (parameters P)).iCycles q ≫ lowerChain P v₀ q) ≫ (chains (TopCat.of (lower P))).d (q + 1) q =
      -(intersectionChain P v₀ q ≫ (push (intoLower P)).f q) := by
  rw [lower_boundary, lower_varying, lower_fixed, push_comp, push_comp]
  simp only [HomologicalComplex.comp_f, intersectionChain, Preadditive.sub_comp,
    Preadditive.comp_sub, Category.assoc]
  abel

theorem lift_boundary {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    intersectionChain P v₀ q ≫ (sequence P).f.f q =
      liftChain P v₀ q ≫ (sequence P).X₂.d (q + 1) q := by
  change _ ≫ (biprod.lift (push (intoUpper P)) (-push (intoLower P))).f q =
    liftChain P v₀ q ≫ (chains (TopCat.of (upper P)) ⊞ chains (TopCat.of (lower P))).d (q + 1) q
  apply HomologicalComplex.biprodX_ext_to
  · change _ ≫ (biprod.lift (push (intoUpper P)) (-push (intoLower P))).f q ≫ _ = _
    rw [HomologicalComplex.biprod_lift_fst_f]
    simp only [liftChain, Preadditive.add_comp, Category.assoc,
      ← HomologicalComplex.Hom.comm, HomologicalComplex.biprod_inl_fst_f_assoc,
      HomologicalComplex.biprod_inr_fst_f_assoc, zero_comp, comp_zero, add_zero]
    simpa only [Category.assoc] using (boundary_upper P v₀ q).symm
  · change _ ≫ (biprod.lift (push (intoUpper P)) (-push (intoLower P))).f q ≫ _ = _
    rw [HomologicalComplex.biprod_lift_snd_f]
    simp only [liftChain, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
      Preadditive.add_comp, Category.assoc, ← HomologicalComplex.Hom.comm,
      HomologicalComplex.biprod_inl_snd_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
      zero_comp, comp_zero, zero_add]
    simpa only [Category.assoc] using (boundary_lower P v₀ q).symm

def coverChain {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  liftChain P v₀ q ≫ (sequence P).g.f (q + 1)

theorem cover_closed {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    coverChain P v₀ q ≫ (sequence P).X₃.d (q + 1) q = 0 := by
  rw [coverChain, Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc,
    ← lift_boundary, Category.assoc, ← HomologicalComplex.comp_f, (sequence P).zero,
    HomologicalComplex.zero_f, comp_zero]

def coverCycles {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :=
  (sequence P).X₃.liftCycles (coverChain P v₀ q) q (by simp) (cover_closed P v₀ q)

theorem connecting_cycles {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ) :
    coverCycles P v₀ q ≫ (sequence P).X₃.homologyπ (q + 1) ≫
      (shortExact P).δ (q + 1) q (by rfl) =
        intersectionCycles P v₀ q ≫ (sequence P).X₁.homologyπ q := by
  have h := (shortExact P).δ_eq (q + 1) q (by rfl)
    (coverChain P v₀ q) (cover_closed P v₀ q) (liftChain P v₀ q) rfl
    (intersectionChain P v₀ q) (lift_boundary P v₀ q) ((ComplexShape.down ℕ).next q) rfl
  refine h.trans ?_
  congr 1
  apply (cancel_mono ((sequence P).X₁.iCycles q)).mp
  rw [HomologicalComplex.liftCycles_i, intersectionCycles_i]

end
end Finsler.MeridianCoverBoundary
