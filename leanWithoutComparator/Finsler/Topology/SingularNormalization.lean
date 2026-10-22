module

public import Finsler.Topology.SupportedCapNaturality
public import Finsler.Topology.CochainClassExact
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-! Actual singular cochain normalization via the existing Dold-Kan
projector. Naturality preserves vanishing on every actual subspace. -/

@[expose] public section
namespace Finsler.SingularNormalization

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def linearization (X : TopCat.{0}) : SimplicialObject (ModuleCat.{0} (ZMod 2)) :=
  TopCat.toSSet.obj X ⋙ sigmaConst.obj coeff

def linearMap {X Y : TopCat.{0}} (f : X ⟶ Y) : linearization X ⟶ linearization Y :=
  Functor.whiskerRight (TopCat.toSSet.map f) (sigmaConst.obj coeff)

def projector (X : TopCat.{0}) : chains X ⟶ chains X :=
  DoldKan.PInfty (X := linearization X)

def projectorHomotopy (X : TopCat.{0}) : Homotopy (projector X) (𝟙 (chains X)) :=
  DoldKan.homotopyPInftyToId (linearization X)

theorem projector_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SupportedCapNaturality.push f).f n ≫ (projector Y).f n =
      (projector X).f n ≫ (SupportedCapNaturality.push f).f n :=
  DoldKan.PInfty_f_naturality n (linearMap f)

def normalize (X : TopCat.{0}) (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n) :
    singularCochainGroup (ZMod 2) X n := (projector X).f n ≫ φ

theorem normalize_zero (X : TopCat.{0}) (n : ℕ) : normalize X n 0 = 0 := comp_zero

theorem normalize_coboundary (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) :
    cochainCoboundary (ZMod 2) X n (normalize X n φ) =
      normalize X (n + 1) (cochainCoboundary (ZMod 2) X n φ) := by
  change (chains X).d (n + 1) n ≫ ((projector X).f n ≫ φ) =
    (projector X).f (n + 1) ≫ ((chains X).d (n + 1) n ≫ φ)
  rw [← Category.assoc, ← (projector X).comm, Category.assoc]

theorem normalize_closed (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    cochainCoboundary (ZMod 2) X n (normalize X n φ) = 0 := by
  rw [normalize_coboundary, hφ, normalize_zero]

theorem normalize_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback f n (normalize Y n φ) = normalize X n (cochainPullback f n φ) := by
  change (SupportedCapNaturality.push f).f n ≫ ((projector Y).f n ≫ φ) =
    (projector X).f n ≫ ((SupportedCapNaturality.push f).f n ≫ φ)
  rw [← Category.assoc, projector_natural, Category.assoc]

theorem normalize_supported {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hf : cochainPullback f n φ = 0) :
    cochainPullback f n (normalize Y n φ) = 0 := by
  rw [normalize_natural, hf, normalize_zero]

theorem normalize_degeneracies (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) :
    DoldKan.DegeneraciesVanish (X := linearization X) (normalize X n φ) :=
  (DoldKan.degeneraciesVanishPInfty_f (X := linearization X) n).comp φ

def primitive (X : TopCat.{0}) (n : ℕ) (φ : singularCochainGroup (ZMod 2) X (n + 1)) :
    singularCochainGroup (ZMod 2) X n := (projectorHomotopy X).hom n (n + 1) ≫ φ

theorem primitive_boundary (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X (n + 1))
    (hφ : cochainCoboundary (ZMod 2) X (n + 1) φ = 0) :
    cochainCoboundary (ZMod 2) X n (primitive X n φ) = normalize X (n + 1) φ - φ := by
  have h := congrArg (fun f : (chains X).X (n + 1) ⟶ (chains X).X (n + 1) => f ≫ φ)
    ((projectorHomotopy X).comm (n + 1))
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have hc : (chains X).d (n + 2) (n + 1) ≫ φ = 0 := hφ
  simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.id_f,
    hc, comp_zero, add_zero, Category.id_comp] at h
  have h' : normalize X (n + 1) φ =
      cochainCoboundary (ZMod 2) X n (primitive X n φ) + φ := h
  exact (eq_sub_iff_add_eq).mpr h'.symm

theorem normalize_class (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X (n + 1))
    (hφ : cochainCoboundary (ZMod 2) X (n + 1) φ = 0) :
    CochainClass.classOf (cochainCxZMod2 X) (n + 1) (normalize X (n + 1) φ)
      (normalize_closed X (n + 1) φ hφ) =
        CochainClass.classOf (cochainCxZMod2 X) (n + 1) φ hφ :=
  RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 X) n (n + 1)
    (primitive X n φ) (normalize X (n + 1) φ) φ
    (normalize_closed X (n + 1) φ hφ) hφ (primitive_boundary X n φ hφ).symm

theorem normalize_class_pos (X : TopCat.{0}) (n : ℕ) (hn : 1 ≤ n)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    CochainClass.classOf (cochainCxZMod2 X) n (normalize X n φ)
      (normalize_closed X n φ hφ) = CochainClass.classOf (cochainCxZMod2 X) n φ hφ := by
  cases n with
  | zero => omega
  | succ n => exact normalize_class X n φ hφ

end
end Finsler.SingularNormalization
