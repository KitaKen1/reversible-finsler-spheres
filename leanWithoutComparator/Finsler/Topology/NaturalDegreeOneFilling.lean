module

public import Finsler.Topology.TripleTimeModelFilling

/-! Construct a natural degree-two filling for a natural closed
degree-one family on simplicial tensor chains. The induction uses the
actual three-factor standard cone and natural classifying-map extension.
On every source cycle the degree-one family is its explicit boundary.
Instantiating the actual two time-prism models remains separate. -/

@[expose] public section
namespace Finsler.NaturalDegreeOneFilling

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SSet
open Finsler.CochainComparison Finsler.TripleTimeModelExtension
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev source (K L : SSet.{0}) := K.chainComplex coeff ⊗ L.chainComplex coeff
abbrev output (K L : SSet.{0}) := (target K L).chainComplex coeff

variable (θ : ∀ n : ℕ, ∀ K L : SSet.{0}, (source K L).X n ⟶ (output K L).X (n + 1))

def doublePrism (n : ℕ) : (K L : SSet.{0}) → ((source K L).X n ⟶ (output K L).X (n + 2)) :=
  Nat.rec (motive := fun n => (K L : SSet.{0}) → ((source K L).X n ⟶ (output K L).X (n + 2)))
    (TripleTimeModelFilling.filling (θ 0))
    (fun n previous => TripleTimeModelFilling.filling
      (fun K L => θ (n + 1) K L + (source K L).d (n + 1) n ≫ previous K L)) n

def residual (n : ℕ) (K L : SSet.{0}) : (source K L).X (n + 1) ⟶ (output K L).X (n + 2) :=
  θ (n + 1) K L + (source K L).d (n + 1) n ≫ doublePrism θ n K L

theorem naturality (n : ℕ) {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f n ≫ doublePrism θ n K' L' =
      doublePrism θ n K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (n + 2) := by
  cases n with
  | zero => exact TripleTimeModelFilling.naturality (θ 0) f g
  | succ n => exact TripleTimeModelFilling.naturality (residual θ n) f g

variable
  (hθ : ∀ n : ℕ, ∀ ⦃K K' L L' : SSet.{0}⦄ (f : K ⟶ K') (g : L ⟶ L'),
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f n ≫ θ n K' L' =
      θ n K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (n + 1))
  (hzero : ∀ K L : SSet.{0}, θ 0 K L ≫ (output K L).d 1 0 = 0)
  (hcomm : ∀ n : ℕ, ∀ K L : SSet.{0}, θ (n + 1) K L ≫ (output K L).d (n + 2) (n + 1) =
    -((source K L).d (n + 1) n ≫ θ n K L))

include hθ in
theorem residual_naturality (n : ℕ) {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).f (n + 1) ≫ residual θ n K' L' =
      residual θ n K L ≫ (SSet.chainComplexMap (f ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ g)) coeff).f (n + 2) := by
  simp only [residual, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  rw [hθ (n + 1)]
  congr 1
  rw [← Category.assoc, (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff).comm,
    Category.assoc, naturality]

include hθ hzero in
theorem boundary_zero (K L : SSet.{0}) :
    doublePrism θ 0 K L ≫ (output K L).d 2 1 = θ 0 K L :=
  TripleTimeModelFilling.boundary (θ 0) hzero (hθ 0) K L

include hcomm in
theorem residual_closed (n : ℕ) (K L : SSet.{0})
    (hweak : (source K L).d (n + 1) n ≫ doublePrism θ n K L ≫
      (output K L).d (n + 2) (n + 1) = (source K L).d (n + 1) n ≫ θ n K L) :
    residual θ n K L ≫ (output K L).d (n + 2) (n + 1) = 0 := by
  simp only [residual, Preadditive.add_comp, Category.assoc]
  rw [hcomm, hweak, neg_add_cancel]

include hθ hzero hcomm in
theorem d_doublePrism_d (n : ℕ) (K L : SSet.{0}) :
    (source K L).d (n + 1) n ≫ doublePrism θ n K L ≫ (output K L).d (n + 2) (n + 1) =
      (source K L).d (n + 1) n ≫ θ n K L := by
  induction n generalizing K L with
  | zero => rw [boundary_zero θ hθ hzero]
  | succ n ih =>
    have hc := fun K L => residual_closed θ hcomm n K L (ih K L)
    have hb : doublePrism θ (n + 1) K L ≫ (output K L).d (n + 3) (n + 2) = residual θ n K L :=
      TripleTimeModelFilling.boundary (residual θ n) hc (fun {K K' L L'} f g => residual_naturality θ hθ n f g) K L
    rw [hb]
    simp only [residual, Preadditive.comp_add, Category.assoc,
      HomologicalComplex.d_comp_d_assoc, zero_comp, add_zero]

include hθ hzero hcomm in
theorem boundary_succ (n : ℕ) (K L : SSet.{0}) :
    doublePrism θ (n + 1) K L ≫ (output K L).d (n + 3) (n + 2) =
      θ (n + 1) K L + (source K L).d (n + 1) n ≫ doublePrism θ n K L :=
  TripleTimeModelFilling.boundary (residual θ n)
    (fun K L => residual_closed θ hcomm n K L (d_doublePrism_d θ hθ hzero hcomm n K L))
    (fun {K K' L L'} f g => residual_naturality θ hθ n f g) K L

include hθ hzero hcomm in
theorem cycle_boundary (n : ℕ) (K L : SSet.{0}) :
    (source K L).iCycles n ≫ θ n K L =
      ((source K L).iCycles n ≫ doublePrism θ n K L) ≫ (output K L).d (n + 2) (n + 1) := by
  cases n with
  | zero =>
    rw [← boundary_zero θ hθ hzero]
    simp only [Category.assoc]
  | succ n =>
    have hh := congrArg (fun f => (source K L).iCycles (n + 1) ≫ f)
      (boundary_succ θ hθ hzero hcomm n K L)
    simp only [Preadditive.comp_add, ← Category.assoc, HomologicalComplex.iCycles_d,
      zero_comp, add_zero] at hh
    exact hh.symm

end
end Finsler.NaturalDegreeOneFilling
