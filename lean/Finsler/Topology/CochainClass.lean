module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ConcreteCategory

/-! Small representative APIs for an arbitrary module-valued cochain complex.
All classes use mathlib's actual homology object and cokernel map. -/

@[expose] public section

namespace Finsler.CochainClass

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {R : Type} [Ring R] (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem next_eq (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 :=
  (ComplexShape.up ℕ).next_eq' rfl

def classOf (n : ℕ) (φ : C.X n) (hφ : (C.d n (n + 1)).hom φ = 0) : C.homology n :=
  (C.homologyπ n).hom (C.cyclesMk φ (n + 1) (next_eq n) hφ)

theorem closed_iCycles (n : ℕ) (c : C.cycles n) :
    (C.d n (n + 1)).hom ((C.iCycles n).hom c) = 0 :=
  ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) c

theorem cyclesMk_iCycles (n : ℕ) (c : C.cycles n) :
    C.cyclesMk ((C.iCycles n).hom c) (n + 1) (next_eq n) (closed_iCycles C n c) = c := by
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  exact C.i_cyclesMk _ _ _ _

theorem classOf_iCycles (n : ℕ) (c : C.cycles n) :
    classOf C n ((C.iCycles n).hom c) (closed_iCycles C n c) = (C.homologyπ n).hom c := by
  unfold classOf
  rw [cyclesMk_iCycles]

theorem classOf_congr (n : ℕ) {φ ψ : C.X n} (h : φ = ψ)
    (hφ : (C.d n (n + 1)).hom φ = 0) (hψ : (C.d n (n + 1)).hom ψ = 0) :
    classOf C n φ hφ = classOf C n ψ hψ := by
  subst ψ
  rfl

theorem classOf_zero (n : ℕ) (h0 : (C.d n (n + 1)).hom (0 : C.X n) = 0) :
    classOf C n 0 h0 = 0 := by
  have h := classOf_iCycles C n (0 : C.cycles n)
  simpa only [map_zero] using h

theorem classOf_boundary (i n : ℕ) (η : C.X i)
    (h : (C.d n (n + 1)).hom ((C.d i n).hom η) = 0) :
    classOf C n ((C.d i n).hom η) h = 0 := by
  have hc : C.cyclesMk ((C.d i n).hom η) (n + 1) (next_eq n) h = (C.toCycles i n).hom η := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    exact (C.i_cyclesMk _ _ _ _).trans
      (ConcreteCategory.congr_hom (C.toCycles_i i n) η).symm
  unfold classOf
  rw [hc]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ i n) η

theorem closed_boundary (i n : ℕ) (η : C.X i) :
    (C.d n (n + 1)).hom ((C.d i n).hom η) = 0 :=
  ConcreteCategory.congr_hom (C.d_comp_d i n (n + 1)) η

def cast {m n : ℕ} (h : m = n) (φ : C.X m) : C.X n := h ▸ φ

theorem classOf_cast_boundary {i n : ℕ} (h : i + 1 = n) (η : C.X i)
    (hc : (C.d n (n + 1)).hom (cast C h ((C.d i (i + 1)).hom η)) = 0) :
    classOf C n (cast C h ((C.d i (i + 1)).hom η)) hc = 0 := by
  subst n
  exact classOf_boundary C i (i + 1) η hc

theorem classOf_liftCycles {A : ModuleCat.{0} R} (n : ℕ) (f : A ⟶ C.X n)
    (hf : f ≫ C.d n (n + 1) = 0) (a : A) :
    (C.homologyπ n).hom ((C.liftCycles f (n + 1) (next_eq n) hf).hom a) =
      classOf C n (f.hom a) (ConcreteCategory.congr_hom hf a) := by
  unfold classOf
  congr 1
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  exact (ConcreteCategory.congr_hom (C.liftCycles_i f (n + 1) (next_eq n) hf) a).trans
    (C.i_cyclesMk _ _ _ _).symm

def cycleRepr (n : ℕ) (a : C.homology n) : C.cycles n :=
  Function.surjInv ((ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance) a

def representative (n : ℕ) (a : C.homology n) : C.X n := (C.iCycles n).hom (cycleRepr C n a)

theorem representative_closed (n : ℕ) (a : C.homology n) :
    (C.d n (n + 1)).hom (representative C n a) = 0 :=
  closed_iCycles C n (cycleRepr C n a)

theorem classOf_representative (n : ℕ) (a : C.homology n) :
    classOf C n (representative C n a) (representative_closed C n a) = a := by
  change classOf C n ((C.iCycles n).hom (cycleRepr C n a)) _ = a
  rw [classOf_iCycles]
  exact Function.surjInv_eq
    ((ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance) a

def descend {A : ModuleCat.{0} R} (n : ℕ) (f : C.cycles n ⟶ A)
    (hf : C.toCycles ((ComplexShape.up ℕ).prev n) n ≫ f = 0) : C.homology n ⟶ A :=
  (C.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc (CokernelCofork.ofπ f hf)

theorem homologyπ_descend {A : ModuleCat.{0} R} (n : ℕ) (f : C.cycles n ⟶ A)
    (hf : C.toCycles ((ComplexShape.up ℕ).prev n) n ≫ f = 0) :
    C.homologyπ n ≫ descend C n f hf = f :=
  (C.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac
    (CokernelCofork.ofπ f hf) WalkingParallelPair.one

theorem descend_classOf {A : ModuleCat.{0} R} (n : ℕ) (f : C.cycles n ⟶ A)
    (hf : C.toCycles ((ComplexShape.up ℕ).prev n) n ≫ f = 0)
    (φ : C.X n) (hφ : (C.d n (n + 1)).hom φ = 0) :
    (descend C n f hf).hom (classOf C n φ hφ) =
      f.hom (C.cyclesMk φ (n + 1) (next_eq n) hφ) := by
  unfold classOf
  exact ConcreteCategory.congr_hom (homologyπ_descend C n f hf) _

theorem classOf_map {D : CochainComplex (ModuleCat.{0} R) ℕ} (f : C ⟶ D) (n : ℕ)
    (φ : C.X n) (hφ : (C.d n (n + 1)).hom φ = 0)
    (hfφ : (D.d n (n + 1)).hom ((f.f n).hom φ) = 0) :
    (HomologicalComplex.homologyMap f n).hom (classOf C n φ hφ) =
      classOf D n ((f.f n).hom φ) hfφ := by
  unfold classOf
  change (C.homologyπ n ≫ HomologicalComplex.homologyMap f n).hom _ = _
  rw [HomologicalComplex.homologyπ_naturality]
  change (D.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom _) = _
  congr 1
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  calc
    (D.iCycles n).hom ((HomologicalComplex.cyclesMap f n).hom _) =
        (f.f n).hom ((C.iCycles n).hom _) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) _
    _ = (f.f n).hom φ := congrArg (f.f n).hom (C.i_cyclesMk _ _ _ _)
    _ = (D.iCycles n).hom (D.cyclesMk _ _ _ hfφ) := (D.i_cyclesMk _ _ _ _).symm

theorem closed_map {D : CochainComplex (ModuleCat.{0} R) ℕ} (f : C ⟶ D) (n : ℕ)
    (φ : C.X n) (hφ : (C.d n (n + 1)).hom φ = 0) :
    (D.d n (n + 1)).hom ((f.f n).hom φ) = 0 := by
  have h := ConcreteCategory.congr_hom (f.comm n (n + 1)) φ
  change _ = (f.f (n + 1)).hom ((C.d n (n + 1)).hom φ) at h
  rw [hφ, map_zero] at h
  exact h

end

end Finsler.CochainClass
