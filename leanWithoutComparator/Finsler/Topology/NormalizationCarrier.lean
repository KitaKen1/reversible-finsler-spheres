module

public import Finsler.Topology.SingularNormalization

/-! The actual normalization projector and its chain homotopy preserve
every singular carrier, in particular each original parent-simplex image. -/

@[expose] public section
namespace Finsler.NormalizationCarrier

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial DoldKan

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def linearization (S : SSet.{0}) : SimplicialObject (ModuleCat.{0} (ZMod 2)) :=
  S ⋙ sigmaConst.obj coeff

def linearMap {S T : SSet.{0}} (f : S ⟶ T) : linearization S ⟶ linearization T :=
  Functor.whiskerRight f (sigmaConst.obj coeff)

def projector (S : SSet.{0}) : S.chainComplex coeff ⟶ S.chainComplex coeff :=
  DoldKan.PInfty (X := linearization S)

def homotopy (S : SSet.{0}) : Homotopy (projector S) (𝟙 (S.chainComplex coeff)) :=
  DoldKan.homotopyPInftyToId (linearization S)

theorem projector_natural {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) :
    (SSet.chainComplexMap f coeff).f n ≫ (projector T).f n =
      (projector S).f n ≫ (SSet.chainComplexMap f coeff).f n :=
  DoldKan.PInfty_f_naturality n (linearMap f)

theorem finite_homotopy_natural {X Y : SimplicialObject (ModuleCat.{0} (ZMod 2))}
    (f : X ⟶ Y) (q n m : ℕ) :
    f.app (Opposite.op ⦋n⦌) ≫ (DoldKan.homotopyPToId Y q).hom n m =
      (DoldKan.homotopyPToId X q).hom n m ≫ f.app (Opposite.op ⦋m⦌) := by
  induction q with
  | zero => simp [DoldKan.homotopyPToId]
  | succ q ih =>
    simp only [DoldKan.homotopyPToId, Homotopy.trans_hom, Homotopy.ofEq_hom,
      Homotopy.add_hom, Homotopy.compLeft_hom, DoldKan.homotopyHσToZero,
      Homotopy.nullHomotopy'_hom, Pi.zero_apply, add_zero, zero_add]
    rw [Preadditive.comp_add, Preadditive.add_comp, ih,
      ← Category.assoc, DoldKan.P_f_naturality, Category.assoc]
    by_cases hmn : (ComplexShape.down ℕ).Rel m n
    · simp only [dif_pos hmn]
      rw [DoldKan.hσ'_naturality, ← Category.assoc]
    · simp only [dif_neg hmn, comp_zero, zero_comp]

theorem homotopy_natural {S T : SSet.{0}} (f : S ⟶ T) (n m : ℕ) :
    (SSet.chainComplexMap f coeff).f n ≫ (homotopy T).hom n m =
      (homotopy S).hom n m ≫ (SSet.chainComplexMap f coeff).f m :=
  finite_homotopy_natural (linearMap f) (m + 1) n m

theorem projector_preserves {X : TopCat.{0}} {ι : Type} (V : ι → Set X) {n : ℕ}
    {f : coeff ⟶ (chains X).X n} (hf : f ∈ supported X V n) :
    f ≫ (SingularNormalization.projector X).f n ∈ supported X V n := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hf
  apply (TauCeti.mem_smallSingularChains_iff _).mpr
  refine ⟨g ≫ (projector (X.smallSingularSubcomplex V : SSet)).f n, ?_⟩
  have he : (SSet.chainComplexMap (X.smallSingularSubcomplex V).ι coeff).f n ≫
      (SingularNormalization.projector X).f n =
    (projector (X.smallSingularSubcomplex V : SSet)).f n ≫
      (SSet.chainComplexMap (X.smallSingularSubcomplex V).ι coeff).f n :=
    projector_natural (X.smallSingularSubcomplex V).ι n
  simpa only [Category.assoc] using congrArg (fun h => g ≫ h) he.symm

theorem homotopy_preserves {X : TopCat.{0}} {ι : Type} (V : ι → Set X) {n m : ℕ}
    {f : coeff ⟶ (chains X).X n} (hf : f ∈ supported X V n) :
    f ≫ (SingularNormalization.projectorHomotopy X).hom n m ∈ supported X V m := by
  obtain ⟨g, rfl⟩ := (TauCeti.mem_smallSingularChains_iff _).mp hf
  apply (TauCeti.mem_smallSingularChains_iff _).mpr
  refine ⟨g ≫ (homotopy (X.smallSingularSubcomplex V : SSet)).hom n m, ?_⟩
  have he : (SSet.chainComplexMap (X.smallSingularSubcomplex V).ι coeff).f n ≫
      (SingularNormalization.projectorHomotopy X).hom n m =
    (homotopy (X.smallSingularSubcomplex V : SSet)).hom n m ≫
      (SSet.chainComplexMap (X.smallSingularSubcomplex V).ι coeff).f m :=
    homotopy_natural (X.smallSingularSubcomplex V).ι n m
  simpa only [Category.assoc] using congrArg (fun h => g ≫ h) he.symm

theorem primitive_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : SphereOddDegree.singularCochainGroup (ZMod 2) Y (n + 1)) :
    SphereOddDegree.cochainPullback f n (SingularNormalization.primitive Y n φ) =
      SingularNormalization.primitive X n (SphereOddDegree.cochainPullback f (n + 1) φ) := by
  have he : (SupportedCapNaturality.push f).f n ≫
      (SingularNormalization.projectorHomotopy Y).hom n (n + 1) =
    (SingularNormalization.projectorHomotopy X).hom n (n + 1) ≫
      (SupportedCapNaturality.push f).f (n + 1) :=
    homotopy_natural (TopCat.toSSet.map f) n (n + 1)
  change (SupportedCapNaturality.push f).f n ≫
      ((SingularNormalization.projectorHomotopy Y).hom n (n + 1) ≫ φ) =
    (SingularNormalization.projectorHomotopy X).hom n (n + 1) ≫
      ((SupportedCapNaturality.push f).f (n + 1) ≫ φ)
  rw [← Category.assoc, he, Category.assoc]

theorem primitive_supported {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : SphereOddDegree.singularCochainGroup (ZMod 2) Y (n + 1))
    (hf : SphereOddDegree.cochainPullback f (n + 1) φ = 0) :
    SphereOddDegree.cochainPullback f n (SingularNormalization.primitive Y n φ) = 0 := by
  rw [primitive_natural, hf]
  change (SingularNormalization.projectorHomotopy X).hom n (n + 1) ≫ 0 = 0
  exact comp_zero

end
end Finsler.NormalizationCarrier
