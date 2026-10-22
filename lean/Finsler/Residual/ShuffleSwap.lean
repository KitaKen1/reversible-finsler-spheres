module

public import TauCeti.AlgebraicTopology.SimplicialSet.Shuffle
import all TauCeti.AlgebraicTopology.SimplicialSet.Shuffle
public import TauCeti.Algebra.Homology.Monoidal.KoszulBraiding
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Finsler.Topology.FilteredBilinearLoopProduct

/-! The shuffle chain is symmetric under the interchange of the two factors, up to the sign
(-1)^(p q) (Claude, UF prototype, step X).

By induction on the recursion of `SSet.shuffleChain`: the cone from (0, 0) commutes with the swap
of Δ[a] ⊗ Δ[b] (`chainComplexMap_f_prodConeChain`), the swap exchanges the two zeroth-face
whiskerings (braiding naturality), and the two terms of the recursion are exchanged with the
right signs. -/

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

@[expose] public section

namespace SSet.ShuffleSwap

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (T : C)

/-- The swap of two standard simplices. -/
abbrev sw (a b : ℕ) : (Δ[a] : SSet.{w}) ⊗ Δ[b] ⟶ (Δ[b] : SSet.{w}) ⊗ Δ[a] := (β_ _ _).hom

theorem sw_prodCone (a b m : ℕ) (x : ((Δ[a] : SSet.{w}) ⊗ Δ[b]) _⦋m⦌) :
    (sw a b).app _ (stdSimplex.prodCone x) = stdSimplex.prodCone ((sw a b).app _ x) := by exact rfl

@[reassoc]
theorem prodConeChain_sw (a b m : ℕ) :
    stdSimplex.prodConeChain a b T m ≫ (chainComplexMap (sw a b) T).f (m + 1) =
      (chainComplexMap (sw a b) T).f m ≫ stdSimplex.prodConeChain b a T m :=
  (stdSimplex.chainComplexMap_f_prodConeChain T (sw a b) (sw_prodCone a b) m).symm

@[reassoc]
theorem whiskerRight_sw {a a' : ℕ} (f : (Δ[a] : SSet.{w}) ⟶ Δ[a']) (b : ℕ) (n : ℕ) :
    (chainComplexMap (f ▷ (Δ[b] : SSet.{w})) T).f n ≫ (chainComplexMap (sw a' b) T).f n =
      (chainComplexMap (sw a b) T).f n ≫ (chainComplexMap ((Δ[b] : SSet.{w}) ◁ f) T).f n := by
  rw [TauCeti.SSet.chainComplexMap_f_comp, TauCeti.SSet.chainComplexMap_f_comp,
    BraidedCategory.braiding_naturality_left]

@[reassoc]
theorem whiskerLeft_sw (a : ℕ) {b b' : ℕ} (g : (Δ[b] : SSet.{w}) ⟶ Δ[b']) (n : ℕ) :
    (chainComplexMap ((Δ[a] : SSet.{w}) ◁ g) T).f n ≫ (chainComplexMap (sw a b') T).f n =
      (chainComplexMap (sw a b) T).f n ≫ (chainComplexMap (g ▷ (Δ[a] : SSet.{w})) T).f n := by
  rw [TauCeti.SSet.chainComplexMap_f_comp, TauCeti.SSet.chainComplexMap_f_comp,
    BraidedCategory.braiding_naturality_right]

/-- A vertex of Δ[0] ⊗ Δ[0]. -/
def v00 : ((Δ[0] : SSet.{w}) ⊗ Δ[0]) _⦋0⦌ := (yonedaEquiv (𝟙 _), yonedaEquiv (𝟙 _))

theorem v00_unique (x : ((Δ[0] : SSet.{w}) ⊗ Δ[0]) _⦋0⦌) : x = v00 :=
  Prod.ext (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)
    (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)

theorem sign_one (p q : ℕ) :
    ((-1 : ℤ) ^ (p + 1)) * (-1) ^ ((p + 1) * q) = (-1) ^ ((p + 1) * (q + 1)) := by
  rw [← pow_add]
  congr 1
  ring

theorem sign_two (p q : ℕ) :
    ((-1 : ℤ) ^ ((p + 1) * (q + 1))) * (-1) ^ (q + 1) = (-1) ^ (p * (q + 1)) := by
  rw [← pow_add]
  have : (p + 1) * (q + 1) + (q + 1) = p * (q + 1) + 2 * (q + 1) := by ring
  rw [this, pow_add, pow_mul]
  norm_num

/-- **Swap symmetry of the shuffle chain.** -/
theorem shuffleChain_sw : ∀ (p q n : ℕ) (h : p + q = n) (h' : q + p = n),
    shuffleChain T p q n h ≫ (chainComplexMap (sw p q) T).f n =
      ((-1 : ℤ) ^ (p * q)) • shuffleChain T q p n h' := fun p q n h h' =>
  match p, q, n, h, h' with
  | 0, 0, 0, h, h' => by
    rw [shuffleChain_zero_zero T h v00, ι_chainComplexMap_f, v00_unique ((sw 0 0).app _ v00)]
    simp
  | p + 1, 0, n + 1, h, h' => by
    rw [shuffleChain_succ_zero, shuffleChain_zero_succ]
    simp only [Category.assoc, prodConeChain_sw, whiskerRight_sw_assoc]
    rw [reassoc_of% (shuffleChain_sw p 0 n (by omega) (by omega))]
    simp
  | 0, q + 1, n + 1, h, h' => by
    rw [shuffleChain_zero_succ, shuffleChain_succ_zero]
    simp only [Category.assoc, prodConeChain_sw, whiskerLeft_sw_assoc]
    rw [reassoc_of% (shuffleChain_sw 0 q n (by omega) (by omega))]
    simp
  | p + 1, q + 1, n + 1, h, h' => by
    rw [shuffleChain_succ_succ, shuffleChain_succ_succ]
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, prodConeChain_sw,
      whiskerRight_sw_assoc, whiskerLeft_sw_assoc]
    rw [reassoc_of% (shuffleChain_sw p (q + 1) n (by omega) (by omega)),
      reassoc_of% (shuffleChain_sw (p + 1) q n (by omega) (by omega))]
    simp only [Preadditive.zsmul_comp, smul_add, smul_smul, sign_one, sign_two]
    exact add_comm _ _
  | 0, 0, _ + 1, h, _ => absurd h (by omega)
  | _ + 1, _, 0, h, _ => absurd h (by omega)
  | 0, _ + 1, 0, h, _ => absurd h (by omega)

end Chain

section Map

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

/-- **Swap symmetry of the shuffle map**: interchanging the simplicial sets and the coefficients
after the shuffle is the Koszul interchange of the tensor factors before it. -/
theorem shuffle_sw :
    shuffle K L R S ≫ chainComplexMap (β_ K L).hom (R ⊗ S) ≫
        ((chainComplexFunctor C).map (β_ R S).hom).app (L ⊗ K) =
      TauCeti.NatChainComplex.koszulBraidingHom (K.chainComplex R) (L.chainComplex S) ≫
        shuffle L K S R := by
  ext n : 1
  refine mapBifunctor.hom_ext fun p q h ↦ SSet.tensorChainComplexX_hom_ext fun x y ↦ ?_
  have hpq : p + q = n := h
  simp only [HomologicalComplex.comp_f, ιChainComplex_tensorHom_ιChainComplex_shuffle_f_assoc,
    TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f_assoc, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc]
  rw [TauCeti.SSet.chainComplexMap_f_comp_assoc, BraidedCategory.braiding_naturality,
    ← TauCeti.SSet.chainComplexMap_f_comp_assoc, reassoc_of% (shuffleChain_sw (R ⊗ S) p q n h (by omega)),
    TauCeti.SSet.chainComplexMap_f_chainComplexFunctor_map_app_f]
  simp only [Preadditive.zsmul_comp]
  rw [shuffleChain_chainComplexFunctor_map_app_f_assoc, BraidedCategory.braiding_naturality_assoc,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f]

end Map

section Singular

open CartesianMonoidalCategory

theorem prodComparison_braid (X Y : TopCat.{w}) :
    CartesianMonoidalCategory.prodComparison TopCat.toSSet X Y ≫ (β_ (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).hom =
      TopCat.toSSet.map (β_ X Y).hom ≫ CartesianMonoidalCategory.prodComparison TopCat.toSSet Y X := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [CartesianMonoidalCategory.prodComparison, ← Functor.map_comp]
  · simp [CartesianMonoidalCategory.prodComparison, ← Functor.map_comp]

theorem mu_braid (X Y : TopCat.{w}) :
    Functor.LaxMonoidal.μ TopCat.toSSet X Y ≫ TopCat.toSSet.map (β_ X Y).hom =
      (β_ (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).hom ≫ Functor.LaxMonoidal.μ TopCat.toSSet Y X := by
  rw [← cancel_mono (CartesianMonoidalCategory.prodComparison TopCat.toSSet Y X), Category.assoc,
    ← prodComparison_braid]
  simp only [← Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, Functor.Monoidal.μ_δ,
    ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, Category.assoc, Functor.Monoidal.μ_δ]
  simp

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- **Swap symmetry of the singular shuffle map.** -/
theorem topShuffle_sw (X Y : TopCat.{w}) (R S : C) :
    TopCat.shuffle X Y R S ≫ chainComplexMap (TopCat.toSSet.map (β_ X Y).hom) (R ⊗ S) ≫
        ((chainComplexFunctor C).map (β_ R S).hom).app (TopCat.toSSet.obj (Y ⊗ X)) =
      TauCeti.NatChainComplex.koszulBraidingHom ((TopCat.toSSet.obj X).chainComplex R)
          ((TopCat.toSSet.obj Y).chainComplex S) ≫ TopCat.shuffle Y X S R := by
  ext n : 1
  have h := congrArg (fun φ => HomologicalComplex.Hom.f φ n)
    (shuffle_sw (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) R S)
  simp only [HomologicalComplex.comp_f] at h
  simp only [TopCat.shuffle_def, HomologicalComplex.comp_f, Category.assoc]
  rw [TauCeti.SSet.chainComplexMap_f_comp_assoc, mu_braid, ← TauCeti.SSet.chainComplexMap_f_comp_assoc,
    TauCeti.SSet.chainComplexMap_f_chainComplexFunctor_map_app_f, reassoc_of% h]

end Singular

section Cycles

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] [B.HasTensor A]
  (p q n : ℕ) (h : p + q = n) (h' : q + p = n)
  [A.HasHomology p] [B.HasHomology q] [(HomologicalComplex.tensorObj A B).HasHomology n]
  [(HomologicalComplex.tensorObj B A).HasHomology n]

/-- **Koszul interchange of cycles.** -/
@[reassoc]
theorem cyclesCross_koszul :
    HomologicalComplex.cyclesCross A B p q n h ≫
        HomologicalComplex.cyclesMap (TauCeti.NatChainComplex.koszulBraidingHom A B) n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (A.cycles p) (B.cycles q)).hom ≫
        HomologicalComplex.cyclesCross B A q p n h') := by
  rw [← cancel_mono ((HomologicalComplex.tensorObj B A).iCycles n)]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i, Preadditive.zsmul_comp,
    HomologicalComplex.cyclesCross_iCycles_assoc, HomologicalComplex.cyclesCross_iCycles,
    TauCeti.NatChainComplex.ιTensorObj_koszulBraidingHom_f, Preadditive.comp_zsmul]
  rw [BraidedCategory.braiding_naturality_assoc]

end Cycles

section Homology

open TopCat

variable (X Y : TopCat.{0}) (R S : ModuleCat.{0} (ZMod 2)) (p q n : ℕ) (h : p + q = n)
  (h' : q + p = n)

noncomputable abbrev CX (Z : TopCat.{0}) (M : ModuleCat.{0} (ZMod 2)) := (toSSet.obj Z).chainComplex M

theorem epi_tensor_homologyπ :
    Epi ((CX X R).homologyπ p ⊗ₘ (CX Y S).homologyπ q) := by
  rw [ModuleCat.epi_iff_surjective]
  have h1 : Function.Surjective ((CX X R).homologyπ p).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have h2 : Function.Surjective ((CX Y S).homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact TensorProduct.map_surjective h1 h2

/-- **Swap symmetry of the homology cross product** (chain complex form). -/
theorem homologyCross_sw :
    homologyCross (CX X R) (CX Y S) p q n h ≫ homologyMap (TopCat.shuffle X Y R S) n ≫
        homologyMap (SSet.chainComplexMap (toSSet.map (β_ X Y).hom) (R ⊗ S)) n ≫
          homologyMap (((SSet.chainComplexFunctor _).map (β_ R S).hom).app (toSSet.obj (Y ⊗ X))) n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ ((CX X R).homology p) ((CX Y S).homology q)).hom ≫
        homologyCross (CX Y S) (CX X R) q p n h' ≫ homologyMap (TopCat.shuffle Y X S R) n) := by
  have := epi_tensor_homologyπ X Y R S p q
  rw [← cancel_epi ((CX X R).homologyπ p ⊗ₘ (CX Y S).homologyπ q)]
  rw [homologyπ_tensorHom_homologyCross_assoc, homologyπ_naturality_assoc,
    homologyπ_naturality_assoc, homologyπ_naturality, ← cyclesMap_comp_assoc, ← cyclesMap_comp_assoc,
    Category.assoc, topShuffle_sw, cyclesMap_comp_assoc, cyclesCross_koszul_assoc _ _ p q n h h']
  rw [Preadditive.comp_zsmul, BraidedCategory.braiding_naturality_assoc,
    homologyπ_tensorHom_homologyCross_assoc, homologyπ_naturality]
  simp only [Preadditive.zsmul_comp, Category.assoc]

/-- **Swap symmetry of the singular homology cross product** (functor form). -/
theorem singularHomologyCross_sw :
    TopCat.singularHomologyCross X Y R S p q n h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) n).obj (R ⊗ S)).map (β_ X Y).hom ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) n).map (β_ R S).hom).app (Y ⊗ X) =
      ((-1 : ℤ) ^ (p * q)) • ((β_ _ _).hom ≫ TopCat.singularHomologyCross Y X S R q p n h') := by
  rw [TopCat.singularHomologyCross_def, TopCat.singularHomologyCross_def]
  exact (Category.assoc _ _ _).trans (homologyCross_sw X Y R S p q n h h')

theorem zmod2_neg_one_pow_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ) (v : V) :
    ((-1 : ℤ) ^ k) • v = v := by
  rcases neg_one_pow_eq_or ℤ k with h1 | h1
  · rw [h1, one_smul]
  · rw [h1, neg_smul, one_smul]
    have h2 : (2 : ZMod 2) = 0 := rfl
    have : v + v = 0 := by
      rw [← two_smul (ZMod 2) v, h2, zero_smul]
    exact neg_eq_of_add_eq_zero_left this

abbrev coeff2 : ModuleCat.{0} (ZMod 2) := Finsler.RelativeCohomology.coeff

theorem braid_leftUnitor :
    (β_ coeff2 coeff2).hom ≫ (λ_ coeff2).hom = (λ_ coeff2).hom := by
  have h1 := braiding_leftUnitor (C := ModuleCat.{0} (ZMod 2)) (𝟙_ (ModuleCat.{0} (ZMod 2)))
  have h2 := MonoidalCategory.unitors_equal (C := ModuleCat.{0} (ZMod 2))
  exact h1.trans h2.symm

/-- **The cross product of mod-2 homology classes is symmetric under the swap.** -/
theorem cross_swap (i j m : ℕ) (h : i + j = m) (h' : j + i = m)
    (x : Finsler.PoolCap.homology X i) (y : Finsler.PoolCap.homology Y j) :
    (Finsler.PoolCap.push (β_ X Y).hom m).hom (Finsler.FilteredBilinearLoopProduct.cross X Y i j m h x y) =
      Finsler.FilteredBilinearLoopProduct.cross Y X j i m h' y x := by
  rw [Finsler.FilteredBilinearLoopProduct.cross_apply, Finsler.FilteredBilinearLoopProduct.cross_apply]
  let sHF := AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) m
  have hnat : ((sHF.map (λ_ coeff2).hom).app (X ⊗ Y)) ≫ Finsler.PoolCap.push (β_ X Y).hom m =
      (sHF.obj (coeff2 ⊗ coeff2)).map (β_ X Y).hom ≫ (sHF.map (λ_ coeff2).hom).app (Y ⊗ X) :=
    ((sHF.map (λ_ coeff2).hom).naturality (β_ X Y).hom).symm
  have hl : (sHF.map (λ_ coeff2).hom).app (Y ⊗ X) =
      (sHF.map (β_ coeff2 coeff2).hom).app (Y ⊗ X) ≫ (sHF.map (λ_ coeff2).hom).app (Y ⊗ X) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, braid_leftUnitor]
  have hs := singularHomologyCross_sw X Y coeff2 coeff2 i j m h h'
  have key : (TopCat.singularHomologyCross X Y coeff2 coeff2 i j m h ≫
        (sHF.map (λ_ coeff2).hom).app (X ⊗ Y)) ≫ Finsler.PoolCap.push (β_ X Y).hom m =
      ((-1 : ℤ) ^ (i * j)) • ((β_ _ _).hom ≫ TopCat.singularHomologyCross Y X coeff2 coeff2 j i m h' ≫
        (sHF.map (λ_ coeff2).hom).app (Y ⊗ X)) := by
    calc _ = TopCat.singularHomologyCross X Y coeff2 coeff2 i j m h ≫
          (sHF.obj (coeff2 ⊗ coeff2)).map (β_ X Y).hom ≫ (sHF.map (β_ coeff2 coeff2).hom).app (Y ⊗ X) ≫
            (sHF.map (λ_ coeff2).hom).app (Y ⊗ X) := by
          rw [Category.assoc, hnat]
          conv_lhs => rw [hl]
      _ = (TopCat.singularHomologyCross X Y coeff2 coeff2 i j m h ≫
          (sHF.obj (coeff2 ⊗ coeff2)).map (β_ X Y).hom ≫ (sHF.map (β_ coeff2 coeff2).hom).app (Y ⊗ X)) ≫
            (sHF.map (λ_ coeff2).hom).app (Y ⊗ X) := by simp only [Category.assoc]
      _ = _ := by rw [hs, Preadditive.zsmul_comp, Category.assoc]
  have := congrArg (fun φ => φ.hom (x ⊗ₜ[ZMod 2] y)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply] at this
  erw [this, zmod2_neg_one_pow_smul]
  rfl

end Homology

end SSet.ShuffleSwap
