module

public import Finsler.Topology.PoolCap
public import Finsler.Topology.Relative

/-! descend the actual Alexander–Whitney diagonal
to C(X,A) -> C(X) tensor C(X,A), then use the genuine generic cap construction. -/

@[expose] public section

namespace Finsler.RelativeCap

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree Finsler.CochainComparison

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev absolute (X : TopCat.{0}) := (TopCat.toSSet.obj X).chainComplex coeff
abbrev relative (P : TopPair.{0}) := P.singularChainComplex coeff
abbrev inclusion (P : TopPair.{0}) := SSet.chainComplexMap (TopCat.toSSet.map P.map) coeff
abbrev quotient (P : TopPair.{0}) := P.singularChainComplexπ coeff
abbrev diagonal (X : TopCat.{0}) :=
  X.alexanderWhitneyDiagonal (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv

def projected (P : TopPair.{0}) :
    absolute P.fst ⟶ HomologicalComplex.tensorObj (absolute P.fst) (relative P) :=
  diagonal P.fst ≫ HomologicalComplex.tensorHom (𝟙 _) (quotient P)

theorem inclusion_projected (P : TopPair.{0}) : inclusion P ≫ projected P = 0 := by
  have hn : inclusion P ≫ diagonal P.fst = diagonal P.snd ≫
      HomologicalComplex.tensorHom (inclusion P) (inclusion P) :=
    TopCat.alexanderWhitneyDiagonal_naturality P.map
      (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
  calc
    inclusion P ≫ projected P = (inclusion P ≫ diagonal P.fst) ≫
        HomologicalComplex.tensorHom (𝟙 _) (quotient P) := (Category.assoc _ _ _).symm
    _ = (diagonal P.snd ≫ HomologicalComplex.tensorHom (inclusion P) (inclusion P)) ≫
        HomologicalComplex.tensorHom (𝟙 _) (quotient P) := congrArg (· ≫ _) hn
    _ = diagonal P.snd ≫ HomologicalComplex.tensorHom
        (inclusion P ≫ 𝟙 _) (inclusion P ≫ quotient P) := by
      rw [Category.assoc]
      change diagonal P.snd ≫ ((inclusion P ⊗ₘ inclusion P) ≫ (𝟙 _ ⊗ₘ quotient P)) =
        diagonal P.snd ≫ ((inclusion P ≫ 𝟙 _) ⊗ₘ (inclusion P ≫ quotient P))
      rw [tensorHom_comp_tensorHom]
    _ = 0 := by
      rw [P.chainComplexMap_comp_singularChainComplexπ coeff]
      have hz : HomologicalComplex.tensorHom (inclusion P)
          (0 : absolute P.snd ⟶ relative P) = 0 := by
        ext j : 1
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro i₁ i₂ h
        rw [HomologicalComplex.ι_tensorHom]
        simp only [HomologicalComplex.zero_f, MonoidalPreadditive.tensor_zero,
          zero_comp, comp_zero]
      exact (congrArg (diagonal P.snd ≫ ·) hz).trans (comp_zero)

def relativeDiagonal (P : TopPair.{0}) :
    relative P ⟶ HomologicalComplex.tensorObj (absolute P.fst) (relative P) :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainComplex coeff)
    (projected P) (inclusion_projected P)).1

theorem quotient_diagonal (P : TopPair.{0}) : quotient P ≫ relativeDiagonal P = projected P :=
  (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkSingularChainComplex coeff)
    (projected P) (inclusion_projected P)).2

theorem diagonal_naturality {P Q : TopPair.{0}} (f : P ⟶ Q) :
    TopPair.singularChainComplexMap f coeff ≫ relativeDiagonal Q = relativeDiagonal P ≫
      HomologicalComplex.tensorHom
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) coeff)
        (TopPair.singularChainComplexMap f coeff) := by
  let g := SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) coeff
  let r := TopPair.singularChainComplexMap f coeff
  have : Epi (quotient P) := (P.shortExact_singularChainComplexShortComplex coeff).epi_g
  apply (cancel_epi (quotient P)).mp
  change quotient P ≫ (r ≫ relativeDiagonal Q) = quotient P ≫
    (relativeDiagonal P ≫ HomologicalComplex.tensorHom g r)
  have hπ : g ≫ quotient Q = quotient P ≫ r :=
    TopPair.singularChainComplexπ_pair_naturality f coeff
  have hd : g ≫ diagonal Q.fst = diagonal P.fst ≫ HomologicalComplex.tensorHom g g :=
    TopCat.alexanderWhitneyDiagonal_naturality (TopPair.Hom.fst f)
      (λ_ (𝟙_ (ModuleCat (ZMod 2)))).inv
  calc
    quotient P ≫ (r ≫ relativeDiagonal Q) = (g ≫ quotient Q) ≫ relativeDiagonal Q := by
      rw [hπ, Category.assoc]
    _ = g ≫ projected Q := by rw [Category.assoc, quotient_diagonal]
    _ = (g ≫ diagonal Q.fst) ≫ HomologicalComplex.tensorHom (𝟙 _) (quotient Q) :=
      (Category.assoc _ _ _).symm
    _ = (diagonal P.fst ≫ HomologicalComplex.tensorHom g g) ≫
        HomologicalComplex.tensorHom (𝟙 _) (quotient Q) := congrArg (· ≫ _) hd
    _ = diagonal P.fst ≫ HomologicalComplex.tensorHom g (g ≫ quotient Q) := by
      change (diagonal P.fst ≫ (g ⊗ₘ g)) ≫ (𝟙 _ ⊗ₘ quotient Q) =
        diagonal P.fst ≫ (g ⊗ₘ (g ≫ quotient Q))
      rw [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
    _ = diagonal P.fst ≫ HomologicalComplex.tensorHom g (quotient P ≫ r) :=
      congrArg (fun z => diagonal P.fst ≫ HomologicalComplex.tensorHom g z) hπ
    _ = (diagonal P.fst ≫ HomologicalComplex.tensorHom (𝟙 _) (quotient P)) ≫
        HomologicalComplex.tensorHom g r := by
      change diagonal P.fst ≫ (g ⊗ₘ (quotient P ≫ r)) =
        (diagonal P.fst ≫ (𝟙 _ ⊗ₘ quotient P)) ≫ (g ⊗ₘ r)
      rw [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = quotient P ≫ (relativeDiagonal P ≫ HomologicalComplex.tensorHom g r) := by
      rw [← Category.assoc, quotient_diagonal]
      rfl

def unitAction (P : TopPair.{0}) :
    ((tensorLeft coeff).mapHomologicalComplex (ComplexShape.down ℕ)).obj (relative P) ⟶
      relative P where
  f q := (λ_ ((relative P).X q)).hom
  comm' i j _ := by
    exact (leftUnitor_naturality ((relative P).d i j)).symm

theorem unitAction_naturality {P Q : TopPair.{0}} (f : relative P ⟶ relative Q) :
    unitAction P ≫ f =
      ((tensorLeft coeff).mapHomologicalComplex (ComplexShape.down ℕ)).map f ≫ unitAction Q := by
  ext q : 1
  exact (leftUnitor_naturality (f.f q)).symm

def cap (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 P.fst p) :
    P.singularHomology (C := ModuleCat (ZMod 2)) coeff n →ₗ[ZMod 2]
      P.singularHomology (C := ModuleCat (ZMod 2)) coeff q :=
  (TauCeti.ChainComplex.cap (C := ModuleCat (ZMod 2)) (ZMod 2) (relativeDiagonal P) (unitAction P)
    p q n h (cohomologyEquiv P.fst p a)).hom

theorem add_left (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (a b : cohomologyZMod2 P.fst p)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff n) :
    cap P p q n h (a + b) x = cap P p q n h a x + cap P p q n h b x := by
  simp only [cap, map_add, ModuleCat.hom_add]
  rfl

theorem smul_left (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (c : ZMod 2) (a : cohomologyZMod2 P.fst p)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff n) :
    cap P p q n h (c • a) x = c • cap P p q n h a x := by
  simp only [cap, map_smul, ModuleCat.hom_smul]
  rfl

theorem zero_left (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff n) : cap P p q n h 0 x = 0 := by
  simp only [cap, map_zero, ModuleCat.hom_zero]
  rfl

theorem naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 Q.fst p)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff n) :
    (P.singularHomologyMap f coeff q).hom
        (cap P p q n h ((cohPullback (TopPair.Hom.fst f) p).hom a) x) =
      cap Q p q n h a ((P.singularHomologyMap f coeff n).hom x) := by
  let r := TopPair.singularChainComplexMap f coeff
  let g := SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) coeff
  unfold cap
  refine (congrArg (fun z => (P.singularHomologyMap f coeff q).hom
    ((TauCeti.ChainComplex.cap (ZMod 2) (relativeDiagonal P) (unitAction P)
      p q n h z).hom x)) (cohomology_natural_apply (TopPair.Hom.fst f) p a)).trans ?_
  exact ConcreteCategory.congr_hom
    (TauCeti.ChainComplex.cap_naturality (k := ZMod 2)
      (relativeDiagonal Q) (unitAction Q) (relativeDiagonal P) (unitAction P)
      r g r r (diagonal_naturality f) (unitAction_naturality r)
      p q n h (cohomologyEquiv Q.fst p a)) x

theorem cap_class (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    (relative P).homologyπ n ≫ ModuleCat.ofHom (cap P p q n h (cocycleClass P.fst p φ hφ)) =
      TauCeti.ChainComplex.capCycles (ZMod 2) (relativeDiagonal P) (unitAction P)
        p q n h ((native P.fst).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ) ≫
          (relative P).homologyπ q := by
  change (relative P).homologyπ n ≫
    TauCeti.ChainComplex.cap (ZMod 2) (relativeDiagonal P) (unitAction P) p q n h
      (cohomologyEquiv P.fst p (cocycleClass P.fst p φ hφ)) = _
  refine (congrArg (fun z => (relative P).homologyπ n ≫
    TauCeti.ChainComplex.cap (ZMod 2) (relativeDiagonal P) (unitAction P) p q n h z)
    (Finsler.PoolCupComparison.cohomology_cocycle P.fst p φ hφ)).trans ?_
  exact TauCeti.ChainComplex.cap_homologyπ (relativeDiagonal P) (unitAction P)
    p q n h ((native P.fst).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

theorem zero_on_image {P Q : TopPair.{0}} (f : P ⟶ Q) (p q n : ℕ) (h : p + q = n)
    (a : cohomologyZMod2 Q.fst p) (ha : (cohPullback (TopPair.Hom.fst f) p).hom a = 0)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff n) :
    cap Q p q n h a ((P.singularHomologyMap f coeff n).hom x) = 0 := by
  rw [← naturality f p q n h a x, ha, zero_left, map_zero]

end

end Finsler.RelativeCap
