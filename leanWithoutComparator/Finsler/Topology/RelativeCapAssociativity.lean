module

public import Finsler.Topology.RelativeCapAbsolute

/-! Cap--cup associativity on the actual relative singular chains and homology.
The relative chain quotient is epi; no surjectivity of absolute-to-relative homology is assumed. -/

@[expose] public section

namespace Finsler.RelativeCapAssociativity

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open SphereOddDegree Finsler.CochainComparison Finsler.RelativeCap

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev chain (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p) :=
  TauCeti.ChainComplex.capChain (ZMod 2) (relativeDiagonal P) (unitAction P) p q n h φ

abbrev absoluteChain (X : TopCat.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) X p) :=
  TauCeti.ChainComplex.capChain (ZMod 2) (diagonal X)
    ((TopCat.toSSet.obj X).chainComplexPairing
      (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom) p q n h φ

theorem chain_assoc (P : TopPair.{0}) {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : singularCochainGroup (ZMod 2) P.fst q) :
    chain P p m n hp φ ≫ chain P q r m hq ψ =
      chain P (p + q) r n (by omega) (cochainCup p q φ ψ) := by
  have : Epi (quotient P) := (P.shortExact_singularChainComplexShortComplex coeff).epi_g
  apply (cancel_epi ((quotient P).f n)).mp
  have hφ := RelativeCapAbsolute.quotient_capChain P p m n hp φ
  have hψ := RelativeCapAbsolute.quotient_capChain P q r m hq ψ
  have hχ := RelativeCapAbsolute.quotient_capChain P (p + q) r n (by omega)
    (cochainCup p q φ ψ)
  have ha : absoluteChain P.fst p m n hp φ ≫ absoluteChain P.fst q r m hq ψ =
      absoluteChain P.fst (p + q) r n (by omega) (PoolCupComparison.nativeCup P.fst p q φ ψ) :=
    TopCat.capChain_alexanderWhitneyDiagonal_assoc P.fst (ZMod 2) hp hq φ ψ
  have ha' := ha.trans (congrArg (absoluteChain P.fst (p + q) r n (by omega))
    (PoolCupComparison.cochain_comparison P.fst p q φ ψ))
  calc
    (quotient P).f n ≫ (chain P p m n hp φ ≫ chain P q r m hq ψ) =
        (absoluteChain P.fst p m n hp φ ≫ (quotient P).f m) ≫ chain P q r m hq ψ := by
      rw [hφ, Category.assoc]
    _ = (absoluteChain P.fst p m n hp φ ≫ absoluteChain P.fst q r m hq ψ) ≫
        (quotient P).f r := by
      rw [Category.assoc]
      exact (congrArg (absoluteChain P.fst p m n hp φ ≫ ·) hψ.symm).trans
        (Category.assoc _ _ _).symm
    _ = absoluteChain P.fst (p + q) r n (by omega) (cochainCup p q φ ψ) ≫
        (quotient P).f r := congrArg (· ≫ _) ha'
    _ = (quotient P).f n ≫ chain P (p + q) r n (by omega) (cochainCup p q φ ψ) := hχ

abbrev cycleOf (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :=
  TauCeti.ChainComplex.capCycles (ZMod 2) (relativeDiagonal P) (unitAction P) p q n h
    ((native P.fst).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

private theorem cycleOf_i (P : TopPair.{0}) (p q n : ℕ) (h : p + q = n)
    (φ : singularCochainGroup (ZMod 2) P.fst p)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    cycleOf P p q n h φ hφ ≫ (relative P).iCycles q =
      (relative P).iCycles n ≫ chain P p q n h φ := by
  refine (TauCeti.ChainComplex.capCycles_i (relativeDiagonal P) (unitAction P)
    p q n h ((native P.fst).cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)).trans ?_
  exact congrArg (fun z => (relative P).iCycles n ≫ chain P p q n h z)
    ((native P.fst).i_cyclesMk φ (p + 1) (CochainClass.next_eq p) hφ)

theorem cycles_assoc (P : TopPair.{0}) {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : singularCochainGroup (ZMod 2) P.fst q)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) P.fst q ψ = 0) :
    cycleOf P p m n hp φ hφ ≫ cycleOf P q r m hq ψ hψ =
      cycleOf P (p + q) r n (by omega) (cochainCup p q φ ψ)
        (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  apply (cancel_mono ((relative P).iCycles r)).mp
  rw [Category.assoc, cycleOf_i, ← Category.assoc, cycleOf_i, Category.assoc,
    chain_assoc P hp hq, cycleOf_i]

theorem assoc (P : TopPair.{0}) {p q r m n : ℕ} (hp : p + m = n) (hq : q + r = m)
    (a : cohomologyZMod2 P.fst p) (b : cohomologyZMod2 P.fst q)
    (x : P.singularHomology (C := ModuleCat (ZMod 2)) coeff n) :
    RelativeCap.cap P q r m hq b (RelativeCap.cap P p m n hp a x) =
      RelativeCap.cap P (p + q) r n (by omega) (cupZMod2 a b) x := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective P.fst p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective P.fst q b
  have hm : ModuleCat.ofHom (RelativeCap.cap P p m n hp (cocycleClass P.fst p φ hφ)) ≫
      ModuleCat.ofHom (RelativeCap.cap P q r m hq (cocycleClass P.fst q ψ hψ)) =
      ModuleCat.ofHom (RelativeCap.cap P (p + q) r n (by omega)
        (cupZMod2 (cocycleClass P.fst p φ hφ) (cocycleClass P.fst q ψ hψ))) := by
    apply (cancel_epi ((relative P).homologyπ n)).mp
    rw [← Category.assoc, RelativeCap.cap_class, Category.assoc, RelativeCap.cap_class,
      ← Category.assoc, cupZMod2_mk, RelativeCap.cap_class]
    exact congrArg (· ≫ (relative P).homologyπ r) (cycles_assoc P hp hq φ ψ hφ hψ)
  exact ConcreteCategory.congr_hom hm x

end

end Finsler.RelativeCapAssociativity
