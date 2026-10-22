module

public import TauCeti.AlgebraicTopology.Singular.Relative

/-! Verified reuse of Tau Ceti's relative singular chain model.
The Finsler loop-space pairs and their maps still need to be instantiated. -/

@[expose] public section

namespace Finsler.Relative

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

theorem chain_short_exact (P : TopPair.{w}) (R : C) :
    (P.singularChainComplexShortComplex R).ShortExact :=
  P.shortExact_singularChainComplexShortComplex R

theorem boundary_natural {P P' : TopPair.{w}} (f : P ⟶ P') (R : C)
    (n m : ℕ) (h : m + 1 = n) :
    P.singularHomologyδ R n m h ≫
        SSet.homologyMap (TopCat.toSSet.map (TopPair.Hom.snd f)) R m =
      TopPair.singularHomologyMap f R n ≫ P'.singularHomologyδ R n m h :=
  TopPair.singularHomologyδ_naturality R f n m h

end Finsler.Relative
