module

public import Finsler.Topology.BorelInvariance
public import Finsler.Topology.RelativeKronecker
public import TauCeti.AlgebraicTopology.Singular.Excision

/-! Excision for Borel cohomology. Over F₂ the actual relative singular cohomology is the dual of
the actual relative singular homology, naturally in maps of pairs, so a map of pairs inducing an
isomorphism on relative singular homology in degree n induces a bijection on relative singular
cohomology in degree n. With the invariance theorem, an equivariant map of pairs inducing
isomorphisms on relative singular homology induces isomorphisms on reflection Borel cohomology
and, when it commutes with a second commuting involution, on the iterated Borel cohomology.
With the pinned Tau Ceti excision theorem this applies to every equivariant map of pairs which
is an embedding of the ambient spaces, takes the subspace onto the full preimage of the
subspace, and whose target has an open cover by sets lying in the subspace or in the image. -/

@[expose] public section

namespace Finsler.BorelExcision

open CategoryTheory Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelIterate
open Finsler.BorelComparison Finsler.RelativeCohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {P Q : TopPair.{0}} (f : P ⟶ Q)

/-- An isomorphism on actual relative singular homology in degree n is a bijection on actual
relative singular cohomology in degree n. -/
theorem bijective_nativePull_of_homology (n : ℕ)
    (h : IsIso (P.singularHomologyMap f coeff n)) : Function.Bijective (nativePull f n) := by
  have hg : Function.Bijective (P.singularHomologyMap f coeff n).hom :=
    ConcreteCategory.bijective_of_isIso (P.singularHomologyMap f coeff n)
  let e := LinearEquiv.ofBijective (P.singularHomologyMap f coeff n).hom hg
  have hcomp : ⇑(nativePull f n) =
      ⇑(RelativeKronecker.equiv P n).symm ∘ ⇑e.dualMap ∘ ⇑(RelativeKronecker.equiv Q n) := by
    funext a
    exact (LinearEquiv.eq_symm_apply _).mpr (RelativeKronecker.equiv_natural f n a)
  rw [hcomp]
  exact (RelativeKronecker.equiv P n).symm.bijective.comp
    (e.dualMap.bijective.comp (RelativeKronecker.equiv Q n).bijective)

variable {r : P ⟶ P} {s : Q ⟶ Q} (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (hf : f ≫ s = r ≫ f)

/-- An equivariant map of pairs inducing isomorphisms on actual relative singular homology
induces isomorphisms on reflection Borel cohomology. -/
theorem bijective_HRmap_of_homology
    (h : ∀ n, IsIso (P.singularHomologyMap f coeff n)) :
    ∀ n, Function.Bijective (HRmap (pullHom hr hs f hf) n) :=
  BorelInvariance.bijective_HRmap hr hs f hf fun n => bijective_nativePull_of_homology f n (h n)

section Excision

variable (hemb : IsEmbedding (TopPair.Hom.fst f))
  (hsnd : ∀ x, TopPair.Hom.fst f x ∈ Set.range Q.map → x ∈ Set.range P.map)
  {ι : Type} (U : ι → Set Q.fst) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
  (hUf : ∀ i, U i ⊆ Set.range Q.map ∨ U i ⊆ Set.range (TopPair.Hom.fst f))

include hemb hsnd hU hcov hUf in
/-- Excision for reflection Borel cohomology: an equivariant map of pairs which is an embedding
of the ambient spaces, with the subspace equal to the full preimage and with an open cover of
the target by sets lying in the subspace or in the image, induces isomorphisms. -/
theorem bijective_HRmap_of_open_cover :
    ∀ n, Function.Bijective (HRmap (pullHom hr hs f hf) n) :=
  bijective_HRmap_of_homology f hr hs hf fun n =>
    TopPair.isIso_singularHomologyMap_of_open_cover coeff f hemb hsnd U hU hcov hUf n

variable {τ : P ⟶ P} {σ : Q ⟶ Q} (hτ : τ ≫ τ = 𝟙 P) (hσ : σ ≫ σ = 𝟙 Q)
  (hcτ : τ ≫ r = r ≫ τ) (hcσ : σ ≫ s = s ≫ σ) (hfτ : f ≫ σ = τ ≫ f)

include hemb hsnd hU hcov hUf in
/-- Excision for the iterated Borel cohomology of two commuting involutions. -/
theorem bijective_iterated_of_open_cover :
    ∀ n, Function.Bijective
      (HRmap (borelHom (BorelInvariance.commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) n) :=
  BorelInvariance.bijective_iterated hr hs f hf hτ hσ hcτ hcσ hfτ fun n =>
    bijective_nativePull_of_homology f n
      (TopPair.isIso_singularHomologyMap_of_open_cover coeff f hemb hsnd U hU hcov hUf n)

end Excision

end

end Finsler.BorelExcision
