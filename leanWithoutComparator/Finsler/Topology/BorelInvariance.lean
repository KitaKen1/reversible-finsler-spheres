module

public import Finsler.Topology.BorelQuasiIso
public import Finsler.Topology.BorelComparison
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance

/-! Invariance of Borel cohomology of actual topological pairs. An equivariant map of pairs which
induces isomorphisms on the actual relative singular cohomology in every degree induces
isomorphisms on the reflection Borel cohomology in every degree. A second involution of a pair
commuting with the first gives the iterated Borel complex of the pair, and a map of pairs
commuting with both involutions which is an isomorphism on actual relative singular cohomology
is an isomorphism on the iterated Borel cohomology. These statements reduce excision, homotopy
equivalence and deformation statements for Borel cohomology to the corresponding statements for
ordinary cohomology. With Tau Ceti's homotopy invariance of relative singular cohomology, an
equivariant map of pairs which is a homotopy equivalence of pairs induces isomorphisms on the
reflection and iterated Borel cohomology; its homotopy inverse and the homotopies need not be
equivariant. No excision statement is proved in this file. -/

@[expose] public section

namespace Finsler.BorelInvariance

open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelIterate
open Finsler.BorelComparison Finsler.RelativeCohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q}
  (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (f : P ⟶ Q) (hf : f ≫ s = r ≫ f)

/-- The ordinary cohomology map of the involutive cochains is the actual pullback. -/
theorem Hmap_pullHom (n : ℕ) (x : ordinary Q s hs n) :
    Hmap (pullHom hr hs f hf) n x =
      (ordinaryEquiv P r hr n).symm (nativePull f n (ordinaryEquiv Q s hs n x)) :=
  (LinearEquiv.eq_symm_apply _).mpr (ordinaryEquiv_natural hr hs f hf n x)

/-- An isomorphism on actual relative singular cohomology is an isomorphism on the ordinary
cohomology of the involutive cochains. -/
theorem bijective_Hmap (h : ∀ n, Function.Bijective (nativePull f n)) (n : ℕ) :
    Function.Bijective (Hmap (pullHom hr hs f hf) n) := by
  have hcomp : ⇑(Hmap (pullHom hr hs f hf) n) =
      ⇑(ordinaryEquiv P r hr n).symm ∘ ⇑(nativePull f n) ∘ ⇑(ordinaryEquiv Q s hs n) := by
    funext x
    exact Hmap_pullHom hr hs f hf n x
  rw [hcomp]
  exact (ordinaryEquiv P r hr n).symm.bijective.comp ((h n).comp (ordinaryEquiv Q s hs n).bijective)

/-- An equivariant map of pairs inducing isomorphisms on actual relative singular cohomology
induces isomorphisms on reflection Borel cohomology. -/
theorem bijective_HRmap (h : ∀ n, Function.Bijective (nativePull f n)) :
    ∀ n, Function.Bijective (HRmap (pullHom hr hs f hf) n) :=
  BorelQuasiIso.bijective_of_ordinary _ (bijective_Hmap hr hs f hf h)

/-- A homotopy equivalence of pairs is an isomorphism on actual relative singular cohomology. -/
theorem bijective_nativePull_of_homotopyEquiv (g : Q ⟶ P)
    (H : TopPair.Homotopy (f ≫ g) (𝟙 P)) (H' : TopPair.Homotopy (g ≫ f) (𝟙 Q)) (n : ℕ) :
    Function.Bijective (nativePull f n) := by
  have hiso : IsIso (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n) :=
    TopPair.isIso_singularCohomologyMap f g H H' coeff (ZMod 2) coeff n
  exact ConcreteCategory.bijective_of_isIso
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f n)

/-- An equivariant map of pairs which is a homotopy equivalence of pairs induces isomorphisms on
reflection Borel cohomology. The homotopy inverse and the homotopies need not be equivariant. -/
theorem bijective_HRmap_of_homotopyEquiv (g : Q ⟶ P)
    (H : TopPair.Homotopy (f ≫ g) (𝟙 P)) (H' : TopPair.Homotopy (g ≫ f) (𝟙 Q)) :
    ∀ n, Function.Bijective (HRmap (pullHom hr hs f hf) n) :=
  bijective_HRmap hr hs f hf (bijective_nativePull_of_homotopyEquiv f g H H')

section Second

/-- A second involution of a pair commuting with the first acts on the involutive cochains. -/
def commuting (τ : P ⟶ P) (hτ : τ ≫ τ = 𝟙 P) (hc : τ ≫ r = r ≫ τ) :
    Commuting (ofPair P r hr) where
  s j := ((pull τ).f j).hom
  ss j x := by
    have h := pull_comp_apply τ τ j x
    have h' : ((pull (τ ≫ τ)).f j).hom x = x := by
      rw [hτ]
      exact pull_id_apply _ j x
    exact h.symm.trans h'
  sd j x := pull_comm_apply τ j x
  st j x := by
    have h1 := pull_comp_apply τ r j (x : (cochains P).X j)
    have h2 := pull_comp_apply r τ j (x : (cochains P).X j)
    rw [hc] at h1
    exact h1.symm.trans h2

variable {τ : P ⟶ P} {σ : Q ⟶ Q} (hτ : τ ≫ τ = 𝟙 P) (hσ : σ ≫ σ = 𝟙 Q)
  (hcτ : τ ≫ r = r ≫ τ) (hcσ : σ ≫ s = s ≫ σ) (hfτ : f ≫ σ = τ ≫ f)

/-- A map of pairs commuting with both involutions commutes with the second cochain
involutions. -/
def commHom : CommHom (commuting hs σ hσ hcσ) (commuting hr τ hτ hcτ) where
  φ := pullHom hr hs f hf
  comm_s j x := by
    have h1 := pull_comp_apply f σ j x
    have h2 := pull_comp_apply τ f j x
    rw [hfτ] at h1
    exact h1.symm.trans h2

/-- A map of pairs commuting with two commuting involutions and inducing isomorphisms on actual
relative singular cohomology induces isomorphisms on the iterated Borel cohomology. -/
theorem bijective_iterated (h : ∀ n, Function.Bijective (nativePull f n)) :
    ∀ n, Function.Bijective (HRmap (borelHom (commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) n) :=
  BorelQuasiIso.bijective_iterated (commHom hr hs f hf hτ hσ hcτ hcσ hfτ)
    (bijective_Hmap hr hs f hf h)

/-- A map of pairs commuting with two commuting involutions which is a homotopy equivalence of
pairs induces isomorphisms on the iterated Borel cohomology. -/
theorem bijective_iterated_of_homotopyEquiv (g : Q ⟶ P)
    (H : TopPair.Homotopy (f ≫ g) (𝟙 P)) (H' : TopPair.Homotopy (g ≫ f) (𝟙 Q)) :
    ∀ n, Function.Bijective (HRmap (borelHom (commHom hr hs f hf hτ hσ hcτ hcσ hfτ)) n) :=
  bijective_iterated hr hs f hf hτ hσ hcτ hcσ hfτ
    (bijective_nativePull_of_homotopyEquiv f g H H')

end Second

end

end Finsler.BorelInvariance
