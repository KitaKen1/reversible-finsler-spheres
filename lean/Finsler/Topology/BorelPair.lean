module

public import Finsler.Topology.RelativeCohomology
public import Finsler.Topology.BorelCochain

/-! Reflection Borel cohomology of an actual topological pair with an involution. The relative
F₂ singular cochains of the pair, with the involution induced by the map of pairs, form an
involutive cochain complex; its Borel cohomology and ordinary cohomology carry the exact Gysin
maps w, forget and transfer. An equivariant map of pairs induces an equivariant cochain map
(pullback), compatibly with composition. -/

@[expose] public section

namespace Finsler.BorelPair

open CategoryTheory Finsler.BorelCochain Finsler.RelativeCohomology

noncomputable section

/-- The relative cochains of a pair. -/
abbrev cochains (P : TopPair.{0}) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  P.singularCochainComplex coeff (ZMod 2) coeff

/-- The pullback of relative cochains along a map of pairs. -/
abbrev pull {P Q : TopPair.{0}} (f : P ⟶ Q) : cochains Q ⟶ cochains P :=
  TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) f

theorem pull_comp_apply {P Q R : TopPair.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (j : ℕ)
    (x : (cochains R).X j) :
    ((pull (f ≫ g)).f j).hom x = ((pull f).f j).hom (((pull g).f j).hom x) := by
  have h := TopPair.singularCochainComplexMap_comp (R := coeff) (k := ZMod 2) (M := coeff) f g
  exact congrArg (fun φ => (φ.f j).hom x) h

theorem pull_id_apply (P : TopPair.{0}) (j : ℕ) (x : (cochains P).X j) :
    ((pull (𝟙 P)).f j).hom x = x := by
  have h := TopPair.singularCochainComplexMap_id (R := coeff) (k := ZMod 2) (M := coeff) P
  exact congrArg (fun φ => (φ.f j).hom x) h

theorem pull_comm_apply {P Q : TopPair.{0}} (f : P ⟶ Q) (j : ℕ) (x : (cochains Q).X j) :
    ((pull f).f (j + 1)).hom (((cochains Q).d j (j + 1)).hom x) =
      ((cochains P).d j (j + 1)).hom (((pull f).f j).hom x) := by
  have h := (pull f).comm j (j + 1)
  exact (congrArg (fun φ => φ.hom x) h).symm

theorem d_d_apply (P : TopPair.{0}) (j : ℕ) (x : (cochains P).X j) :
    ((cochains P).d (j + 1) (j + 1 + 1)).hom (((cochains P).d j (j + 1)).hom x) = 0 := by
  have h := (cochains P).d_comp_d j (j + 1) (j + 1 + 1)
  have h' := congrArg (fun φ => φ.hom x) h
  exact h'

/-- The involutive relative cochain complex of a pair with an involution. -/
def ofPair (P : TopPair.{0}) (r : P ⟶ P) (hr : r ≫ r = 𝟙 P) : InvComplex where
  C j := (cochains P).X j
  d j := ((cochains P).d j (j + 1)).hom
  t j := ((pull r).f j).hom
  dd j x := d_d_apply P j x
  tt j x := by
    have h := pull_comp_apply r r j x
    rw [hr, pull_id_apply] at h
    exact h.symm
  td j x := pull_comm_apply r j x

/-- An equivariant map of pairs pulls back to an equivariant cochain map. -/
def pullHom {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q} (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q)
    (f : P ⟶ Q) (hf : f ≫ s = r ≫ f) : InvHom (ofPair Q s hs) (ofPair P r hr) where
  f j := ((pull f).f j).hom
  comm_d j x := pull_comm_apply f j x
  comm_t j x := by
    have h1 := pull_comp_apply f s j x
    have h2 := pull_comp_apply r f j x
    rw [hf] at h1
    exact h1.symm.trans h2

theorem pullHom_comp {P Q R : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q} {u : R ⟶ R}
    (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (hu : u ≫ u = 𝟙 R) (f : P ⟶ Q) (g : Q ⟶ R)
    (hf : f ≫ s = r ≫ f) (hg : g ≫ u = s ≫ g) (hfg : (f ≫ g) ≫ u = r ≫ (f ≫ g)) (j : ℕ)
    (x : (cochains R).X j) :
    (pullHom hr hu (f ≫ g) hfg).f j x =
      (invHomComp (pullHom hs hu g hg) (pullHom hr hs f hf)).f j x :=
  pull_comp_apply f g j x

end

end Finsler.BorelPair
