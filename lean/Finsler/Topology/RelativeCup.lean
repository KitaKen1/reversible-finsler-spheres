module

public import Finsler.Topology.CochainClass
public import Finsler.Topology.RelativeCupCochain
public import Finsler.Topology.TransportedCup

/-! Descend the actual relative cochain pairing in both variables, using
mathlib's homology cokernel, and compare its ambient image with Lean Pool's cup.
No relative/absolute comparison is assumed. -/

@[expose] public section

namespace Finsler.RelativeCup

open CategoryTheory CategoryTheory.Limits SphereOddDegree
open Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney

noncomputable section

abbrev cx (P : TopPair.{0}) := P.singularCochainComplex coeff (ZMod 2) coeff
abbrev cohomology (P : TopPair.{0}) (n : ℕ) := (cx P).homology n

def leftMor (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q) :
    (cochainCxZMod2 P.fst).X p ⟶ (cx P).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun φ => RelativeCupCochain.cup P p q φ ψ
      map_add' := fun φ φ' => RelativeCupCochain.add_left P p q φ φ' ψ
      map_smul' := fun r φ => RelativeCupCochain.smul_left P p q r φ ψ }

def rightMor (P : TopPair.{0}) (p q : ℕ) (φ : singularCochainGroup (ZMod 2) P.fst p) :
    (cx P).X q ⟶ (cx P).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun ψ => RelativeCupCochain.cup P p q φ ψ
      map_add' := fun ψ ψ' => RelativeCupCochain.add_right P p q φ ψ ψ'
      map_smul' := fun r ψ => RelativeCupCochain.smul_right P p q r φ ψ }

theorem left_closed (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0) :
    ((cochainCxZMod2 P.fst).iCycles p ≫ leftMor P p q ψ) ≫ (cx P).d (p + q) (p + q + 1) = 0 := by
  ext c
  exact RelativeCupCochain.preserves_cocycles P p q _ ψ
    (CochainClass.closed_iCycles (cochainCxZMod2 P.fst) p c) hψ

theorem right_closed (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    ((cx P).iCycles q ≫ rightMor P p q φ) ≫ (cx P).d (p + q) (p + q + 1) = 0 := by
  ext c
  exact RelativeCupCochain.preserves_cocycles P p q φ _ hφ (CochainClass.closed_iCycles (cx P) q c)

def cycleLeft (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0) :
    (cochainCxZMod2 P.fst).cycles p ⟶ cohomology P (p + q) :=
  (cx P).liftCycles ((cochainCxZMod2 P.fst).iCycles p ≫ leftMor P p q ψ)
      (p + q + 1) (CochainClass.next_eq (p + q)) (left_closed P p q ψ hψ)
    ≫ (cx P).homologyπ (p + q)

def cycleRight (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    (cx P).cycles q ⟶ cohomology P (p + q) :=
  (cx P).liftCycles ((cx P).iCycles q ≫ rightMor P p q φ)
      (p + q + 1) (CochainClass.next_eq (p + q)) (right_closed P p q φ hφ)
    ≫ (cx P).homologyπ (p + q)

theorem cycleLeft_apply (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0) (c : (cochainCxZMod2 P.fst).cycles p) :
    (cycleLeft P p q ψ hψ).hom c =
      CochainClass.classOf (cx P) (p + q)
        (RelativeCupCochain.cup P p q ((cochainCxZMod2 P.fst).iCycles p c) ψ)
        (RelativeCupCochain.preserves_cocycles P p q _ ψ
          (CochainClass.closed_iCycles (cochainCxZMod2 P.fst) p c) hψ) :=
  CochainClass.classOf_liftCycles (cx P) (p + q) _ (left_closed P p q ψ hψ) c

theorem cycleRight_apply (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (c : (cx P).cycles q) :
    (cycleRight P p q φ hφ).hom c =
      CochainClass.classOf (cx P) (p + q)
        (RelativeCupCochain.cup P p q φ ((cx P).iCycles q c))
        (RelativeCupCochain.preserves_cocycles P p q φ _ hφ (CochainClass.closed_iCycles (cx P) q c)) :=
  CochainClass.classOf_liftCycles (cx P) (p + q) _ (right_closed P p q φ hφ) c

theorem left_boundary_zero (P : TopPair.{0}) (q i p : ℕ)
    (η : (cochainCxZMod2 P.fst).X i) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0)
    (hc : RelativeCupCochain.differential P (p + q)
      (RelativeCupCochain.cup P p q (((cochainCxZMod2 P.fst).d i p).hom η) ψ) = 0) :
    CochainClass.classOf (cx P) (p + q)
      (RelativeCupCochain.cup P p q (((cochainCxZMod2 P.fst).d i p).hom η) ψ) hc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := h
    have heq := RelativeCupCochain.boundary_left P i q η ψ hψ
    have hc' : RelativeCupCochain.differential P (i + 1 + q)
        (RelativeCupCochain.cast P (aw_degree_left_succ i q).symm
          (RelativeCupCochain.differential P (i + q) (RelativeCupCochain.cup P i q η ψ))) = 0 := by
      rw [← heq]
      exact hc
    exact (CochainClass.classOf_congr (cx P) (i + 1 + q) heq hc hc').trans
      (CochainClass.classOf_cast_boundary (cx P) (aw_degree_left_succ i q).symm
        (RelativeCupCochain.cup P i q η ψ) hc')
  · have hz : RelativeCupCochain.cup P p q (((cochainCxZMod2 P.fst).d i p).hom η) ψ = 0 := by
      rw [(cochainCxZMod2 P.fst).shape i p h, ModuleCat.hom_zero, LinearMap.zero_apply]
      exact RelativeCupCochain.zero_left P p q ψ
    exact (CochainClass.classOf_congr (cx P) (p + q) hz hc (map_zero _)).trans
      (CochainClass.classOf_zero (cx P) (p + q) (map_zero _))

theorem right_boundary_zero (P : TopPair.{0}) (p i q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (η : (cx P).X i)
    (hc : RelativeCupCochain.differential P (p + q)
      (RelativeCupCochain.cup P p q φ (((cx P).d i q).hom η)) = 0) :
    CochainClass.classOf (cx P) (p + q)
      (RelativeCupCochain.cup P p q φ (((cx P).d i q).hom η)) hc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := h
    have heq := RelativeCupCochain.boundary_right P p i φ hφ η
    have hc' : RelativeCupCochain.differential P (p + (i + 1))
        (RelativeCupCochain.cast P (aw_degree_right_succ p i).symm
          (RelativeCupCochain.differential P (p + i) (RelativeCupCochain.cup P p i φ η))) = 0 := by
      rw [← heq]
      exact hc
    exact (CochainClass.classOf_congr (cx P) (p + (i + 1)) heq hc hc').trans
      (CochainClass.classOf_cast_boundary (cx P) (aw_degree_right_succ p i).symm
        (RelativeCupCochain.cup P p i φ η) hc')
  · have hz : RelativeCupCochain.cup P p q φ (((cx P).d i q).hom η) = 0 := by
      rw [(cx P).shape i q h, ModuleCat.hom_zero, LinearMap.zero_apply,
        RelativeCupCochain.zero_right]
    exact (CochainClass.classOf_congr (cx P) (p + q) hz hc (map_zero _)).trans
      (CochainClass.classOf_zero (cx P) (p + q) (map_zero _))

theorem cycleLeft_boundary (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0) :
    (cochainCxZMod2 P.fst).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cycleLeft P p q ψ hψ = 0 := by
  ext η
  change (cycleLeft P p q ψ hψ).hom _ = 0
  rw [cycleLeft_apply]
  have h := ConcreteCategory.congr_hom
    ((cochainCxZMod2 P.fst).toCycles_i ((ComplexShape.up ℕ).prev p) p) η
  have heq := congrArg (fun φ => RelativeCupCochain.cup P p q φ ψ) h
  have hc := RelativeCupCochain.preserves_cocycles P p q _ ψ
    (CochainClass.closed_boundary (cochainCxZMod2 P.fst) ((ComplexShape.up ℕ).prev p) p η) hψ
  exact (CochainClass.classOf_congr (cx P) (p + q) heq _ hc).trans
    (left_boundary_zero P q ((ComplexShape.up ℕ).prev p) p η ψ hψ hc)

theorem cycleRight_boundary (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    (cx P).toCycles ((ComplexShape.up ℕ).prev q) q ≫ cycleRight P p q φ hφ = 0 := by
  ext η
  change (cycleRight P p q φ hφ).hom _ = 0
  rw [cycleRight_apply]
  have h := ConcreteCategory.congr_hom ((cx P).toCycles_i ((ComplexShape.up ℕ).prev q) q) η
  have heq := congrArg (fun ψ => RelativeCupCochain.cup P p q φ ψ) h
  have hc := RelativeCupCochain.preserves_cocycles P p q φ _ hφ
    (CochainClass.closed_boundary (cx P) ((ComplexShape.up ℕ).prev q) q η)
  exact (CochainClass.classOf_congr (cx P) (p + q) heq _ hc).trans
    (right_boundary_zero P p ((ComplexShape.up ℕ).prev q) q φ hφ η hc)

def homLeft (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0) :
    cohomologyZMod2 P.fst p ⟶ cohomology P (p + q) :=
  CochainClass.descend (cochainCxZMod2 P.fst) p (cycleLeft P p q ψ hψ) (cycleLeft_boundary P p q ψ hψ)

def homRight (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    cohomology P q ⟶ cohomology P (p + q) :=
  CochainClass.descend (cx P) q (cycleRight P p q φ hφ) (cycleRight_boundary P p q φ hφ)

theorem homLeft_apply (P : TopPair.{0}) (p q : ℕ) (ψ : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) :
    (homLeft P p q ψ hψ).hom (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ) =
      CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ ψ)
        (RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ) := by
  have h := CochainClass.descend_classOf (cochainCxZMod2 P.fst) p
    (cycleLeft P p q ψ hψ) (cycleLeft_boundary P p q ψ hψ) φ hφ
  exact h.trans ((cycleLeft_apply P p q ψ hψ _).trans
    (CochainClass.classOf_congr (cx P) (p + q)
      (congrArg (fun a => RelativeCupCochain.cup P p q a ψ)
        ((cochainCxZMod2 P.fst).i_cyclesMk _ _ _ _)) _ _))

theorem homRight_apply (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (ψ : RelativeCupCochain.relative P q) (hψ : RelativeCupCochain.differential P q ψ = 0) :
    (homRight P p q φ hφ).hom (CochainClass.classOf (cx P) q ψ hψ) =
      CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ ψ)
        (RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ) := by
  have h := CochainClass.descend_classOf (cx P) q
    (cycleRight P p q φ hφ) (cycleRight_boundary P p q φ hφ) ψ hψ
  exact h.trans ((cycleRight_apply P p q φ hφ _).trans
    (CochainClass.classOf_congr (cx P) (p + q)
      (congrArg (RelativeCupCochain.cup P p q φ) ((cx P).i_cyclesMk _ _ _ _)) _ _))

def cup (P : TopPair.{0}) (p q : ℕ) (a : cohomologyZMod2 P.fst p) (b : cohomology P q) :
    cohomology P (p + q) :=
  (homLeft P p q (CochainClass.representative (cx P) q b)
    (CochainClass.representative_closed (cx P) q b)).hom a

/-- The computation rule proves independence of both chosen representatives:
the product depends only on their actual cohomology classes. -/
theorem cup_mk (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (ψ : RelativeCupCochain.relative P q) (hψ : RelativeCupCochain.differential P q ψ = 0) :
    cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)
      (CochainClass.classOf (cx P) q ψ hψ) =
      CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ ψ)
        (RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ) := by
  have hl := homLeft_apply P p q
    (CochainClass.representative (cx P) q (CochainClass.classOf (cx P) q ψ hψ))
    (CochainClass.representative_closed (cx P) q _) φ hφ
  have hr := homRight_apply P p q φ hφ
    (CochainClass.representative (cx P) q (CochainClass.classOf (cx P) q ψ hψ))
    (CochainClass.representative_closed (cx P) q _)
  have key := (congrArg (homRight P p q φ hφ).hom
    (CochainClass.classOf_representative (cx P) q (CochainClass.classOf (cx P) q ψ hψ))).symm.trans hr
  exact hl.trans (key.symm.trans (homRight_apply P p q φ hφ ψ hψ))

theorem cup_eq_homRight (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (b : cohomology P q) :
    cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ) b = (homRight P p q φ hφ).hom b := by
  have hb := CochainClass.classOf_representative (cx P) q b
  have hc := cup_mk P p q φ hφ (CochainClass.representative (cx P) q b)
    (CochainClass.representative_closed (cx P) q b)
  have hr := homRight_apply P p q φ hφ (CochainClass.representative (cx P) q b)
    (CochainClass.representative_closed (cx P) q b)
  exact (congrArg (cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)) hb).symm.trans
    (hc.trans (hr.symm.trans (congrArg (homRight P p q φ hφ).hom hb)))

theorem cup_eq_right (P : TopPair.{0}) (p q : ℕ) (a : cohomologyZMod2 P.fst p) (b : cohomology P q) :
    cup P p q a b =
      (homRight P p q (CochainClass.representative (cochainCxZMod2 P.fst) p a)
        (CochainClass.representative_closed (cochainCxZMod2 P.fst) p a)).hom b := by
  have ha := CochainClass.classOf_representative (cochainCxZMod2 P.fst) p a
  exact (congrArg (fun x => cup P p q x b) ha).symm.trans
    (cup_eq_homRight P p q _ (CochainClass.representative_closed (cochainCxZMod2 P.fst) p a) b)

theorem add_left (P : TopPair.{0}) (p q : ℕ) (a a' : cohomologyZMod2 P.fst p) (b : cohomology P q) :
    cup P p q (a + a') b = cup P p q a b + cup P p q a' b :=
  map_add _ a a'

theorem smul_left (P : TopPair.{0}) (p q : ℕ) (r : ZMod 2) (a : cohomologyZMod2 P.fst p) (b : cohomology P q) :
    cup P p q (r • a) b = r • cup P p q a b :=
  map_smul _ r a

theorem zero_left (P : TopPair.{0}) (p q : ℕ) (b : cohomology P q) : cup P p q 0 b = 0 := map_zero _

theorem add_right (P : TopPair.{0}) (p q : ℕ) (a : cohomologyZMod2 P.fst p) (b b' : cohomology P q) :
    cup P p q a (b + b') = cup P p q a b + cup P p q a b' := by
  rw [cup_eq_right, cup_eq_right, cup_eq_right, map_add]

theorem smul_right (P : TopPair.{0}) (p q : ℕ) (r : ZMod 2) (a : cohomologyZMod2 P.fst p) (b : cohomology P q) :
    cup P p q a (r • b) = r • cup P p q a b := by
  rw [cup_eq_right, cup_eq_right, map_smul]

theorem zero_right (P : TopPair.{0}) (p q : ℕ) (a : cohomologyZMod2 P.fst p) : cup P p q a 0 = 0 := by
  rw [cup_eq_right, map_zero]

/-- The descended pairing packaged as an actual bilinear map. Associativity
and a unit law are separate statements, not fields assumed here. -/
def cupLinear (P : TopPair.{0}) (p q : ℕ) :
    cohomologyZMod2 P.fst p →ₗ[ZMod 2] cohomology P q →ₗ[ZMod 2] cohomology P (p + q) where
  toFun a :=
    { toFun := cup P p q a
      map_add' := add_right P p q a
      map_smul' := fun r b => smul_right P p q r a b }
  map_add' a a' := by
    ext b
    exact add_left P p q a a' b
  map_smul' r a := by
    ext b
    exact smul_left P p q r a b

theorem cupLinear_apply (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (b : cohomology P q) : cupLinear P p q a b = cup P p q a b := rfl

theorem naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (a : cohomologyZMod2 Q.fst p) (b : cohomology Q q) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f (p + q)).hom
        (cup Q p q a b) =
      cup P p q ((cohPullback (TopPair.Hom.fst f) p).hom a)
        ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom b) := by
  let φ : singularCochainGroup (ZMod 2) Q.fst p := CochainClass.representative (cochainCxZMod2 Q.fst) p a
  let ψ : RelativeCupCochain.relative Q q := CochainClass.representative (cx Q) q b
  have hφ : cochainCoboundary (ZMod 2) Q.fst p φ = 0 := CochainClass.representative_closed _ p a
  have hψ : RelativeCupCochain.differential Q q ψ = 0 := CochainClass.representative_closed _ q b
  have ha : CochainClass.classOf (cochainCxZMod2 Q.fst) p φ hφ = a := CochainClass.classOf_representative _ p a
  have hb : CochainClass.classOf (cx Q) q ψ hψ = b := CochainClass.classOf_representative _ q b
  let g := TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) f
  let k := singularCochainComplexZMod2.map (TopPair.Hom.fst f).op
  let φ' := cochainPullback (TopPair.Hom.fst f) p φ
  let ψ' := RelativeCupCochain.pullback f q ψ
  have hφ' : cochainCoboundary (ZMod 2) P.fst p φ' = 0 := CochainClass.closed_map _ k p φ hφ
  have hψ' : RelativeCupCochain.differential P q ψ' = 0 := CochainClass.closed_map _ g q ψ hψ
  have hmφ : (cohPullback (TopPair.Hom.fst f) p).hom (CochainClass.classOf (cochainCxZMod2 Q.fst) p φ hφ) =
      CochainClass.classOf (cochainCxZMod2 P.fst) p φ' hφ' := by
    exact CochainClass.classOf_map (cochainCxZMod2 Q.fst) k p φ hφ hφ'
  have hmψ := CochainClass.classOf_map (cx Q) g q ψ hψ hψ'
  have hc := RelativeCupCochain.preserves_cocycles Q p q φ ψ hφ hψ
  have hcp := RelativeCupCochain.preserves_cocycles P p q φ' ψ' hφ' hψ'
  have hcmap := CochainClass.closed_map (cx Q) g (p + q) (RelativeCupCochain.cup Q p q φ ψ) hc
  have hm := CochainClass.classOf_map (cx Q) g (p + q) (RelativeCupCochain.cup Q p q φ ψ) hc hcmap
  have hn := CochainClass.classOf_congr (cx P) (p + q) (RelativeCupCochain.naturality f p q φ ψ) hcmap hcp
  calc
    _ = (HomologicalComplex.homologyMap g (p + q)).hom
        (cup Q p q (CochainClass.classOf (cochainCxZMod2 Q.fst) p φ hφ) (CochainClass.classOf (cx Q) q ψ hψ)) :=
      congrArg (HomologicalComplex.homologyMap g (p + q)).hom (congrArg₂ (cup Q p q) ha.symm hb.symm)
    _ = (HomologicalComplex.homologyMap g (p + q)).hom
        (CochainClass.classOf (cx Q) (p + q) (RelativeCupCochain.cup Q p q φ ψ) hc) :=
      congrArg (HomologicalComplex.homologyMap g (p + q)).hom (cup_mk Q p q φ hφ ψ hψ)
    _ = CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ' ψ') hcp := hm.trans hn
    _ = cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ' hφ')
        (CochainClass.classOf (cx P) q ψ' hψ') := (cup_mk P p q φ' hφ' ψ' hψ').symm
    _ = _ := congrArg₂ (cup P p q)
      (hmφ.symm.trans (congrArg (cohPullback (TopPair.Hom.fst f) p).hom ha))
      (hmψ.symm.trans (congrArg (HomologicalComplex.homologyMap g q).hom hb))

/-- Replacing either cocycle by another representative of the same class
does not change the relative product class. -/
theorem representative_independence (P : TopPair.{0}) (p q : ℕ)
    (φ φ' : singularCochainGroup (ZMod 2) P.fst p)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) P.fst p φ' = 0)
    (ψ ψ' : RelativeCupCochain.relative P q)
    (hψ : RelativeCupCochain.differential P q ψ = 0)
    (hψ' : RelativeCupCochain.differential P q ψ' = 0)
    (ha : CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ =
      CochainClass.classOf (cochainCxZMod2 P.fst) p φ' hφ')
    (hb : CochainClass.classOf (cx P) q ψ hψ = CochainClass.classOf (cx P) q ψ' hψ') :
    CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ ψ)
        (RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ) =
      CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ' ψ')
        (RelativeCupCochain.preserves_cocycles P p q φ' ψ' hφ' hψ') :=
  (cup_mk P p q φ hφ ψ hψ).symm.trans
    ((congrArg₂ (cup P p q) ha hb).trans (cup_mk P p q φ' hφ' ψ' hψ'))

def ambientMap (P : TopPair.{0}) : cx P ⟶ cochainCxZMod2 P.fst :=
  (P.singularCochainComplexShortComplex coeff (ZMod 2) coeff).f ≫ (cochainIso P.fst).inv

theorem ambientMap_homology (P : TopPair.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (ambientMap P) n = relativeToPool P n := by
  have h := HomologicalComplex.homologyMap_comp
    (P.singularCochainComplexShortComplex coeff (ZMod 2) coeff).f (cochainIso P.fst).inv n
  exact h

theorem toAmbient_closed (P : TopPair.{0}) (n : ℕ) (ψ : RelativeCupCochain.relative P n)
    (hψ : RelativeCupCochain.differential P n ψ = 0) :
    cochainCoboundary (ZMod 2) P.fst n (RelativeCupCochain.toAmbient P n ψ) = 0 :=
  CochainClass.closed_map (cx P) (ambientMap P) n ψ hψ

theorem relativeToPool_classOf (P : TopPair.{0}) (n : ℕ)
    (ψ : RelativeCupCochain.relative P n) (hψ : RelativeCupCochain.differential P n ψ = 0) :
    (relativeToPool P n).hom (CochainClass.classOf (cx P) n ψ hψ) =
      CochainClass.classOf (cochainCxZMod2 P.fst) n (RelativeCupCochain.toAmbient P n ψ)
        (toAmbient_closed P n ψ hψ) := by
  have h := CochainClass.classOf_map (cx P) (ambientMap P) n ψ hψ (toAmbient_closed P n ψ hψ)
  rw [ambientMap_homology] at h
  exact h

/-- The product is on actual relative cohomology, and its image agrees with
the actual absolute cup rather than a separately postulated operation. -/
theorem relativeToPool_cup (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (b : cohomology P q) :
    (relativeToPool P (p + q)).hom (cup P p q a b) =
      cupZMod2 a ((relativeToPool P q).hom b) := by
  let φ : singularCochainGroup (ZMod 2) P.fst p := CochainClass.representative (cochainCxZMod2 P.fst) p a
  let ψ : RelativeCupCochain.relative P q := CochainClass.representative (cx P) q b
  have hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0 := CochainClass.representative_closed _ p a
  have hψ : RelativeCupCochain.differential P q ψ = 0 := CochainClass.representative_closed _ q b
  have ha : CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ = a := CochainClass.classOf_representative _ p a
  have hb : CochainClass.classOf (cx P) q ψ hψ = b := CochainClass.classOf_representative _ q b
  have hc := RelativeCupCochain.preserves_cocycles P p q φ ψ hφ hψ
  have hψa := toAmbient_closed P q ψ hψ
  have hca := cochainCupZMod2_respects_cocycles p q φ (RelativeCupCochain.toAmbient P q ψ) hφ hψa
  calc
    _ = (relativeToPool P (p + q)).hom
        (cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)
          (CochainClass.classOf (cx P) q ψ hψ)) :=
      congrArg (relativeToPool P (p + q)).hom (congrArg₂ (cup P p q) ha.symm hb.symm)
    _ = (relativeToPool P (p + q)).hom
        (CochainClass.classOf (cx P) (p + q) (RelativeCupCochain.cup P p q φ ψ) hc) :=
      congrArg (relativeToPool P (p + q)).hom (cup_mk P p q φ hφ ψ hψ)
    _ = CochainClass.classOf (cochainCxZMod2 P.fst) (p + q)
        (RelativeCupCochain.toAmbient P (p + q) (RelativeCupCochain.cup P p q φ ψ))
        (toAmbient_closed P (p + q) _ hc) := relativeToPool_classOf P (p + q) _ hc
    _ = CochainClass.classOf (cochainCxZMod2 P.fst) (p + q)
        (cochainCup p q φ (RelativeCupCochain.toAmbient P q ψ)) hca :=
      CochainClass.classOf_congr (cochainCxZMod2 P.fst) (p + q)
        (RelativeCupCochain.toAmbient_cup P p q φ ψ) _ hca
    _ = cupZMod2 (CochainClass.classOf (cochainCxZMod2 P.fst) p φ hφ)
        (CochainClass.classOf (cochainCxZMod2 P.fst) q (RelativeCupCochain.toAmbient P q ψ) hψa) :=
      (cupZMod2_mk φ hφ (RelativeCupCochain.toAmbient P q ψ) hψa).symm
    _ = _ := congrArg₂ cupZMod2 ha
      ((relativeToPool_classOf P q ψ hψ).symm.trans (congrArg (relativeToPool P q).hom hb))

end

end Finsler.RelativeCup
