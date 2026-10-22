module

public import Finsler.Topology.CupUnit

/-! Strict associativity of the actual Alexander–Whitney cochain product,
then of the actual absolute product and absolute-relative pairing over F₂.
Relative cohomology is not assumed to inject into absolute cohomology. -/

@[expose] public section

namespace Finsler.CupAssociativity

open CategoryTheory SphereOddDegree Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney

noncomputable section

def degreeMap {m n : ℕ} (h : m = n) :
    (SimplexCategory.mk m) ⟶ SimplexCategory.mk n := eqToHom (congrArg SimplexCategory.mk h)

theorem degreeMap_val {m n : ℕ} (h : m = n) (i : Fin (m + 1)) :
    ((degreeMap h).toOrderHom i : ℕ) = i.val := by
  rw [degreeMap, SimplexCategory.eqToHom_toOrderHom]
  rfl

theorem front_front (p q r : ℕ) :
    frontFace p q ≫ frontFace (p + q) r ≫ degreeMap (Nat.add_assoc p q r) =
      frontFace p (q + r) := by
  ext i : 3
  apply Fin.ext
  change ((degreeMap (Nat.add_assoc p q r)).toOrderHom
    ((frontFace (p + q) r).toOrderHom ((frontFace p q).toOrderHom i)) : ℕ) = _
  rw [degreeMap_val, frontFace_apply, frontFace_apply, frontFace_apply]

theorem back_front (p q r : ℕ) :
    backFace p q ≫ frontFace (p + q) r ≫ degreeMap (Nat.add_assoc p q r) =
      frontFace q r ≫ backFace p (q + r) := by
  ext i : 3
  apply Fin.ext
  change ((degreeMap (Nat.add_assoc p q r)).toOrderHom
    ((frontFace (p + q) r).toOrderHom ((backFace p q).toOrderHom i)) : ℕ) =
    ((backFace p (q + r)).toOrderHom ((frontFace q r).toOrderHom i) : ℕ)
  rw [degreeMap_val, frontFace_apply, backFace_apply, backFace_apply, frontFace_apply]

theorem back_back (p q r : ℕ) :
    backFace (p + q) r ≫ degreeMap (Nat.add_assoc p q r) =
      backFace q r ≫ backFace p (q + r) := by
  ext i : 3
  apply Fin.ext
  change ((degreeMap (Nat.add_assoc p q r)).toOrderHom
    ((backFace (p + q) r).toOrderHom i) : ℕ) =
    ((backFace p (q + r)).toOrderHom ((backFace q r).toOrderHom i) : ℕ)
  rw [degreeMap_val, backFace_apply, backFace_apply, backFace_apply]
  omega

theorem simplexCast_eq_map (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (σ : singularSimplices X n) :
    CupUnit.simplexCast X h.symm σ = (TopCat.toSSet.obj X).map (degreeMap h).op σ :=
  (CupUnit.map_eqToHom_apply X h.symm σ).symm

theorem front_front_simplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : singularSimplices X (p + (q + r))) :
    frontSimplex X p q (frontSimplex X (p + q) r
      (CupUnit.simplexCast X (Nat.add_assoc p q r).symm σ)) =
      frontSimplex X p (q + r) σ := by
  rw [simplexCast_eq_map X (Nat.add_assoc p q r) σ]
  unfold frontSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    Category.assoc, front_front]

theorem back_front_simplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : singularSimplices X (p + (q + r))) :
    backSimplex X p q (frontSimplex X (p + q) r
      (CupUnit.simplexCast X (Nat.add_assoc p q r).symm σ)) =
      frontSimplex X q r (backSimplex X p (q + r) σ) := by
  rw [simplexCast_eq_map X (Nat.add_assoc p q r) σ]
  unfold frontSimplex backSimplex
  rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
    Category.assoc, back_front, op_comp, Functor.map_comp_apply]

theorem back_back_simplex (X : TopCat.{0}) (p q r : ℕ)
    (σ : singularSimplices X (p + (q + r))) :
    backSimplex X (p + q) r (CupUnit.simplexCast X (Nat.add_assoc p q r).symm σ) =
      backSimplex X q r (backSimplex X p (q + r) σ) := by
  rw [simplexCast_eq_map X (Nat.add_assoc p q r) σ]
  unfold backSimplex
  rw [← Functor.map_comp_apply, ← op_comp, back_back, op_comp, Functor.map_comp_apply]

theorem cochain_assoc (X : TopCat.{0}) (p q r : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (γ : singularCochainGroup (ZMod 2) X r) :
    cochainCast (Nat.add_assoc p q r) (cochainCup (p + q) r (cochainCup p q α β) γ) =
      cochainCup p (q + r) α (cochainCup q r β γ) := by
  apply cochain_ext
  intro σ
  rw [CupUnit.cochainCast_eval, cochainCup_eval, cochainCup_eval,
    cochainCup_eval, cochainCup_eval, front_front_simplex, back_front_simplex, back_back_simplex]
  exact mul_assoc _ _ _

theorem relative_cochain_assoc (P : TopPair.{0}) (p q r : ℕ)
    (α : singularCochainGroup (ZMod 2) P.fst p) (β : singularCochainGroup (ZMod 2) P.fst q)
    (γ : RelativeCupCochain.relative P r) :
    RelativeCupCochain.cast P (Nat.add_assoc p q r)
      (RelativeCupCochain.cup P (p + q) r (cochainCup p q α β) γ) =
      RelativeCupCochain.cup P p (q + r) α (RelativeCupCochain.cup P q r β γ) := by
  apply RelativeCupCochain.toAmbient_injective P (p + (q + r))
  rw [RelativeCupCochain.toAmbient_cast, RelativeCupCochain.toAmbient_cup,
    RelativeCupCochain.toAmbient_cup, RelativeCupCochain.toAmbient_cup]
  exact cochain_assoc P.fst p q r α β (RelativeCupCochain.toAmbient P r γ)

theorem absolute_assoc (X : TopCat.{0}) (p q r : ℕ)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) (c : cohomologyZMod2 X r) :
    CupUnit.absoluteCast X (Nat.add_assoc p q r) (cupZMod2 (cupZMod2 a b) c) =
      cupZMod2 a (cupZMod2 b c) := by
  obtain ⟨α, hα, rfl⟩ := cocycleClass_surjective X p a
  obtain ⟨β, hβ, rfl⟩ := cocycleClass_surjective X q b
  obtain ⟨γ, hγ, rfl⟩ := cocycleClass_surjective X r c
  have hab := cochainCupZMod2_respects_cocycles p q α β hα hβ
  have hbc := cochainCupZMod2_respects_cocycles q r β γ hβ hγ
  have hl := cochainCupZMod2_respects_cocycles (p + q) r (cochainCup p q α β) γ hab hγ
  have hr := cochainCupZMod2_respects_cocycles p (q + r) α (cochainCup q r β γ) hα hbc
  have heq := cochain_assoc X p q r α β γ
  have hcast : cochainCoboundary (ZMod 2) X (p + (q + r))
      (cochainCast (Nat.add_assoc p q r) (cochainCup (p + q) r (cochainCup p q α β) γ)) = 0 := by
    rw [heq]
    exact hr
  have hfirst := (congrArg (fun x => cupZMod2 x (cocycleClass X r γ hγ))
    (cupZMod2_mk α hα β hβ)).trans (cupZMod2_mk (cochainCup p q α β) hab γ hγ)
  have hlast := (congrArg (fun x => cupZMod2 (cocycleClass X p α hα) x)
    (cupZMod2_mk β hβ γ hγ)).trans (cupZMod2_mk α hα (cochainCup q r β γ) hbc)
  exact (congrArg (CupUnit.absoluteCast X (Nat.add_assoc p q r)) hfirst).trans
    ((CupUnit.absoluteCast_classOf X (Nat.add_assoc p q r) _ hl hcast).trans
      ((cocycleClass_congr X (p + (q + r)) heq hcast hr).trans hlast.symm))

/-- The module associativity law on actual relative cohomology. The proof
uses the cochain injection, not an assumed injection on cohomology. -/
theorem relative_assoc (P : TopPair.{0}) (p q r : ℕ)
    (a : cohomologyZMod2 P.fst p) (b : cohomologyZMod2 P.fst q)
    (c : RelativeCup.cohomology P r) :
    CupBoundary.castClass P (Nat.add_assoc p q r)
      (RelativeCup.cup P (p + q) r (cupZMod2 a b) c) =
      RelativeCup.cup P p (q + r) a (RelativeCup.cup P q r b c) := by
  obtain ⟨α, hα, rfl⟩ := cocycleClass_surjective P.fst p a
  obtain ⟨β, hβ, rfl⟩ := cocycleClass_surjective P.fst q b
  let γ := CochainClass.representative (RelativeCup.cx P) r c
  have hγ := CochainClass.representative_closed (RelativeCup.cx P) r c
  have hb := CochainClass.classOf_representative (RelativeCup.cx P) r c
  have hab := cochainCupZMod2_respects_cocycles p q α β hα hβ
  have hbc := RelativeCupCochain.preserves_cocycles P q r β γ hβ hγ
  have hl := RelativeCupCochain.preserves_cocycles P (p + q) r (cochainCup p q α β) γ hab hγ
  have hr := RelativeCupCochain.preserves_cocycles P p (q + r) α
    (RelativeCupCochain.cup P q r β γ) hα hbc
  have heq := relative_cochain_assoc P p q r α β γ
  have hcast : RelativeCupCochain.differential P (p + (q + r))
      (RelativeCupCochain.cast P (Nat.add_assoc p q r)
        (RelativeCupCochain.cup P (p + q) r (cochainCup p q α β) γ)) = 0 := by
    rw [heq]
    exact hr
  have hfirst := (congrArg (fun x => RelativeCup.cup P (p + q) r x
    (CochainClass.classOf (RelativeCup.cx P) r γ hγ)) (cupZMod2_mk α hα β hβ)).trans
      (RelativeCup.cup_mk P (p + q) r (cochainCup p q α β) hab γ hγ)
  have hlast := (congrArg (fun x => RelativeCup.cup P p (q + r)
    (cocycleClass P.fst p α hα) x) (RelativeCup.cup_mk P q r β hβ γ hγ)).trans
      (RelativeCup.cup_mk P p (q + r) α hα (RelativeCupCochain.cup P q r β γ) hbc)
  have hcore := (congrArg (CupBoundary.castClass P (Nat.add_assoc p q r)) hfirst).trans
    ((CupBoundary.castClass_classOf P (Nat.add_assoc p q r) _ hl hcast).trans
      ((CochainClass.classOf_congr (RelativeCup.cx P) (p + (q + r)) heq hcast hr).trans hlast.symm))
  exact (congrArg (fun x => CupBoundary.castClass P (Nat.add_assoc p q r)
    (RelativeCup.cup P (p + q) r (cupZMod2 (cocycleClass P.fst p α hα)
      (cocycleClass P.fst q β hβ)) x)) hb).symm.trans
      (hcore.trans (congrArg (fun x => RelativeCup.cup P p (q + r)
        (cocycleClass P.fst p α hα) (RelativeCup.cup P q r (cocycleClass P.fst q β hβ) x)) hb))

end

end Finsler.CupAssociativity
