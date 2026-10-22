module

public import Finsler.Topology.CupBoundary

/-! Units of the actual F₂ cup pairings: the left relative unit and both
absolute units. Degree transports are explicit; no unit law is postulated. -/

@[expose] public section

namespace Finsler.CupUnit

open CategoryTheory SphereOddDegree Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney

noncomputable section

def simplexCast (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (σ : singularSimplices X m) : singularSimplices X n := h ▸ σ

theorem map_eqToHom_apply (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (σ : singularSimplices X m) :
    (TopCat.toSSet.obj X).map (eqToHom (congrArg SimplexCategory.mk h.symm)).op σ =
      simplexCast X h σ := by
  subst n
  simp [simplexCast]

theorem backFace_zero (n : ℕ) :
    backFace 0 n = eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n).symm) := by
  ext i : 3
  apply Fin.ext
  simp [backFace]

theorem backSimplex_zero (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X (0 + n)) :
    backSimplex X 0 n σ = simplexCast X (Nat.zero_add n) σ := by
  unfold backSimplex
  rw [backFace_zero]
  exact map_eqToHom_apply X (Nat.zero_add n) σ

theorem cochainCast_eval (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (φ : singularCochainGroup (ZMod 2) X m) (σ : singularSimplices X n) :
    cochainEval n (cochainCast h φ) σ = cochainEval m φ (simplexCast X h.symm σ) := by
  subst n
  simp [cochainCast, simplexCast]

theorem cochain_one_left (X : TopCat.{0}) (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n) :
    cochainCup 0 n (cochainOne (R := ZMod 2) (Z := X)) φ = cochainCast (Nat.zero_add n).symm φ := by
  apply cochain_ext
  intro σ
  rw [cochainCup_eval, cochainOne_eval, one_mul, cochainCast_eval, backSimplex_zero]

theorem relative_cochain_one_left (P : TopPair.{0}) (n : ℕ)
    (ψ : RelativeCupCochain.relative P n) :
    RelativeCupCochain.cast P (Nat.zero_add n)
        (RelativeCupCochain.cup P 0 n (cochainOne (R := ZMod 2) (Z := P.fst)) ψ) = ψ := by
  apply RelativeCupCochain.toAmbient_injective P n
  rw [RelativeCupCochain.toAmbient_cast, RelativeCupCochain.toAmbient_cup,
    cochain_one_left, cochainCast_cast]

theorem relative_one_left (P : TopPair.{0}) (n : ℕ) (b : RelativeCup.cohomology P n) :
    CupBoundary.castClass P (Nat.zero_add n) (RelativeCup.cup P 0 n (oneZMod2 P.fst) b) = b := by
  let ψ := CochainClass.representative (RelativeCup.cx P) n b
  have hψ := CochainClass.representative_closed (RelativeCup.cx P) n b
  have hb := CochainClass.classOf_representative (RelativeCup.cx P) n b
  have hc := RelativeCup.cup_mk P 0 n (cochainOne (R := ZMod 2) (Z := P.fst))
    (cochainCoboundary_cochainOne P.fst) ψ hψ
  have hh := RelativeCupCochain.preserves_cocycles P 0 n _ ψ (cochainCoboundary_cochainOne P.fst) hψ
  have hu := relative_cochain_one_left P n ψ
  have hclosed : RelativeCupCochain.differential P n
      (RelativeCupCochain.cast P (Nat.zero_add n) (RelativeCupCochain.cup P 0 n
        (cochainOne (R := ZMod 2) (Z := P.fst)) ψ)) = 0 := by
    rw [hu]
    exact hψ
  have hcast := CupBoundary.castClass_classOf P (Nat.zero_add n) _ hh hclosed
  exact (congrArg (fun x => CupBoundary.castClass P (Nat.zero_add n)
    (RelativeCup.cup P 0 n (oneZMod2 P.fst) x)) hb).symm.trans
      ((congrArg (CupBoundary.castClass P (Nat.zero_add n)) hc).trans
        (hcast.trans ((CochainClass.classOf_congr (RelativeCup.cx P) n hu hclosed hψ).trans hb)))

def absoluteCast (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (a : cohomologyZMod2 X m) : cohomologyZMod2 X n := h ▸ a

theorem absoluteCast_classOf (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (φ : singularCochainGroup (ZMod 2) X m) (hφ : cochainCoboundary (ZMod 2) X m φ = 0)
    (hc : cochainCoboundary (ZMod 2) X n (cochainCast h φ) = 0) :
    absoluteCast X h (cocycleClass X m φ hφ) = cocycleClass X n (cochainCast h φ) hc := by
  subst n
  simp only [cochainCast, eqToHom_refl, Category.id_comp]
  rfl

theorem absolute_one_left (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    absoluteCast X (Nat.zero_add n) (cupZMod2 (oneZMod2 X) a) = a := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X n a
  have h0 := cochainCoboundary_cochainOne X
  have hc := cupZMod2_mk (cochainOne (R := ZMod 2) (Z := X)) h0 φ hφ
  have hh := cochainCupZMod2_respects_cocycles 0 n _ φ h0 hφ
  have hu : cochainCast (Nat.zero_add n) (cochainCup 0 n (cochainOne (R := ZMod 2) (Z := X)) φ) = φ := by
    rw [cochain_one_left, cochainCast_cast]
  have hclosed : cochainCoboundary (ZMod 2) X n
      (cochainCast (Nat.zero_add n) (cochainCup 0 n (cochainOne (R := ZMod 2) (Z := X)) φ)) = 0 := by
    rw [hu]
    exact hφ
  exact (congrArg (absoluteCast X (Nat.zero_add n)) hc).trans
    ((absoluteCast_classOf X (Nat.zero_add n) _ hh hclosed).trans
      (cocycleClass_congr X n hu hclosed hφ))

theorem absolute_one_right (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    cupZMod2 a (oneZMod2 X) = a := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective X n a
  have hc := cupZMod2_mk φ hφ (cochainOne (R := ZMod 2) (Z := X)) (cochainCoboundary_cochainOne X)
  exact hc.trans (cocycleClass_congr X n (cochainCup_one n φ) _ hφ)

end

end Finsler.CupUnit
