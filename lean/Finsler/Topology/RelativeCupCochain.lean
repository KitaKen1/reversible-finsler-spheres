module

public import Finsler.Topology.CochainComparison

/-! The canonical relative cochain cup action on actual topological pairs.
The ambient cochain injection is injective, so the lift used here is unique.
Naturality, bilinearity and the differential formula hold on cochains.
The separate RelativeCup module descends this pairing to relative cohomology. -/

@[expose] public section

namespace Finsler.RelativeCupCochain

open CategoryTheory SphereOddDegree Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney

noncomputable section

abbrev sequence (P : TopPair.{0}) (n : ℕ) :=
  (P.singularCochainComplexShortComplex coeff (ZMod 2) coeff).map
    (HomologicalComplex.eval (ModuleCat (ZMod 2)) (ComplexShape.up ℕ) n)

abbrev relative (P : TopPair.{0}) (n : ℕ) :=
  (P.singularCochainComplex coeff (ZMod 2) coeff).X n

def toAmbient (P : TopPair.{0}) (n : ℕ) :
    relative P n →ₗ[ZMod 2] singularCochainGroup (ZMod 2) P.fst n :=
  (sequence P n).f.hom

theorem degree_short_exact (P : TopPair.{0}) (n : ℕ) : (sequence P n).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (Finsler.RelativeCohomology.cochain_short_exact P) n

theorem toAmbient_injective (P : TopPair.{0}) (n : ℕ) :
    Function.Injective (toAmbient P n) := by
  have : Mono (sequence P n).f := (degree_short_exact P n).mono_f
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem restriction_toAmbient (P : TopPair.{0}) (n : ℕ) (ψ : relative P n) :
    cochainPullback P.map n (toAmbient P n ψ) = 0 :=
  ConcreteCategory.congr_hom (sequence P n).zero ψ

theorem exists_lift (P : TopPair.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst n) (hφ : cochainPullback P.map n φ = 0) :
    ∃ ψ : relative P n, toAmbient P n ψ = φ :=
  (ShortComplex.moduleCat_exact_iff _).mp (degree_short_exact P n).exact φ hφ

theorem exists_cup_lift (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    ∃ χ : relative P (p + q),
      toAmbient P (p + q) χ = cochainCup p q φ (toAmbient P q ψ) := by
  apply exists_lift
  rw [cochainCup_naturality, restriction_toAmbient, cochainCup_zero_right]

def cup (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    relative P (p + q) := Classical.choose (exists_cup_lift P p q φ ψ)

theorem toAmbient_cup (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    toAmbient P (p + q) (cup P p q φ ψ) = cochainCup p q φ (toAmbient P q ψ) :=
  Classical.choose_spec (exists_cup_lift P p q φ ψ)

theorem cup_unique (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q)
    (χ : relative P (p + q))
    (hχ : toAmbient P (p + q) χ = cochainCup p q φ (toAmbient P q ψ)) :
    χ = cup P p q φ ψ :=
  (toAmbient_injective P (p + q)) (hχ.trans (toAmbient_cup P p q φ ψ).symm)

def pullback {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ) : relative Q n →ₗ[ZMod 2] relative P n :=
  ((TopPair.singularCochainComplexMap (R := coeff) (k := ZMod 2) (M := coeff) f).f n).hom

theorem toAmbient_pullback {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ) (ψ : relative Q n) :
    toAmbient P n (pullback f n ψ) =
      cochainPullback (TopPair.Hom.fst f) n (toAmbient Q n ψ) := by
  have h := (TopPair.singularCochainComplexShortComplexMap
    (R := coeff) (k := ZMod 2) (M := coeff) f).comm₁₂
  simp only [TopPair.singularCochainComplexShortComplexMap_τ₁,
    TopPair.singularCochainComplexShortComplexMap_τ₂] at h
  exact congrArg (fun g => (g.f n).hom ψ) h

theorem naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Q.fst p) (ψ : relative Q q) :
    pullback f (p + q) (cup Q p q φ ψ) =
      cup P p q (cochainPullback (TopPair.Hom.fst f) p φ) (pullback f q ψ) := by
  apply toAmbient_injective P (p + q)
  rw [toAmbient_pullback, toAmbient_cup, cochainCup_naturality, toAmbient_cup,
    toAmbient_pullback]

theorem add_left (P : TopPair.{0}) (p q : ℕ)
    (φ φ' : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    cup P p q (φ + φ') ψ = cup P p q φ ψ + cup P p q φ' ψ := by
  apply toAmbient_injective P (p + q)
  rw [map_add, toAmbient_cup, toAmbient_cup, toAmbient_cup, cochainCup_add_left]

theorem add_right (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ ψ' : relative P q) :
    cup P p q φ (ψ + ψ') = cup P p q φ ψ + cup P p q φ ψ' := by
  apply toAmbient_injective P (p + q)
  rw [map_add, toAmbient_cup, toAmbient_cup, toAmbient_cup, map_add, cochainCup_add_right]

theorem zero_left (P : TopPair.{0}) (p q : ℕ) (ψ : relative P q) : cup P p q 0 ψ = 0 := by
  apply toAmbient_injective P (p + q)
  rw [toAmbient_cup, map_zero, cochainCup_zero_left]

theorem zero_right (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) : cup P p q φ 0 = 0 := by
  apply toAmbient_injective P (p + q)
  rw [toAmbient_cup, map_zero, map_zero, cochainCup_zero_right]

theorem smul_left (P : TopPair.{0}) (p q : ℕ) (r : ZMod 2)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    cup P p q (r • φ) ψ = r • cup P p q φ ψ := by
  apply toAmbient_injective P (p + q)
  rw [map_smul, toAmbient_cup, toAmbient_cup, cochainCup_smul_left]

theorem smul_right (P : TopPair.{0}) (p q : ℕ) (r : ZMod 2)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    cup P p q φ (r • ψ) = r • cup P p q φ ψ := by
  apply toAmbient_injective P (p + q)
  rw [map_smul, toAmbient_cup, toAmbient_cup, map_smul, cochainCup_smul_right]

def differential (P : TopPair.{0}) (n : ℕ) : relative P n →ₗ[ZMod 2] relative P (n + 1) :=
  ((P.singularCochainComplex coeff (ZMod 2) coeff).d n (n + 1)).hom

theorem toAmbient_differential (P : TopPair.{0}) (n : ℕ) (ψ : relative P n) :
    toAmbient P (n + 1) (differential P n ψ) =
      cochainCoboundary (ZMod 2) P.fst n (toAmbient P n ψ) := by
  exact (congrArg (fun g => g.hom ψ)
    ((P.singularCochainComplexShortComplex coeff (ZMod 2) coeff).f.comm n (n + 1))).symm

theorem preserves_cocycles (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q)
    (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0) (hψ : differential P q ψ = 0) :
    differential P (p + q) (cup P p q φ ψ) = 0 := by
  apply toAmbient_injective P (p + q + 1)
  rw [toAmbient_differential, map_zero, toAmbient_cup]
  apply cochainCupZMod2_respects_cocycles p q _ _ hφ
  rw [← toAmbient_differential, hψ, map_zero]

def cast (P : TopPair.{0}) {m n : ℕ} (h : m = n) (ψ : relative P m) : relative P n := h ▸ ψ

theorem toAmbient_cast (P : TopPair.{0}) {m n : ℕ} (h : m = n) (ψ : relative P m) :
    toAmbient P n (cast P h ψ) = cochainCast h (toAmbient P m ψ) := by
  subst n
  rfl

theorem differential_cup (P : TopPair.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (ψ : relative P q) :
    differential P (p + q) (cup P p q φ ψ) =
      cast P (aw_degree_left_succ p q)
        (cup P (p + 1) q (cochainCoboundary (ZMod 2) P.fst p φ) ψ) +
      cast P (aw_degree_right_succ p q) (cup P p (q + 1) φ (differential P q ψ)) := by
  apply toAmbient_injective P (p + q + 1)
  rw [toAmbient_differential, toAmbient_cup, cochainCupZMod2_differential, map_add,
    toAmbient_cast, toAmbient_cast, toAmbient_cup, toAmbient_cup, toAmbient_differential]

theorem cast_zero (P : TopPair.{0}) {m n : ℕ} (h : m = n) : cast P h (0 : relative P m) = 0 := by
  subst n
  rfl

theorem cast_cast (P : TopPair.{0}) {m n : ℕ} (h : m = n) (ψ : relative P m) :
    cast P h.symm (cast P h ψ) = ψ := by
  subst n
  rfl

theorem boundary_left (P : TopPair.{0}) (m q : ℕ)
    (η : singularCochainGroup (ZMod 2) P.fst m) (ψ : relative P q)
    (hψ : differential P q ψ = 0) :
    cup P (m + 1) q (cochainCoboundary (ZMod 2) P.fst m η) ψ =
      cast P (aw_degree_left_succ m q).symm (differential P (m + q) (cup P m q η ψ)) := by
  have h := differential_cup P m q η ψ
  rw [hψ, zero_right, cast_zero, add_zero] at h
  simpa only [cast_cast] using congrArg (cast P (aw_degree_left_succ m q).symm) h.symm

theorem boundary_right (P : TopPair.{0}) (p m : ℕ)
    (φ : singularCochainGroup (ZMod 2) P.fst p) (hφ : cochainCoboundary (ZMod 2) P.fst p φ = 0)
    (η : relative P m) :
    cup P p (m + 1) φ (differential P m η) =
      cast P (aw_degree_right_succ p m).symm (differential P (p + m) (cup P p m φ η)) := by
  have h := differential_cup P p m φ η
  rw [hφ, zero_left, cast_zero, zero_add] at h
  simpa only [cast_cast] using congrArg (cast P (aw_degree_right_succ p m).symm) h.symm

end

end Finsler.RelativeCupCochain
