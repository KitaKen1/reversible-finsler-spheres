module

public import Finsler.Topology.RelativeKronecker

/-! Compute the actual connecting morphism using cochain extensions.
The product formula is over F₂, so the graded sign is trivial. -/

@[expose] public section

namespace Finsler.CupBoundary

open CategoryTheory SphereOddDegree Finsler.CochainComparison
open SphereOddDegree.AlexanderWhitney

noncomputable section

def boundary (P : TopPair.{0}) (n : ℕ) :
    cohomologyZMod2 P.snd n →ₗ[ZMod 2] RelativeCup.cohomology P (n + 1) :=
  (P.singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl).hom.comp
    (cohomologyEquiv P.snd n).toLinearMap

theorem exists_extension (P : TopPair.{0}) (n : ℕ)
    (χ : singularCochainGroup (ZMod 2) P.snd n) :
    ∃ η : singularCochainGroup (ZMod 2) P.fst n, cochainPullback P.map n η = χ := by
  have : Epi (RelativeCupCochain.sequence P n).g :=
    (RelativeCupCochain.degree_short_exact P n).epi_g
  exact (ModuleCat.epi_iff_surjective (RelativeCupCochain.sequence P n).g).mp inferInstance χ

theorem exists_boundary_lift (P : TopPair.{0}) (n : ℕ)
    (χ : singularCochainGroup (ZMod 2) P.snd n) (hχ : cochainCoboundary (ZMod 2) P.snd n χ = 0)
    (η : singularCochainGroup (ZMod 2) P.fst n) (hη : cochainPullback P.map n η = χ) :
    ∃ ψ : RelativeCupCochain.relative P (n + 1),
      RelativeCupCochain.toAmbient P (n + 1) ψ = cochainCoboundary (ZMod 2) P.fst n η := by
  apply RelativeCupCochain.exists_lift
  rw [← cochainPullback_cochainCoboundary, hη, hχ]

theorem lift_closed (P : TopPair.{0}) (n : ℕ)
    (η : singularCochainGroup (ZMod 2) P.fst n) (ψ : RelativeCupCochain.relative P (n + 1))
    (hψ : RelativeCupCochain.toAmbient P (n + 1) ψ = cochainCoboundary (ZMod 2) P.fst n η) :
    RelativeCupCochain.differential P (n + 1) ψ = 0 := by
  apply RelativeCupCochain.toAmbient_injective P (n + 2)
  rw [RelativeCupCochain.toAmbient_differential, map_zero, hψ]
  exact cochainCoboundary_cochainCoboundary P.fst n η

theorem boundary_classOf (P : TopPair.{0}) (n : ℕ)
    (χ : singularCochainGroup (ZMod 2) P.snd n) (hχ : cochainCoboundary (ZMod 2) P.snd n χ = 0)
    (η : singularCochainGroup (ZMod 2) P.fst n) (hη : cochainPullback P.map n η = χ)
    (ψ : RelativeCupCochain.relative P (n + 1))
    (hψ : RelativeCupCochain.toAmbient P (n + 1) ψ = cochainCoboundary (ZMod 2) P.fst n η) :
    boundary P n (CochainClass.classOf (cochainCxZMod2 P.snd) n χ hχ) =
      CochainClass.classOf (RelativeCup.cx P) (n + 1) ψ (lift_closed P n η ψ hψ) := by
  have hc := CochainClass.classOf_map (cochainCxZMod2 P.snd) (cochainIso P.snd).hom n χ hχ hχ
  have hd := (RelativeCohomology.cochain_short_exact P).δ_apply n (n + 1) rfl
    χ hχ η hη ψ hψ (n + 2) (CochainClass.next_eq (n + 1))
  exact (congrArg (P.singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl).hom hc).trans hd

def castClass (P : TopPair.{0}) {m n : ℕ} (h : m = n)
    (a : RelativeCup.cohomology P m) : RelativeCup.cohomology P n := h ▸ a

theorem castClass_classOf (P : TopPair.{0}) {m n : ℕ} (h : m = n)
    (ψ : RelativeCupCochain.relative P m) (hψ : RelativeCupCochain.differential P m ψ = 0)
    (hc : RelativeCupCochain.differential P n (RelativeCupCochain.cast P h ψ) = 0) :
    castClass P h (CochainClass.classOf (RelativeCup.cx P) m ψ hψ) =
      CochainClass.classOf (RelativeCup.cx P) n (RelativeCupCochain.cast P h ψ) hc := by
  subst n
  rfl

theorem cup_lift_image (P : TopPair.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) P.fst p) (hα : cochainCoboundary (ZMod 2) P.fst p α = 0)
    (η : singularCochainGroup (ZMod 2) P.fst q) (ψ : RelativeCupCochain.relative P (q + 1))
    (hψ : RelativeCupCochain.toAmbient P (q + 1) ψ = cochainCoboundary (ZMod 2) P.fst q η) :
    RelativeCupCochain.toAmbient P (p + q + 1)
        (RelativeCupCochain.cast P (aw_degree_right_succ p q)
          (RelativeCupCochain.cup P p (q + 1) α ψ)) =
      cochainCoboundary (ZMod 2) P.fst (p + q) (cochainCup p q α η) := by
  rw [RelativeCupCochain.toAmbient_cast, RelativeCupCochain.toAmbient_cup, hψ]
  exact (cochainCupZMod2_coboundary_right p q α η hα).symm

theorem boundary_cup_classOf (P : TopPair.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) P.fst p) (hα : cochainCoboundary (ZMod 2) P.fst p α = 0)
    (χ : singularCochainGroup (ZMod 2) P.snd q) (hχ : cochainCoboundary (ZMod 2) P.snd q χ = 0)
    (η : singularCochainGroup (ZMod 2) P.fst q) (hη : cochainPullback P.map q η = χ)
    (ψ : RelativeCupCochain.relative P (q + 1))
    (hψ : RelativeCupCochain.toAmbient P (q + 1) ψ = cochainCoboundary (ZMod 2) P.fst q η) :
    boundary P (p + q)
        (cupZMod2 ((cohPullback P.map p).hom (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα))
          (CochainClass.classOf (cochainCxZMod2 P.snd) q χ hχ)) =
      castClass P (aw_degree_right_succ p q)
        (RelativeCup.cup P p (q + 1) (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα)
          (CochainClass.classOf (RelativeCup.cx P) (q + 1) ψ (lift_closed P q η ψ hψ))) := by
  have hαr := cochainPullback_cocycle P.map p α hα
  have hprod := cochainCupZMod2_respects_cocycles p q (cochainPullback P.map p α) χ hαr hχ
  have hηprod : cochainPullback P.map (p + q) (cochainCup p q α η) =
      cochainCup p q (cochainPullback P.map p α) χ := by
    rw [cochainCup_naturality, hη]
  have hd := boundary_classOf P (p + q) (cochainCup p q (cochainPullback P.map p α) χ)
    hprod (cochainCup p q α η) hηprod
    (RelativeCupCochain.cast P (aw_degree_right_succ p q) (RelativeCupCochain.cup P p (q + 1) α ψ))
    (cup_lift_image P p q α hα η ψ hψ)
  have hc := RelativeCup.cup_mk P p (q + 1) α hα ψ (lift_closed P q η ψ hψ)
  have hh := RelativeCupCochain.preserves_cocycles P p (q + 1) α ψ hα (lift_closed P q η ψ hψ)
  have hcast := castClass_classOf P (aw_degree_right_succ p q)
    (RelativeCupCochain.cup P p (q + 1) α ψ) hh
    (lift_closed P (p + q) (cochainCup p q α η) _ (cup_lift_image P p q α hα η ψ hψ))
  have hpull := cohPullback_cocycleClass P.map p α hα
  have hcup := cupZMod2_mk (cochainPullback P.map p α) hαr χ hχ
  have hfirst := (congrArg (fun x => cupZMod2 x (cocycleClass P.snd q χ hχ)) hpull).trans hcup
  exact (congrArg (boundary P (p + q)) hfirst).trans
    (hd.trans (hcast.symm.trans (congrArg (castClass P (aw_degree_right_succ p q)) hc).symm))

/-- The actual module law for the connecting morphism over F₂. Neither a
cup-compatible boundary nor cochain extensions are assumed in the statement. -/
theorem boundary_cup (P : TopPair.{0}) (p q : ℕ)
    (a : cohomologyZMod2 P.fst p) (b : cohomologyZMod2 P.snd q) :
    boundary P (p + q) (cupZMod2 ((cohPullback P.map p).hom a) b) =
      castClass P (aw_degree_right_succ p q)
        (RelativeCup.cup P p (q + 1) a (boundary P q b)) := by
  obtain ⟨α, hα, rfl⟩ := cocycleClass_surjective P.fst p a
  obtain ⟨χ, hχ, rfl⟩ := cocycleClass_surjective P.snd q b
  obtain ⟨η, hη⟩ := exists_extension P q χ
  obtain ⟨ψ, hψ⟩ := exists_boundary_lift P q χ hχ η hη
  have hd := boundary_classOf P q χ hχ η hη ψ hψ
  exact (boundary_cup_classOf P p q α hα χ hχ η hη ψ hψ).trans
    (congrArg (fun x => castClass P (aw_degree_right_succ p q)
      (RelativeCup.cup P p (q + 1) (cocycleClass P.fst p α hα) x)) hd.symm)

theorem boundary_natural {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (b : cohomologyZMod2 Q.snd n) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f (n + 1)).hom
        (boundary Q n b) =
      boundary P n ((cohPullback (TopPair.Hom.snd f) n).hom b) := by
  have h := ConcreteCategory.congr_hom
    (RelativeCohomology.boundary_natural f n (n + 1) rfl) (cohomologyEquiv Q.snd n b)
  exact h.symm.trans (congrArg (P.singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl).hom
    (cohomology_natural_apply (TopPair.Hom.snd f) n b).symm)

theorem boundary_restriction_zero (P : TopPair.{0}) (n : ℕ) (a : cohomologyZMod2 P.fst n) :
    boundary P n ((cohPullback P.map n).hom a) = 0 := by
  have h := ConcreteCategory.congr_hom
    (P.singularCohomologyMap_comp_singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl)
    (cohomologyEquiv P.fst n a)
  exact (congrArg (P.singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl).hom
    (cohomology_natural_apply P.map n a)).trans h

theorem relativeToPool_boundary_zero (P : TopPair.{0}) (n : ℕ)
    (b : cohomologyZMod2 P.snd n) : (relativeToPool P (n + 1)).hom (boundary P n b) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((RelativeCohomology.cochain_short_exact P).δ_comp n (n + 1) rfl)
    (cohomologyEquiv P.snd n b)
  change (cohomologyEquiv P.fst (n + 1)).symm
    ((P.singularCohomologyπ coeff (ZMod 2) coeff (n + 1)).hom (boundary P n b)) = 0
  change (P.singularCohomologyπ coeff (ZMod 2) coeff (n + 1)).hom (boundary P n b) = 0 at h
  rw [h, map_zero]

/-- Exactness at subspace cohomology, expressed using Lean Pool's absolute
classes and the actual native relative connecting map. -/
theorem boundary_zero_iff_lift (P : TopPair.{0}) (n : ℕ) (b : cohomologyZMod2 P.snd n) :
    boundary P n b = 0 ↔ ∃ a : cohomologyZMod2 P.fst n, (cohPullback P.map n).hom a = b := by
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (P.singularCohomology_exact_subspace coeff (ZMod 2) coeff n (n + 1) rfl)
      (cohomologyEquiv P.snd n b) hb
    refine ⟨(cohomologyEquiv P.fst n).symm a, ?_⟩
    apply (cohomologyEquiv P.snd n).injective
    have h := cohomology_natural_apply P.map n ((cohomologyEquiv P.fst n).symm a)
    change _ = (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) P.map n).hom
      ((cohomologyEquiv P.fst n) ((cohomologyEquiv P.fst n).symm a)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.trans ha
  · rintro ⟨a, rfl⟩
    exact boundary_restriction_zero P n a

end

end Finsler.CupBoundary
