module

public import Finsler.Residual.FillAbs
public import Finsler.Topology.BasisResidual
public import Finsler.Geometry.OrdinaryGeodesic

/-! The filling bound `BasisResidual.FillRes.fill` of the ordinary Borel-model cohomology of the
pairs (t_a, M), and the main assertion (Claude, UF prototype).

Evaluation at the base point retracts t_a onto the constant loops M, so the relative-to-absolute
map H^i(t_a, M) → H^i(t_a) is injective in every degree (`pi_injective`: the connecting map
vanishes on restrictions). Given y on (t_b, M), b ≥ a + D, the restriction to t_a of its absolute
class is the restriction of a class x' of Λ (`UFFill.fill_abs`); x' vanishes on M, since it
restricts there through t_a, where the class comes from (t_a, M); so x' lifts to (Λ, M), and the
lift restricts to the cut of y by injectivity on t_a (`fill`). With the resonance bands
(`HRBridge.hr_of_finite`) this gives `FillRes F` for every metric with finitely many prime closed
geodesic images (`fillRes`), hence the main assertion (`reversible_sphere_assertion`). -/

@[expose] public section

namespace Finsler.UFFillRel

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.BorelCochain Finsler.BorelEvaluation

noncomputable section
set_option autoImplicit false

/-- With a retraction of the pair, the relative-to-absolute map is injective in every degree. -/
theorem pi_injective (P : TopPair.{0}) (r : P.fst ⟶ P.snd) (hr : P.map ≫ r = 𝟙 P.snd) (k : ℕ) :
    Function.Injective (P.singularCohomologyπ coeff (ZMod 2) coeff k).hom := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  cases k with
  | zero =>
    exact ((ModuleCat.mono_iff_injective _).mp inferInstance) (hb.trans (map_zero _).symm)
  | succ j =>
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (P.singularCohomology_exact_relative coeff (ZMod 2) coeff j (j + 1) rfl) b hb
    have hxr : x = (TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) P.map j).hom
        ((TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) r j).hom x) := by
      have h := TopCat.singularCohomologyMap_comp (R := coeff) (k := ZMod 2) (M := coeff) P.map r j
      rw [hr, TopCat.singularCohomologyMap_id] at h
      exact ConcreteCategory.congr_hom h x
    have hz := ConcreteCategory.congr_hom
      (P.singularCohomologyMap_comp_singularCohomologyδ coeff (ZMod 2) coeff j (j + 1) rfl)
      ((TopCat.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) r j).hom x)
    rw [← hx, hxr]
    exact hz

/-- An absolute class coming from the pair vanishes on the subspace. -/
theorem pull_relativeToPool (P : TopPair.{0}) (i : ℕ)
    (v : P.singularCohomology coeff (ZMod 2) coeff i) :
    (cohPullback P.map i).hom ((relativeToPool P i).hom v) = 0 := by
  refine (relative_lift_iff P i _).2 ⟨v, ?_⟩
  change _ = (cohomologyEquiv P.fst i) ((cohomologyEquiv P.fst i).symm
    ((P.singularCohomologyπ coeff (ZMod 2) coeff i).hom v))
  rw [LinearEquiv.apply_symm_apply]

variable (m : ℕ) (F : ReversibleMetric (m + 1))

/-- Evaluation at the base point retracts t_a onto the constant loops. -/
def retr (a : ℝ) : (levPair F a).fst ⟶ (levPair F a).snd :=
  levEval F a ≫ ConstantLoopModel.fromSphere (m + 1)

theorem retr_spec (a : ℝ) : (levPair F a).map ≫ retr m F a = 𝟙 _ := by
  have h : (levPair F a).map ≫ levEval F a = ConstantLoopModel.toSphere (m + 1) := by
    ext u : 1
    rfl
  have h2 := congrArg (· ≫ ConstantLoopModel.fromSphere (m + 1)) h
  simp only at h2
  exact (Category.assoc _ _ _).symm.trans (h2.trans (ConstantLoopModel.to_from (m + 1)))

/-- The absolute class of an ordinary class of (t_a, M) determines it, in every degree. -/
theorem toAbsLev_injective_all (a : ℝ) (i : ℕ) : Function.Injective (HRBridge.toAbsLev m F a i) := by
  intro y y' h
  apply (Finsler.BorelComparison.ordinaryEquiv (levPair F a) (revPair F a) (revPair_sq F a) i).injective
  apply pi_injective (levPair F a) (retr m F a) (retr_spec m F a) i
  apply (cohomologyEquiv (levPair F a).fst i).symm.injective
  exact h

theorem res_forget (a : ℝ) :
    TopPair.Hom.fst (resPair F a) ≫ FullLoopModel.forget (m + 1) = HRBridge.inclE m F a := by
  ext u : 1
  rfl

theorem consts_square (a : ℝ) :
    (levPair F a).map ≫ TopPair.Hom.fst (resPair F a) = (fullPair (m + 1)).map := by
  ext u : 1
  rfl

/-- **The filling bound** of `BasisResidual.FillRes` with finitely many prime closed geodesic
images, in every degree. -/
theorem fill (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a b : ℝ) (hab : a ≤ b), 1 ≤ a → a + D ≤ b → ∀ (i : ℕ)
      (y : H (levComplex F b) i),
      ∃ x : H (fullComplex (m + 1)) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y := by
  obtain ⟨D, hD, hfill⟩ := UFFill.fill_abs m F hm hfin
  refine ⟨D, hD, fun a b hab ha hb i y => ?_⟩
  obtain ⟨x', hx'⟩ := hfill a b (by linarith) hab hb i (HRBridge.toAbsLev m F b i y)
  -- the class on the full pair's ambient space
  have hwa : (cohPullback (TopPair.Hom.fst (resPair F a)) i).hom
      ((cohPullback (FullLoopModel.forget (m + 1)) i).hom x') =
        HRBridge.toAbsLev m F a i (Hmap (cutHom F hab) i y) := by
    rw [UFWindow.toAbsLev_cut, ← hx', ← Finsler.Cup.pullback_comp, res_forget]
    rfl
  have hw0 : (cohPullback (fullPair (m + 1)).map i).hom
      ((cohPullback (FullLoopModel.forget (m + 1)) i).hom x') = 0 := by
    have h1 := Finsler.Cup.pullback_comp (levPair F a).map (TopPair.Hom.fst (resPair F a)) i
      ((cohPullback (FullLoopModel.forget (m + 1)) i).hom x')
    rw [consts_square, hwa] at h1
    exact h1.trans (pull_relativeToPool (levPair F a) i _)
  obtain ⟨v, hv⟩ := relative_lift (fullPair (m + 1)) i _ hw0
  refine ⟨(Finsler.BorelComparison.ordinaryEquiv (fullPair (m + 1)) (revFullPair (m + 1))
    (revFullPair_sq (m + 1)) i).symm v, ?_⟩
  apply toAbsLev_injective_all m F a i
  rw [← hwa, HRBridge.toAbsLev, Finsler.BorelComparison.ordinaryEquiv_natural (revPair_sq F a)
    (revFullPair_sq (m + 1)) (resPair F a) (resPair_equivariant F a) i _,
    LinearEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom (relative_to_absolute_natural (resPair F a) i) v
  refine hn.trans ?_
  change (cohPullback (TopPair.Hom.fst (resPair F a)) i).hom
    ((cohomologyEquiv (fullPair (m + 1)).fst i).symm
      (((fullPair (m + 1)).singularCohomologyπ coeff (ZMod 2) coeff i).hom v)) = _
  rw [hv]
  exact congrArg _ ((cohomologyEquiv (fullPair (m + 1)).fst i).symm_apply_apply _)

/-- **`FillRes` with finitely many prime closed geodesic images**, n = m + 1 ≥ 3. -/
theorem fillRes (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    Nonempty (Finsler.BasisResidual.FillRes F) := by
  obtain ⟨α, c₁, a₀, hα, hc₁, -, hinj, hzero⟩ := HRBridge.hr_of_finite m F hm hfin
  obtain ⟨D, hD, hfill⟩ := fill m F hm hfin
  exact ⟨{
    α := α
    c₁ := c₁
    D := D
    a₀ := max a₀ 1
    α_pos := hα
    c₁_nonneg := hc₁
    D_nonneg := hD
    a₀_pos := lt_of_lt_of_le one_pos (le_max_right _ _)
    fill := fun a b hab ha hb i y => hfill a b hab ((le_max_right _ _).trans ha) hb i y
    res_inj := fun a ha i h1 h2 => hinj a ((le_max_left _ _).trans ha) i h1 h2
    res_zero := fun a ha i h1 x => hzero a ((le_max_left _ _).trans ha) i h1 x }⟩

/-- **The main assertion**: every reversible Finsler metric on S^n, n ≥ 3, has
infinitely many prime closed geodesic images. -/
theorem reversible_sphere_assertion : Finsler.Geodesics.ReversibleSphereAssertion :=
  Finsler.BasisResidual.assertion_of_fillRes fun n hn F hfin => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact fillRes m F (by omega) hfin

/-- **The main assertion in ordinary coordinates**: the same infinitude for the closed geodesics
of the coordinate Euler–Lagrange equation (`OrdinaryGeodesics.assertion_iff`). -/
theorem ordinary_sphere_assertion : Finsler.OrdinaryGeodesics.ReversibleSphereAssertion :=
  Finsler.OrdinaryGeodesics.assertion_iff.mp reversible_sphere_assertion

end

end Finsler.UFFillRel
