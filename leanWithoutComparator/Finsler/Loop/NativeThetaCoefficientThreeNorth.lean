module

public import Finsler.Loop.NorthRotationPrismLocalization

/-! The SAME original global Theta-cut coefficient is EXACTLY the
sum of THREE actual northern-quarter cohomology pairings on the
ORIGINAL triple cross fundamental source class. Nine actual quarter
terms, all pole/equator endpoints and the comparison boundary are
removed by proved original cochain identities, not local counts. -/
@[expose] public section
namespace Finsler.NativeThetaCoefficientThreeNorth
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.NativeFixedReturnRotationZero
open Finsler.NorthRotationPrismLocalization Finsler.NativeThetaCoefficientSixQuarters
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

private theorem sum_four {A : Type*} [AddCommMonoid A] (f : Fin 4 → A) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = f 0 + f 1 + f 2 + f 3
  abel

private theorem pairing_transport (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) (hφ : cochainCoboundary (ZMod 2) X j φ = 0)
    (z : homologyZMod2 X i) :
    (kroneckerMap X j).hom (cocycleClass X j φ hφ)
      ((eqToHom (congrArg (fun k => homologyZMod2 X k) h)).hom z) =
    (kroneckerMap X i).hom
      (cocycleClass X i (CochainDegreeTransport.pre X h φ) (CochainDegreeTransport.closed X h φ hφ)) z := by
  subst j
  simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply, CochainDegreeTransport.pre, Category.id_comp]

theorem coefficient_full_prism_any_point (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (Q : Sphere (m + 1)) {η ρ r : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      (((chains (parameters P)).iCycles (3 * m) ≫
        ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1)) ≫
        castCochain m Q hη hρ hρr hr).hom (sourceCycle m hm P) := by
  let φ := LocalizedThetaCutCoefficient.cochain m Q hη hρ hρr hr
  have hφ := LocalizedThetaCutCoefficient.closed m Q hη hρ hρr hr
  have he := LocalizedThetaCutCoefficient.coefficient_pairing m hm P v₀ Q hη hρ hρr hr
  have ht := pairing_transport (Loops (m + 1))
    (show 3 * m + 1 = (m + m) + (m + 1) by omega) φ hφ (MeridianRotationClasses.H1Theta m hm P v₀)
  have hp := sweep_pairing ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff)
    (3 * m) (castCochain m Q hη hρ hρr hr) (cast_closed m Q hη hρ hρr hr) (sourceCycle m hm P)
  rw [sourceCycle_class, NativeH1TripleMeridian.theta_original] at hp
  exact he.symm.trans (ht.trans hp)

theorem north_prisms_only (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    ((chains (parameters P)).iCycles (3 * m) ≫
      ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1)) ≫
      castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr =
    ∑ k : Fin 3, (chains (parameters P)).iCycles (3 * m) ≫ northCochain m P v₀ k hη hρ hρr hr := by
  let ψ := castCochain m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr
  have hc := cast_closed m (NorthMeridianEvaluationPoint.target P v₀) hη hρ hρr hr
  change (chains (Loops (m + 1))).d (3 * m + 2) (3 * m + 1) ≫ ψ = 0 at hc
  have hs := congrArg (fun a => a ≫ ψ) (NativeThetaVariableQuarters.original_twelve_split P v₀ (3 * m))
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, hc, comp_zero, add_zero] at hs
  change (chains (parameters P)).iCycles (3 * m) ≫
    ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = _
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : ((quarterHomotopy P v₀ k 1).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = 0 :=
    nonnorth_prism_zero m P v₀ k 0 hη hη2 hρ hρr hr
  have h2 : ((quarterHomotopy P v₀ k 2).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = 0 :=
    nonnorth_prism_zero m P v₀ k 1 hη hη2 hρ hρr hr
  have h3 : ((quarterHomotopy P v₀ k 3).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1) ≫ ψ = 0 :=
    nonnorth_prism_zero m P v₀ k 2 hη hη2 hρ hρr hr
  rw [sum_four]
  simp only [h1, h2, h3, comp_zero, add_zero]
  rfl

theorem coefficient_three_north_prisms (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      (∑ k : Fin 3, (chains (parameters P)).iCycles (3 * m) ≫ northCochain m P v₀ k hη hρ hρr hr).hom
        (sourceCycle m hm P) := by
  have hs := congrArg (fun f => f.hom (sourceCycle m hm P)) (north_prisms_only m P v₀ hη hη2 hρ hρr hr)
  exact (coefficient_full_prism_any_point m hm P v₀ _ hη hρ hρr hr).trans hs

theorem north_pairing (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    (kroneckerMap (parameters P) (3 * m)).hom
      (cocycleClass _ _ (northCochain m P v₀ k hη hρ hρr hr) (north_closed m P v₀ k hη hη2 hρ hρr hr))
      (BasedMeridianProducts.tripleSource m hm P) =
    ((chains (parameters P)).iCycles (3 * m) ≫ northCochain m P v₀ k hη hρ hρr hr).hom (sourceCycle m hm P) := by
  rw [kroneckerMap_cocycleClass, ← sourceCycle_class m hm P]
  exact kroneckerFunctional_apply (parameters P) (3 * m) _ _ (sourceCycle m hm P)

theorem coefficient_three_north_pairings (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
    ∑ k : Fin 3, (kroneckerMap (parameters P) (3 * m)).hom
      (cocycleClass _ _ (northCochain m P v₀ k hη hρ hρr hr) (north_closed m P v₀ k hη hη2 hρ hρr hr))
      (BasedMeridianProducts.tripleSource m hm P) := by
  rw [coefficient_three_north_prisms m hm P v₀ hη hη2 hρ hρr hr, ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact (north_pairing m hm P v₀ k hη hη2 hρ hρr hr).symm

end
end Finsler.NativeThetaCoefficientThreeNorth
