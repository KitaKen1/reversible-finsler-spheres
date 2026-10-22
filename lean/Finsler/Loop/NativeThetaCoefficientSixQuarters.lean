module

public import Finsler.Loop.NativeThetaVariableQuarters

/-! Express the SAME original global Theta-cut scalar as the sum
of the SIX actual remaining variable-quarter prism evaluations.
The source is a genuine cycle representing the ORIGINAL triple
cross fundamental class. No nonzero Theta or local count is assumed. -/
@[expose] public section
namespace Finsler.NativeThetaCoefficientSixQuarters
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.NativeFixedReturnRotationZero
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem sweep_pairing {X Y : TopCat.{0}} {f : X ⟶ Y} (H : _root_.Homotopy
    (SupportedCapNaturality.push f) (SupportedCapNaturality.push f)) (q : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (q + 1))
    (hφ : cochainCoboundary (ZMod 2) Y (q + 1) φ = 0) (c : (chains X).cycles q) :
    (kroneckerMap Y (q + 1)).hom (cocycleClass Y (q + 1) φ hφ)
      ((SelfHomotopySweep.homology H q).hom (((chains X).homologyπ q).hom c)) =
      (((chains X).iCycles q ≫ SelfHomotopySweep.component H q) ≫ φ).hom c := by
  have he := ConcreteCategory.congr_hom (SelfHomotopySweep.homologyπ_homology H q) c
  change (SelfHomotopySweep.homology H q).hom (((chains X).homologyπ q).hom c) =
    ((chains Y).homologyπ (q + 1)).hom ((SelfHomotopySweep.cycles H q).hom c) at he
  rw [he, kroneckerMap_cocycleClass]
  have hk := kroneckerFunctional_apply Y (q + 1) φ hφ ((SelfHomotopySweep.cycles H q).hom c)
  have hi := ConcreteCategory.congr_hom (SelfHomotopySweep.cycles_i H q) c
  exact hk.trans (congrArg φ.hom hi)

def sourceCycle (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) : (chains (parameters P)).cycles (3 * m) :=
  Function.surjInv ((ModuleCat.epi_iff_surjective ((chains (parameters P)).homologyπ (3 * m))).mp inferInstance)
    (BasedMeridianProducts.tripleSource m hm P)

theorem sourceCycle_class (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) :
    ((chains (parameters P)).homologyπ (3 * m)).hom (sourceCycle m hm P) =
      BasedMeridianProducts.tripleSource m hm P :=
  Function.surjInv_eq ((ModuleCat.epi_iff_surjective ((chains (parameters P)).homologyπ (3 * m))).mp inferInstance) _

private theorem pairing_transport (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) (hφ : cochainCoboundary (ZMod 2) X j φ = 0)
    (z : homologyZMod2 X i) :
    (kroneckerMap X j).hom (cocycleClass X j φ hφ)
      ((eqToHom (congrArg (fun k => homologyZMod2 X k) h)).hom z) =
    (kroneckerMap X i).hom
      (cocycleClass X i (CochainDegreeTransport.pre X h φ) (CochainDegreeTransport.closed X h φ hφ)) z := by
  subst j
  simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply,
    CochainDegreeTransport.pre, Category.id_comp]

theorem coefficient_full_prism (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      (((chains (parameters P)).iCycles (3 * m) ≫
        ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1)) ≫
        castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr).hom (sourceCycle m hm P) := by
  let Q := OppositeMeridianEvaluationPoint.target v₀
  let φ := LocalizedThetaCutCoefficient.cochain m Q hη hρ hρr hr
  have hφ := LocalizedThetaCutCoefficient.closed m Q hη hρ hρr hr
  have he := LocalizedThetaCutCoefficient.coefficient_pairing m hm P v₀ Q hη hρ hρr hr
  have ht := pairing_transport (Loops (m + 1))
    (show 3 * m + 1 = (m + m) + (m + 1) by omega) φ hφ (MeridianRotationClasses.H1Theta m hm P v₀)
  have hs := NativeH1TripleMeridian.theta_original m hm P v₀
  have hsource := sourceCycle_class m hm P
  have hp := sweep_pairing ((NativeH1TripleMeridian.rotationHomotopy P v₀).toSSet.chainComplexMap coeff)
    (3 * m) (castCochain m Q hη hρ hρr hr) (cast_closed m Q hη hρ hρr hr) (sourceCycle m hm P)
  rw [hsource, hs] at hp
  exact he.symm.trans (ht.trans hp)

theorem coefficient_six_quarters (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {η ρ r : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      (∑ k : Fin 3, ∑ q : Fin 2,
        ((chains (parameters P)).iCycles (3 * m) ≫
          ((quarterHomotopy P v₀ k ⟨q.val, by omega⟩).toSSet.chainComplexMap coeff).hom (3 * m) (3 * m + 1)) ≫
            castCochain m (OppositeMeridianEvaluationPoint.target v₀) hη hρ hρr hr).hom (sourceCycle m hm P) := by
  have hs := congrArg (fun f => f.hom (sourceCycle m hm P))
    (NativeThetaVariableQuarters.variable_quarters_only m P v₀ hη hη1 hρ hρr hr)
  exact (coefficient_full_prism m hm P v₀ hη hρ hρr hr).trans hs

end
end Finsler.NativeThetaCoefficientSixQuarters
