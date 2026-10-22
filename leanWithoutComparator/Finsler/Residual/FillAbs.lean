module

public import Finsler.Residual.UFLow

/-! The uniform filling in absolute cohomology of energy sublevels (Claude, UF prototype).

The length sublevels and the energy sublevels have the same homology (`homologyIso`), so a class of
t_a dying in Λ dies in t_{a + D} (`energy_kill`, from `UFLow.uf_all`). Dually over F₂: the restriction
to t_a of a class of t_b, b ≥ a + D, annihilates the kernel of H_i(t_a) → H_i(Λ), hence is the
restriction of a class of Λ (`range_dualMap_eq_dualAnnihilator_ker`, Kronecker duality) — `fill_abs`. -/

@[expose] public section

namespace Finsler.UFFill

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (F : ReversibleMetric (m + 1))

/-- **Uniform filling on energy sublevels** (homology). -/
theorem energy_kill (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a b : ℝ) (_ha : 0 < a) (hab : a ≤ b), a + D ≤ b → ∀ (i : ℕ)
      (z : homologyZMod2 (TopCat.of ↥(lev F a)) i),
      (homologyPushZMod2 (HRBridge.inclE m F a) i).hom z = 0 →
        (homologyPushZMod2 (TopPair.Hom.fst (cutPair F hab)) i).hom z = 0 := by
  obtain ⟨D, hD, hUF⟩ := UFLow.uf_all F hm hfin
  refine ⟨D, hD, fun a b ha hab hb i z hz => ?_⟩
  set z' := (homologyPushZMod2 (toLength F a ha) i).hom z with hz'
  have hz'n : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) i).hom z' = 0 := by
    rw [hz', push_comp_apply]
    exact hz
  have hk := hUF a ha i z' hz'n (by linarith)
  have hk' := UFBLF.enl_zero_mono m F (by linarith : a ≤ a + D) hb i z' hk
  -- back to the energy sublevel
  have hinv := ConcreteCategory.congr_hom (energy_homology_inverse F a ha i) z
  have hinv' : (homologyPushZMod2 (toEnergy F a) i).hom z' = z := by
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at hinv
    exact hinv
  have hsq : toEnergy F a ≫ TopPair.Hom.fst (cutPair F hab) =
      LengthFilteredLoopRotation.cut F hab ≫ toEnergy F b := by
    ext u : 1
    rfl
  rw [← hinv']
  have h1 := push_comp_apply (toEnergy F a) (TopPair.Hom.fst (cutPair F hab)) i z'
  rw [hsq] at h1
  have h2 := push_comp_apply (LengthFilteredLoopRotation.cut F hab) (toEnergy F b) i z'
  have h3 : (homologyPushZMod2 (toEnergy F b) i).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.cut F hab) i).hom z') = 0 := by
    rw [show (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hab) i).hom z' = 0 from hk', map_zero]
  exact h1.trans (h2.symm.trans h3)

/-- **Uniform filling in absolute cohomology** of energy sublevels. -/
theorem fill_abs (hm : 2 ≤ m) (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a b : ℝ) (_ha : 0 < a) (hab : a ≤ b), a + D ≤ b → ∀ (i : ℕ)
      (ψ : cohomologyZMod2 (TopCat.of ↥(lev F b)) i),
      ∃ x : cohomologyZMod2 (Loops (m + 1)) i,
        (cohPullback (HRBridge.inclE m F a) i).hom x =
          (cohPullback (TopPair.Hom.fst (cutPair F hab)) i).hom ψ := by
  obtain ⟨D, hD, hk⟩ := energy_kill m F hm hfin
  refine ⟨D, hD, fun a b ha hab hb i ψ => ?_⟩
  set f := (homologyPushZMod2 (HRBridge.inclE m F a) i).hom with hf
  set φ := (kroneckerMap (TopCat.of ↥(lev F a)) i).hom
    ((cohPullback (TopPair.Hom.fst (cutPair F hab)) i).hom ψ) with hφ
  have hann : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    have hn := kroneckerMap_naturality_apply (TopPair.Hom.fst (cutPair F hab)) i ψ
    have h1 := congrArg (fun φ' => φ' z) hn
    simp only [LinearMap.comp_apply] at h1
    rw [hφ]
    refine h1.trans ?_
    exact (congrArg ((kroneckerMap _ i).hom ψ) (hk a b ha hab hb i z hz)).trans (map_zero _)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  obtain ⟨χ, hχ⟩ := hann
  obtain ⟨x, hx⟩ := (kroneckerMap_bijective (Loops (m + 1)) i).2 χ
  refine ⟨x, (kroneckerMap_bijective (TopCat.of ↥(lev F a)) i).1 ?_⟩
  have hn := kroneckerMap_naturality_apply (HRBridge.inclE m F a) i x
  refine hn.trans ?_
  rw [hx]
  exact hχ

end

end Finsler.UFFill
