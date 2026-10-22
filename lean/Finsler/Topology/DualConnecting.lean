module

public import Finsler.Topology.RelativeKronecker
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! The cohomological connecting map of the dual of a short exact sequence of F₂ chain
complexes is dual to the homological connecting map under the Kronecker pairing:
evaluating δ a on the class of a cycle z equals evaluating a on ∂z. The proof chooses a
cochain extension, a lift of the coboundary, a chain lift and a boundary preimage, and
compares the two element-level descriptions of the connecting maps. For a topological
pair this identifies the relative universal-coefficient comparison of δ a with the
evaluation of a after the homological boundary. -/

@[expose] public section

namespace Finsler.DualConnecting

open CategoryTheory Limits Opposite

noncomputable section

set_option maxHeartbeats 400000

open Finsler.RelativeCohomology

abbrev dualF : (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  TauCeti.ChainComplex.linearYonedaFunctor (ZMod 2) coeff

variable {S : ShortComplex (ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ)}

theorem surj_g {c : ComplexShape ℕ}
    {T : ShortComplex (HomologicalComplex (ModuleCat.{0} (ZMod 2)) c)} (hT : T.ShortExact)
    (i : ℕ) : Function.Surjective (T.g.f i).hom := by
  have := hT.epi_g
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem exact_at {c : ComplexShape ℕ}
    {T : ShortComplex (HomologicalComplex (ModuleCat.{0} (ZMod 2)) c)} (hT : T.ShortExact)
    (i : ℕ) (x : T.X₂.X i) (hx : (T.g.f i).hom x = 0) : ∃ y, (T.f.f i).hom y = x := by
  have h := ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hT i).exact
  exact (ShortComplex.moduleCat_exact_iff _).mp h x hx

theorem cyclesMk_iCycles (K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (i j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (c : K.cycles i)
    (hc : (K.d i j).hom ((K.iCycles i).hom c) = 0) :
    K.cyclesMk ((K.iCycles i).hom c) j hj hc = c := by
  apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  exact K.i_cyclesMk _ j hj hc

theorem cocyclesMk_iCycles (K : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (i j : ℕ)
    (hj : (ComplexShape.up ℕ).next i = j) (c : K.cycles i)
    (hc : (K.d i j).hom ((K.iCycles i).hom c) = 0) :
    K.cyclesMk ((K.iCycles i).hom c) j hj hc = c := by
  apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  exact K.i_cyclesMk _ j hj hc

/-- The cohomological connecting map of the dual of a short exact sequence of chain complexes
is dual to the homological connecting map under the Kronecker pairing over F₂. -/
theorem kronecker_δ (hS : S.ShortExact) (hD : (S.op.map dualF).ShortExact) (n : ℕ)
    (a : (S.X₁.linearYonedaObj (ZMod 2) coeff).homology n) :
    TauCeti.ChainComplex.kronecker (ZMod 2) S.X₃ coeff (n + 1) ((hD.δ n (n + 1) rfl).hom a) =
      hS.δ (n + 1) n rfl ≫ TauCeti.ChainComplex.kronecker (ZMod 2) S.X₁ coeff n a := by
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((S.X₁.linearYonedaObj (ZMod 2) coeff).homologyπ n)).mp inferInstance a
  -- the cocycle and its extension
  have hφ₀ : ((S.X₁.linearYonedaObj (ZMod 2) coeff).d n (n + 1)).hom
      (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ) = 0 :=
    ConcreteCategory.congr_hom ((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles_d n (n + 1)) φ
  obtain ⟨x₂, hx₂⟩ := surj_g hD n (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ)
  have hgd : ((S.op.map dualF).g.f (n + 1)).hom
      (((S.op.map dualF).X₂.d n (n + 1)).hom x₂) = 0 := by
    have hcomm := ConcreteCategory.congr_hom (((S.op.map dualF).g.comm n (n + 1))) x₂
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    rw [← hcomm, hx₂]
    exact hφ₀
  obtain ⟨x₁, hx₁⟩ := exact_at hD (n + 1) _ hgd
  have hδD := hD.δ_apply n (n + 1) rfl
    (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ) hφ₀ x₂ hx₂ x₁ hx₁ (n + 2) (by simp)
  change (hD.δ n (n + 1) rfl).hom (((S.X₁.linearYonedaObj (ZMod 2) coeff).homologyπ n).hom
      ((S.X₁.linearYonedaObj (ZMod 2) coeff).cyclesMk
        (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ) (n + 1) (by simp) hφ₀)) =
    ((S.X₃.linearYonedaObj (ZMod 2) coeff).homologyπ (n + 1)).hom
      ((S.X₃.linearYonedaObj (ZMod 2) coeff).cyclesMk x₁ (n + 2) (by simp) _) at hδD
  rw [cocyclesMk_iCycles] at hδD
  obtain ⟨y, hy1, hy2⟩ : ∃ y : (S.X₃.linearYonedaObj (ZMod 2) coeff).cycles (n + 1),
      (hD.δ n (n + 1) rfl).hom (((S.X₁.linearYonedaObj (ZMod 2) coeff).homologyπ n).hom φ) =
        ((S.X₃.linearYonedaObj (ZMod 2) coeff).homologyπ (n + 1)).hom y ∧
      ConcreteCategory.hom (HomologicalComplex.iCycles (S.X₃.linearYonedaObj (ZMod 2) coeff)
        (n + 1)) y = x₁ :=
    ⟨_, hδD, (by exact (HomologicalComplex.i_cyclesMk (S.X₃.linearYonedaObj (ZMod 2) coeff)
      x₁ (n + 2) _ _))⟩
  rw [hy1]
  apply (cancel_epi (S.X₃.homologyπ (n + 1))).mp
  rw [TauCeti.ChainComplex.kronecker_homologyπ, hy2]
  ext c
  -- the homological connecting map on the class of c
  have hz₃ : (S.X₃.d (n + 1) n).hom ((S.X₃.iCycles (n + 1)).hom c) = 0 :=
    ConcreteCategory.congr_hom (S.X₃.iCycles_d (n + 1) n) c
  obtain ⟨z₂, hz₂⟩ := surj_g hS (n + 1) ((S.X₃.iCycles (n + 1)).hom c)
  have hgz : (S.g.f n).hom ((S.X₂.d (n + 1) n).hom z₂) = 0 := by
    have hcomm := ConcreteCategory.congr_hom (S.g.comm (n + 1) n) z₂
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    rw [← hcomm, hz₂]
    exact hz₃
  obtain ⟨z₁, hz₁⟩ := exact_at hS n _ hgz
  have hδS := hS.δ_apply (n + 1) n rfl ((S.X₃.iCycles (n + 1)).hom c) hz₃ z₂ hz₂ z₁ hz₁
    ((ComplexShape.down ℕ).next n) rfl
  rw [cyclesMk_iCycles] at hδS
  obtain ⟨w, hw1, hw2⟩ : ∃ w : S.X₁.cycles n,
      (hS.δ (n + 1) n rfl).hom ((S.X₃.homologyπ (n + 1)).hom c) = (S.X₁.homologyπ n).hom w ∧
      (S.X₁.iCycles n).hom w = z₁ :=
    ⟨_, hδS, by exact HomologicalComplex.i_cyclesMk S.X₁ z₁ _ _ _⟩
  have hk := ConcreteCategory.congr_hom
    (TauCeti.ChainComplex.kronecker_homologyπ (k := ZMod 2) (X := S.X₁) (Y := coeff) n φ) w
  have rhs : ModuleCat.Hom.hom (HomologicalComplex.homologyπ S.X₃ (n + 1) ≫ hS.δ (n + 1) n rfl ≫
      TauCeti.ChainComplex.kronecker (ZMod 2) S.X₁ coeff n
        ((ConcreteCategory.hom (HomologicalComplex.homologyπ
          (S.X₁.linearYonedaObj (ZMod 2) coeff) n)) φ)) c =
      ModuleCat.Hom.hom (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ :
        S.X₁.X n ⟶ coeff) z₁ := by
    calc _ = ModuleCat.Hom.hom (TauCeti.ChainComplex.kronecker (ZMod 2) S.X₁ coeff n
          ((ConcreteCategory.hom (HomologicalComplex.homologyπ
            (S.X₁.linearYonedaObj (ZMod 2) coeff) n)) φ))
          ((hS.δ (n + 1) n rfl).hom ((S.X₃.homologyπ (n + 1)).hom c)) := rfl
      _ = ModuleCat.Hom.hom (TauCeti.ChainComplex.kronecker (ZMod 2) S.X₁ coeff n
          ((ConcreteCategory.hom (HomologicalComplex.homologyπ
            (S.X₁.linearYonedaObj (ZMod 2) coeff) n)) φ)) ((S.X₁.homologyπ n).hom w) :=
          congrArg _ hw1
      _ = _ := hk
      _ = ModuleCat.Hom.hom (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ :
          S.X₁.X n ⟶ coeff) ((S.X₁.iCycles n).hom w) := rfl
      _ = _ := congrArg _ hw2
  have lhs : ModuleCat.Hom.hom (HomologicalComplex.iCycles S.X₃ (n + 1) ≫ x₁) c =
      ModuleCat.Hom.hom (((S.X₁.linearYonedaObj (ZMod 2) coeff).iCycles n).hom φ :
        S.X₁.X n ⟶ coeff) z₁ := by
    calc _ = ModuleCat.Hom.hom (x₁ : S.X₃.X (n + 1) ⟶ coeff)
          ((S.X₃.iCycles (n + 1)).hom c) := rfl
      _ = ModuleCat.Hom.hom (x₁ : S.X₃.X (n + 1) ⟶ coeff) ((S.g.f (n + 1)).hom z₂) :=
          congrArg _ hz₂.symm
      _ = ModuleCat.Hom.hom (((S.op.map dualF).f.f (n + 1)).hom x₁ : S.X₂.X (n + 1) ⟶ coeff)
          z₂ := rfl
      _ = ModuleCat.Hom.hom (((S.op.map dualF).X₂.d n (n + 1)).hom x₂ :
          S.X₂.X (n + 1) ⟶ coeff) z₂ :=
          congrArg (fun g : S.X₂.X (n + 1) ⟶ coeff => ModuleCat.Hom.hom g z₂) hx₁
      _ = ModuleCat.Hom.hom (x₂ : S.X₂.X n ⟶ coeff) ((S.X₂.d (n + 1) n).hom z₂) := rfl
      _ = ModuleCat.Hom.hom (x₂ : S.X₂.X n ⟶ coeff) ((S.f.f n).hom z₁) := congrArg _ hz₁.symm
      _ = ModuleCat.Hom.hom (((S.op.map dualF).g.f n).hom x₂ : S.X₁.X n ⟶ coeff) z₁ := rfl
      _ = _ := congrArg (fun g : S.X₁.X n ⟶ coeff => ModuleCat.Hom.hom g z₁) hx₂
  exact lhs.trans rhs.symm




/-- For a topological pair, the cohomological connecting map is dual to the homological one:
evaluating δ a on a relative class equals evaluating a on its homological boundary. -/
theorem pair_kronecker_δ (P : TopPair.{0}) (n : ℕ)
    (a : ((P.singularChainComplexShortComplex coeff).X₁.linearYonedaObj (ZMod 2) coeff).homology n) :
    TauCeti.ChainComplex.kronecker (ZMod 2) (P.singularChainComplex coeff) coeff (n + 1)
        ((P.singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl).hom a) =
      P.singularHomologyδ coeff (n + 1) n rfl ≫
        TauCeti.ChainComplex.kronecker (ZMod 2) (P.singularChainComplexShortComplex coeff).X₁
          coeff n a :=
  kronecker_δ (Finsler.Relative.chain_short_exact P coeff)
    (Finsler.RelativeCohomology.cochain_short_exact P) n a

/-- The same duality for the relative universal-coefficient comparison. -/
theorem comparison_δ (P : TopPair.{0}) (n : ℕ)
    (a : ((P.singularChainComplexShortComplex coeff).X₁.linearYonedaObj (ZMod 2) coeff).homology n) :
    Finsler.RelativeKronecker.comparison P (n + 1)
        ((P.singularCohomologyδ coeff (ZMod 2) coeff n (n + 1) rfl).hom a) =
      (TauCeti.ChainComplex.kronecker (ZMod 2) (P.singularChainComplexShortComplex coeff).X₁
          coeff n a).hom.comp (P.singularHomologyδ coeff (n + 1) n rfl).hom := by
  have h := congrArg (fun g => g.hom) (pair_kronecker_δ P n a)
  exact h

end

end Finsler.DualConnecting
