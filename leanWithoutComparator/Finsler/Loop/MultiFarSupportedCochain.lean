module

public import Finsler.Loop.MultiFarSupportedCap
public import Finsler.Loop.SupportedExactThomCap
public import Finsler.Loop.SupportedCutCochainCarrierZero

/-! Cochain identities and whole-parent support for the actual
separate-far-set cap. The near output can be defined ONLY on the genuine
common near set. Its zero extension is not assumed closed. -/
@[expose] public section
namespace Finsler.MultiFarSupportedCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MultiFarSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {ι : Type*} (A : ι → Set X) (B : Set X)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hc : (⋃ i, A i) ∪ B = Set.univ)

theorem coboundary_supported (p : ℕ) (κ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p κ = 0) :
    ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) (p + 1)
      (cochainCoboundary (ZMod 2) X p κ) = 0 :=
  fun i => SupportedExactThomCap.coboundary_supported X (A i) p κ (hs i)

theorem cut_eq (p q N : ℕ) (hN : p + q = N)
    (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0)
    (hψ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p ψ = 0) (he : φ = ψ) :
    cut X A B hA hB hc p q N hN φ hφ = cut X A B hA hB hc p q N hN ψ hψ := by
  cases he
  rfl

theorem cut_sub (p q N : ℕ) (hN : p + q = N)
    (φ ψ : singularCochainGroup (ZMod 2) X p)
    (hφ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p φ = 0)
    (hψ : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p ψ = 0)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p (φ - ψ) = 0) :
    cut X A B hA hB hc p q N hN (φ - ψ) hs =
      cut X A B hA hB hc p q N hN φ hφ - cut X A B hA hB hc p q N hN ψ hψ := by
  have : Mono ((push (SupportedCap.subspaceMap X B)).f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono ((push (SupportedCap.subspaceMap X B)).f q)).mp
  rw [Preadditive.sub_comp, cut_inclusion, cut_inclusion, cut_inclusion,
    SupportedCapCochain.absolute_sub, Preadditive.comp_sub]

theorem cut_boundary (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)
    (hθ : cochainCoboundary (ZMod 2) X p θ = 0) :
    cut X A B hA hB hc p (q + 1) (N + 1) (by omega) θ hs ≫ (chains (TopCat.of B)).d (q + 1) q =
      (chains X).d (N + 1) N ≫ cut X A B hA hB hc p q N hN θ hs := by
  let j := push (SupportedCap.subspaceMap X B)
  have : Mono (j.f q) := SupportedCap.subspacePush_mono X B q
  apply (cancel_mono (j.f q)).mp
  calc
    _ = cut X A B hA hB hc p (q + 1) (N + 1) (by omega) θ hs ≫
        (j.f (q + 1) ≫ (chains X).d (q + 1) q) := by
      rw [Category.assoc, ← HomologicalComplex.Hom.comm]
    _ = (TauCeti.singularSmallApprox coeff (cover X A B)).f (N + 1) ≫
        (absoluteChain X p (q + 1) (N + 1) (by omega) θ ≫ (chains X).d (q + 1) q) := by
      rw [← Category.assoc, cut_inclusion, Category.assoc]
    _ = (TauCeti.singularSmallApprox coeff (cover X A B)).f (N + 1) ≫
        ((chains X).d (N + 1) N ≫ absoluteChain X p q N hN θ) := by
      rw [RelativeCapBoundary.absolute_chain_boundary X p q N hN θ hθ]
    _ = _ := by
      rw [← Category.assoc, HomologicalComplex.Hom.comm, Category.assoc,
        ← cut_inclusion, ← Category.assoc]

theorem scalar_closed (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)
    (hθ : cochainCoboundary (ZMod 2) X p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X N (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  change (chains X).d (N + 1) N ≫ (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0
  change (chains (TopCat.of B)).d (q + 1) q ≫ ψ = 0 at hψ
  rw [← Category.assoc, ← cut_boundary X A B hA hB hc p q N hN θ hs hθ, Category.assoc, hψ, comp_zero]

theorem correction_boundary (p q N : ℕ) (hN : p + q = N)
    (κ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p κ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X N (cut X A B hA hB hc p q N hN κ hs ≫ ψ) =
      cut X A B hA hB hc (p + 1) q (N + 1) (by omega)
        (cochainCoboundary (ZMod 2) X p κ) (coboundary_supported X A p κ hs) ≫ ψ := by
  have he := congrArg (fun f => f ≫ ψ)
    (cut_coboundary X A B hA hB hc p q N hN κ hs (coboundary_supported X A p κ hs))
  change (chains (TopCat.of B)).d (q + 1) q ≫ ψ = 0 at hψ
  simp only [Category.assoc, hψ, comp_zero, Preadditive.sub_comp] at he
  exact sub_eq_zero.mp he.symm

theorem zero_of_supported (C : Set X) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0)
    {c : coeff ⟶ (chains X).X N} (hcar : c ∈ supported X (fun _ : Unit => C) N) :
    c ≫ cut X A B hA hB hc p q N hN θ hs ≫ ψ = 0 := by
  let Ψ := TubeCochainExtension.extend X B q ψ
  have hzero : cochainPullback (SupportedCap.subspaceMap X C) q Ψ = 0 :=
    TubeExtensionPullback.pullback_zero (SupportedCap.subspaceMap X C) B q ψ hψ
  have happrox := approximation_preserves (cover X A B) (fun _ : Unit => C) hcar
  have hcap := SmallCapCarrier.cap_preserves (fun _ : Unit => C) p q N hN θ happrox
  have hz := CarrierCochainZero.carried_zero (fun _ : Unit => C) q Ψ (fun _ => hzero) hcap
  have he : ψ = (push (SupportedCap.subspaceMap X B)).f q ≫ Ψ :=
    (TubeCochainExtension.restriction X B q ψ).symm
  calc
    _ = c ≫ cut X A B hA hB hc p q N hN θ hs ≫
        ((push (SupportedCap.subspaceMap X B)).f q ≫ Ψ) := congrArg
          (fun f => c ≫ cut X A B hA hB hc p q N hN θ hs ≫ f) he
    _ = c ≫ (cut X A B hA hB hc p q N hN θ hs ≫
        (push (SupportedCap.subspaceMap X B)).f q) ≫ Ψ := by simp only [Category.assoc]
    _ = c ≫ ((TauCeti.singularSmallApprox coeff (cover X A B)).f N ≫
        absoluteChain X p q N hN θ) ≫ Ψ := by rw [cut_inclusion]
    _ = 0 := by simpa only [Category.assoc] using hz

theorem subspace_zero (C : Set X) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) N
      (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of C)) (R := coeff)
  intro σ
  change (TopCat.toSSet.obj (TopCat.of C)).ιChainComplex σ ≫
    ((push (SupportedCap.subspaceMap X C)).f N ≫ (cut X A B hA hB hc p q N hN θ hs ≫ ψ)) = 0
  rw [← Category.assoc, push, SSet.ι_chainComplexMap_f]
  let τ := (TopCat.toSSet.map (SupportedCap.subspaceMap X C)).app _ σ
  have ht : τ ∈ (X.smallSingularSubcomplex (fun _ : Unit => C)).obj (Opposite.op ⦋N⦌) :=
    (TopCat.mem_smallSingularSubcomplex_iff X (fun _ : Unit => C) τ).mpr
      ⟨(), TubeCochainExtension.included_range X C σ⟩
  exact zero_of_supported X A B hA hB hc C p q N hN θ hs ψ hψ
    (TauCeti.ιChainComplex_mem_smallSingularChains (R := coeff) ⟨τ, ht⟩)

end
end Finsler.MultiFarSupportedCochain
