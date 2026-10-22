module

public import Finsler.Topology.DoubleCapEmbeddingPullback

/-! Pull back the actual local two-cap boundary identity along a
chain-monic parameter embedding. No globally closed zero extension is
introduced by the pullback. -/

@[expose] public section
namespace Finsler.DoubleCapEmbeddingBoundary

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem boundary {Z X : TopCat.{0}} {ι : Type*} (h : Z ⟶ X) (W : ι → Set X)
    (hmono : ∀ q, Mono ((push h).f q)) (k p : ℕ)
    (φ : singularCochainGroup (ZMod 2) X k) (ψ : singularCochainGroup (ZMod 2) X p)
    (hcomm : ∀ q, ((inclusion X W).f (k + (p + (q + 1))) ≫
      PartialDoubleCap.cap X k p (q + 1) φ ψ) ≫ (chains X).d (q + 1) q =
        (small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫
          ((inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ)) (q : ℕ) :
    ((inclusion Z (DoubleCapEmbeddingPullback.cover h W)).f (k + (p + (q + 1))) ≫
      PartialDoubleCap.cap Z k p (q + 1) (cochainPullback h k φ) (cochainPullback h p ψ)) ≫
        (chains Z).d (q + 1) q =
      (small Z (DoubleCapEmbeddingPullback.cover h W)).d (k + (p + (q + 1))) (k + (p + q)) ≫
        ((inclusion Z (DoubleCapEmbeddingPullback.cover h W)).f (k + (p + q)) ≫
          PartialDoubleCap.cap Z k p q (cochainPullback h k φ) (cochainPullback h p ψ)) := by
  let U := DoubleCapEmbeddingPullback.cover h W
  let M := SmallRetractionComparison.map (X := Z) (Y := X) U W h id (fun _ _ hz => hz)
  let cZ := fun q => (inclusion Z U).f (k + (p + q)) ≫
    PartialDoubleCap.cap Z k p q (cochainPullback h k φ) (cochainPullback h p ψ)
  let cX := fun q => (inclusion X W).f (k + (p + q)) ≫ PartialDoubleCap.cap X k p q φ ψ
  have he (j : ℕ) : cZ j ≫ (push h).f j = M.f (k + (p + j)) ≫ cX j := by
    have hi := congrArg (fun g => g.f (k + (p + j)))
      (SmallRetractionComparison.map_inclusion (X := Z) (Y := X) U W h id (fun _ _ hz => hz))
    change M.f (k + (p + j)) ≫ (inclusion X W).f (k + (p + j)) =
      (inclusion Z U).f (k + (p + j)) ≫ (push h).f (k + (p + j)) at hi
    dsimp only [cZ, cX]
    rw [Category.assoc, PartialDoubleCap.cap_natural, ← Category.assoc, ← hi, Category.assoc]
  haveI : Mono ((push h).f q) := hmono q
  apply (cancel_mono ((push h).f q)).mp
  change (cZ (q + 1) ≫ (chains Z).d (q + 1) q) ≫ (push h).f q =
    ((small Z U).d (k + (p + (q + 1))) (k + (p + q)) ≫ cZ q) ≫ (push h).f q
  calc
    _ = (cZ (q + 1) ≫ (push h).f (q + 1)) ≫ (chains X).d (q + 1) q := by
      rw [Category.assoc, ← (push h).comm, ← Category.assoc]
    _ = (M.f (k + (p + (q + 1))) ≫ cX (q + 1)) ≫ (chains X).d (q + 1) q := by rw [he]
    _ = M.f (k + (p + (q + 1))) ≫
        ((small X W).d (k + (p + (q + 1))) (k + (p + q)) ≫ cX q) := by
      rw [Category.assoc]
      exact congrArg (fun g => M.f (k + (p + (q + 1))) ≫ g) (hcomm q)
    _ = ((small Z U).d (k + (p + (q + 1))) (k + (p + q)) ≫ M.f (k + (p + q))) ≫ cX q := by
      rw [← Category.assoc, M.comm]
    _ = _ := by rw [Category.assoc, ← he, ← Category.assoc]

end
end Finsler.DoubleCapEmbeddingBoundary
