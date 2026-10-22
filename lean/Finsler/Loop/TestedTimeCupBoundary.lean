module

public import Finsler.Loop.NativeBVCutTestBoundary

/-! The actual geometric time cup carries an arbitrary tested-slot
primitive to a source primitive, with explicit degree alignment. -/
@[expose] public section
namespace Finsler.TestedTimeCupBoundary
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedSelfCut Finsler.NativeBVThomBoundary
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K = CochainDegreeTransport.pre X hj T := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)

theorem split_sub (p q : ℕ)
    (T U : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q) :
    GeometricTimeCupCochain.splitCup m p hr (T - U) q B =
      GeometricTimeCupCochain.splitCup m p hr T q B - GeometricTimeCupCochain.splitCup m p hr U q B := by
  unfold GeometricTimeCupCochain.splitCup NormalizedSelfCut.testedCocycle
  have hp := map_sub ((singularCochainComplexZMod2.map
    (TopCat.ofHom (tested (m + 1) hr)).op).f p).hom T U
  change cochainPullback (TopCat.ofHom (tested (m + 1) hr)) p (T - U) =
    cochainPullback (TopCat.ofHom (tested (m + 1) hr)) p T -
      cochainPullback (TopCat.ofHom (tested (m + 1) hr)) p U at hp
  rw [hp]
  exact map_sub (cupRightMor _ p q _).hom _ _

theorem source_boundary_at (p j q : ℕ) (hj : p + 1 = j)
    (K : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0) :
    (chains (Loops (m + 1))).d (m + (j + q)) (m + (p + q)) ≫
      source m hρ hρr (p + q) (GeometricTimeCupCochain.splitCup m p hr K q B) =
    source m hρ hρr (j + q)
      (GeometricTimeCupCochain.splitCup m j hr ((chains (Loops (m + 1))).d j p ≫ K) q B) := by
  subst j
  exact NativeBVCutTestBoundary.source_test_boundary m hρ hρr hr p q K B hB

theorem geometric_boundary_at (p j q : ℕ) (hj : p + 1 = j)
    (K : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0) :
    (chains (Loops (m + 1))).d ((m + j) + q) ((m + p) + q) ≫
      GeometricTimeCupCochain.cochain m p hρ hρr hr K q B =
    GeometricTimeCupCochain.cochain m j hρ hρr hr ((chains (Loops (m + 1))).d j p ≫ K) q B := by
  rw [← NativeBVCutTestBoundary.source_geometric m hρ hρr hr p q K B,
    ← NativeBVCutTestBoundary.source_geometric m hρ hρr hr j q]
  exact boundary_pre (Nat.add_assoc m p q) (Nat.add_assoc m j q) _ _
    (source_boundary_at m hρ hρr hr p j q hj K B hB)

theorem geometric_sub (p q : ℕ)
    (T U : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q) :
    GeometricTimeCupCochain.cochain m p hρ hρr hr (T - U) q B =
      GeometricTimeCupCochain.cochain m p hρ hρr hr T q B -
        GeometricTimeCupCochain.cochain m p hρ hρr hr U q B := by
  simp only [GeometricTimeCupCochain.cochain, split_sub, Preadditive.comp_sub]

end
end Finsler.TestedTimeCupBoundary
