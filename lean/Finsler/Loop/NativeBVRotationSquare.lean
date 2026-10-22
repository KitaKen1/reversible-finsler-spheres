module

public import Finsler.Loop.NativeGlobalTimeSquare
public import Finsler.Loop.NativeBVThomBoundary
public import Finsler.Loop.H1LoopRotation
public import Finsler.Loop.SelfCutPrismCoboundary

/-! The ORIGINAL full-period H1 rotation followed by the original cut
time is the actual two-time square. Its rotation faces agree (they need
not vanish); only the cut faces need vanish to transport a boundary. -/
@[expose] public section
namespace Finsler.NativeBVRotationSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

abbrev rotationDomain (n : ℕ) := DoubleRelativeTimeCylinder.cylinder (Loops n)
abbrev squareDomain (n : ℕ) := DoubleRelativeTimeCylinder.cylinder (rotationDomain n)

def rotationMap (n : ℕ) : rotationDomain n ⟶ Loops n :=
  TopCat.ofHom (H1LoopRotation.homotopy n).toContinuousMap

def intoCut (n : ℕ) : squareDomain n ⟶ SelfCutThomCocycle.parameters n :=
  TopCat.ofHom ⟨fun z => (z.1, rotationMap n z.2),
    continuous_fst.prodMk ((rotationMap n).hom.continuous.comp continuous_snd)⟩

def rotationFace (n : ℕ) (t : _root_.unitInterval) : SelfCutThomCocycle.parameters n ⟶ squareDomain n :=
  TopCat.ofHom ⟨fun z => (z.1, (t, z.2)),
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩

theorem rotation_prism (n q : ℕ) :
    ((DoubleRelativeTimeCylinder.homotopy (Loops n)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (push (rotationMap n)).f (q + 1) = (H1LoopRotation.chainHomotopy n).hom q (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (rotationMap n))
      (DoubleRelativeTimeCylinder.homotopy (Loops n))).h = (H1LoopRotation.homotopy n).h := by
    ext z : 1
    rfl
  exact (TimePrismNaturality.prism_post (DoubleRelativeTimeCylinder.homotopy (Loops n))
    (rotationMap n) q).trans (TimePrismNaturality.prism_congr _ _ he q)

theorem cut_prism (n q : ℕ) :
    (push (rotationMap n)).f q ≫ SelfCutTimePrism.prism n q =
      ((DoubleRelativeTimeCylinder.homotopy (rotationDomain n)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
        (push (intoCut n)).f (q + 1) := by
  have he : ((SelfCutTimePrism.cylinder n).comp (TopCat.Homotopy.refl (rotationMap n))).h =
      (TopCat.Homotopy.comp (TopCat.Homotopy.refl (intoCut n))
        (DoubleRelativeTimeCylinder.homotopy (rotationDomain n))).h := by
    ext z : 1
    rfl
  exact (TimePrismNaturality.prism_pre (SelfCutTimePrism.cylinder n) (rotationMap n) q).trans
    ((TimePrismNaturality.prism_congr _ _ he q).trans
      (TimePrismNaturality.prism_post (DoubleRelativeTimeCylinder.homotopy (rotationDomain n)) (intoCut n) q).symm)

theorem double_prism (n q : ℕ) :
    (H1LoopRotation.chainHomotopy n).hom q (q + 1) ≫ SelfCutTimePrism.prism n (q + 1) =
      NativeGlobalTimeSquare.squarePrism (Loops n) q ≫ (push (intoCut n)).f (q + 2) := by
  rw [← rotation_prism, Category.assoc, cut_prism]
  rfl

theorem cut_endpoint (n : ℕ) (t : _root_.unitInterval) :
    DoubleRelativeTimeCylinder.atTime (rotationDomain n) t ≫ intoCut n =
      rotationMap n ≫ SelfCutThomCocycle.atTime n t := by
  ext z : 1
  rfl

theorem rotation_zero (n : ℕ) : rotationFace n 0 ≫ intoCut n = 𝟙 (SelfCutThomCocycle.parameters n) := by
  ext z : 1
  change (z.1, (H1LoopRotation.homotopy n) (0, z.2)) = z
  exact Prod.ext rfl ((H1LoopRotation.homotopy n).map_zero_left z.2)

theorem rotation_one (n : ℕ) : rotationFace n 1 ≫ intoCut n = 𝟙 (SelfCutThomCocycle.parameters n) := by
  ext z : 1
  change (z.1, (H1LoopRotation.homotopy n) (1, z.2)) = z
  exact Prod.ext rfl ((H1LoopRotation.homotopy n).map_one_left z.2)

theorem rotation_faces_equal (n q : ℕ)
    (T : singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters n) q) :
    cochainPullback (rotationFace n 0) q (cochainPullback (intoCut n) q T) =
      cochainPullback (rotationFace n 1) q (cochainPullback (intoCut n) q T) := by
  rw [← pullback_comp, ← pullback_comp, rotation_zero, rotation_one]

theorem thom_cut_endpoint_zero (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) q)
    (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (DoubleRelativeTimeCylinder.atTime (rotationDomain (m + 1)) t) ((m + 1) + q)
      (cochainPullback (intoCut (m + 1)) ((m + 1) + q) (NativeBVThomBoundary.parameter m hρ hρr q K)) = 0 := by
  rw [← pullback_comp, cut_endpoint, pullback_comp,
    NativeBVThomBoundary.parameter_endpoint m hρ hρr q K t ht]
  exact map_zero _

theorem double_boundary_zero (n q : ℕ)
    (T : singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters n) (q + 1))
    (h0 : cochainPullback (SelfCutThomCocycle.atTime n 0) (q + 1) T = 0)
    (h1 : cochainPullback (SelfCutThomCocycle.atTime n 1) (q + 1) T = 0) :
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      (push (intoCut n)).f (q + 2) ≫ cochainCoboundary (ZMod 2) _ (q + 1) T = 0 := by
  have hb := SelfCutPrismCoboundary.boundary n q T h0 h1
  change (chains (Loops n)).d (q + 1) q ≫ SelfCutPrismCoboundary.primitive n q T =
    SelfCutTimePrism.prism n (q + 1) ≫ cochainCoboundary (ZMod 2) _ (q + 1) T at hb
  have hz : ((chains (Loops n)).iCycles q ≫ (H1LoopRotation.chainHomotopy n).hom q (q + 1)) ≫
      (chains (Loops n)).d (q + 1) q = 0 :=
    SelfHomotopySweep.cycles_closed (H1LoopRotation.chainHomotopy n) q
  calc
    _ = (chains (Loops n)).iCycles q ≫ (H1LoopRotation.chainHomotopy n).hom q (q + 1) ≫
        (SelfCutTimePrism.prism n (q + 1) ≫ cochainCoboundary (ZMod 2) _ (q + 1) T) := by
      rw [← Category.assoc (NativeGlobalTimeSquare.squarePrism (Loops n) q), ← double_prism]
      simp only [Category.assoc]
    _ = (((chains (Loops n)).iCycles q ≫ (H1LoopRotation.chainHomotopy n).hom q (q + 1)) ≫
        (chains (Loops n)).d (q + 1) q) ≫ SelfCutPrismCoboundary.primitive n q T := by
      rw [← hb]
      simp only [Category.assoc]
    _ = 0 := by rw [hz, zero_comp]

end
end Finsler.NativeBVRotationSquare
