module

public import Finsler.Topology.FirstHalfInteriorFamily
public import Finsler.Topology.SupportedCapNaturality

/-! Along the original interior first-half deformation the tested map
is literally pulled back from the source. This is an equality of actual
cochains in every degree, before passage to cohomology. -/

@[expose] public section
namespace Finsler.FirstHalfInteriorTested

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.FirstHalfInteriorFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {X : Type} [TopologicalSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
  {r : ℝ} (hr : r ≤ 1)

def sourceMap : TopCat.of (domain u a ha ha1 r) ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom ⟨fun z => (family u a ha ha1 hr (0, z)).1,
    continuous_fst.comp ((family u a ha ha1 hr).continuous.comp (continuous_const.prodMk continuous_id))⟩

def familyMap : TopCat.of (_root_.unitInterval × domain u a ha ha1 r) ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom ⟨fun z => (family u a ha ha1 hr z).1,
    continuous_fst.comp (family u a ha ha1 hr).continuous⟩

def projection : TopCat.of (_root_.unitInterval × domain u a ha ha1 r) ⟶ TopCat.of (domain u a ha ha1 r) :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

theorem family_fixed : familyMap u a ha ha1 hr = projection u a ha ha1 ≫ sourceMap u a ha ha1 hr := by
  apply TopCat.ext
  intro z
  change (family u a ha ha1 hr (z.1, z.2)).1 = (family u a ha ha1 hr (0, z.2)).1
  rw [tested_fixed, tested_fixed]

theorem cochain_fixed (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (familyMap u a ha ha1 hr) p T =
      cochainPullback (projection u a ha ha1) p (cochainPullback (sourceMap u a ha ha1 hr) p T) := by
  rw [family_fixed, pullback_comp]

theorem cochain_closed (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (_root_.unitInterval × domain u a ha ha1 r)) p
      (cochainPullback (familyMap u a ha ha1 hr) p T) = 0 :=
  pullback_closed (familyMap u a ha ha1 hr) p T hT

end
end Finsler.FirstHalfInteriorTested
