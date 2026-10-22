module

public import Finsler.Geometry.RoundTails
public import Finsler.Topology.DirectedUnionLocal
public import Finsler.Topology.BorelLens

/-! Compact supports of the homology of the loop space along the round cuts.

The sublevels t_{c_k} are open (positive cuts), increasing, and cover the loop space (every loop
has finite energy), so by the compact supports of singular homology (Tau Ceti `DirectedUnion`,
here through the local copy `DirectedUnionLocal`) every class of the loop space comes from some
cut and a class of a cut which dies in the loop space dies in a larger cut. This is `Supports`. -/

@[expose] public section

namespace Finsler.RoundSupports

open CategoryTheory Limits AlgebraicTopology Finsler.SphereGeometry Finsler.Geometry
open Finsler.RoundFiltration Finsler.RoundTails Finsler.TameHomology Finsler.BorelLoop
open Finsler.RelativeCohomology
open Set Topology

noncomputable section

variable {n : ℕ}

section Supports

variable {Y : TopCat.{0}} {U : ℕ → Set Y} (hU : Monotone U) {V : Set Y} (hUV : ∀ j, U j ⊆ V)
  (hopen : ∀ j, IsOpen (Subtype.val ⁻¹' U j : Set V)) (hcover : V ⊆ ⋃ j, U j)

include hU hopen hcover in
/-- Every class of the union comes from a member. -/
theorem exists_rep (q : ℕ) (y : Hq (TopCat.of V) q) :
    ∃ j, ∃ x : Hq (TopCat.of (U j)) q,
      (HqMap (TopCat.ofHom (ContinuousMap.inclusion (hUV j))) q).hom x = y := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{0} (ZMod 2))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let c : Cocone ({ obj j := TopCat.of (U j)
                    map f := TopCat.ofHom (ContinuousMap.inclusion (hU f.le)) } : ℕ ⥤ TopCat.{0}) :=
    { pt := TopCat.of V, ι := { app j := TopCat.ofHom (ContinuousMap.inclusion (hUV j)) } }
  have hK (K : Set c.pt) (hK : IsCompact K) : ∃ j, K ⊆ Set.range (c.ι.app j) := by
    obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ (Subtype.val ⁻¹' U j : Set V)) hopen
      (fun x _ ↦ Set.mem_iUnion.2 (Set.mem_iUnion.1 (hcover x.2) : ∃ j, x.1 ∈ U j))
      (Monotone.directed_le fun _ _ h ↦ Set.preimage_mono (hU h))
    exact ⟨j, fun x hx ↦ ⟨⟨x.1, hj hx⟩, rfl⟩⟩
  obtain ⟨j, x, hx⟩ := Concrete.isColimit_exists_rep _
    (Finsler.DirectedUnionLocal.isColimitMapCoconeSingularHomology coeff q c
      (fun j ↦ IsEmbedding.inclusion (hUV j)) hK) y
  exact ⟨j, x, hx⟩

end Supports

theorem lev_cover (u : Loops n) : ∃ k, u ∈ lev (roundMetric n) (cut k) := by
  obtain ⟨k, hk⟩ := exists_cut_gt (Real.sqrt (Finsler.SobolevEnergy.energy (roundMetric n) u))
  exact ⟨k, Or.inl hk⟩

theorem hU_mono : Monotone fun k : ℕ => lev (roundMetric n) (cut k) :=
  fun _ _ h => lev_mono (roundMetric n) (cut_le_cut h)

theorem hopen_lev (k : ℕ) :
    IsOpen (Subtype.val ⁻¹' lev (roundMetric n) (cut k) : Set (univ : Set (Loops n))) :=
  (Finsler.BorelLens.lev_isOpen (roundMetric n) (cut_pos k)).preimage continuous_subtype_val

theorem hcover_lev : (univ : Set (Loops n)) ⊆ ⋃ k, lev (roundMetric n) (cut k) := fun u _ =>
  mem_iUnion.mpr (lev_cover u)

/-- **Compact supports along the round cuts.** -/
theorem round_supports (n : ℕ) : Supports n := by
  refine ⟨fun q y => ?_, fun q i x hx => ?_⟩
  · obtain ⟨j, x, hx⟩ := exists_rep hU_mono (fun _ => subset_univ _) hopen_lev hcover_lev q y
    exact ⟨j, x, hx⟩
  · obtain ⟨j, hij, h⟩ := Finsler.DirectedUnionLocal.exists_singularHomologyMap_inclusion_eq_zero
      coeff q hU_mono (fun _ => subset_univ _) hopen_lev hcover_lev x hx
    exact ⟨j, hij, h⟩

end

end Finsler.RoundSupports
