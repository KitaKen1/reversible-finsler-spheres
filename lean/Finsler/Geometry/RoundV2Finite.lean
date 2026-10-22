module

public import Finsler.Geometry.RoundThom
public import Finsler.Topology.FiniteCut

/-! V₂ has finite dimensional cohomology in every degree.

The Stiefel manifold V₂ of orthonormal pairs is a compact subset of the open set of independent
pairs, onto which Gram–Schmidt retracts it. Between V₂ and the open set lies an open finite union
of convex sets, which is tame (`TameHomology`); since V₂ is a retract of it, V₂ is tame. The
universal coefficient isomorphism over F₂ then gives finite dimensional ordinary cohomology of the
pair (V₂, ∅) in every degree. -/

@[expose] public section

namespace Finsler.RoundV2Finite

open CategoryTheory Finsler.SphereGeometry Finsler.RoundQR Finsler.RoundChart Finsler.RoundThom
open Finsler.TameHomology Finsler.BorelCochain Finsler.BorelPair Finsler.PairTriple
open Finsler.BorelComparison Finsler.BorelLoop
open Set Topology Filter
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- The independent pairs. -/
def Ind : Set (Ambient n × Ambient n) := {p | Indep p.1 p.2}

theorem continuousAt_res {A B : Ambient n} (hA : A ≠ 0) :
    ContinuousAt (fun p : Ambient n × Ambient n => res p.1 p.2) (A, B) := by
  have hx : ContinuousAt (fun p : Ambient n × Ambient n => gsx p.1) (A, B) :=
    ContinuousAt.comp (g := gsx) (f := fun p : Ambient n × Ambient n => p.1)
      (continuousAt_gsx hA) continuousAt_fst
  have hi : ContinuousAt (fun p : Ambient n × Ambient n => ⟪p.2, gsx p.1⟫) (A, B) :=
    continuousAt_snd.inner hx
  have hs : ContinuousAt (fun p : Ambient n × Ambient n => ⟪p.2, gsx p.1⟫ • gsx p.1) (A, B) :=
    hi.smul hx
  unfold res r12
  exact continuousAt_snd.sub hs

theorem Ind_isOpen : IsOpen (Ind (n := n)) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨A, B⟩ h
  have h1 : ∀ᶠ p in 𝓝 (A, B), (p : Ambient n × Ambient n).1 ≠ 0 :=
    continuousAt_fst.eventually (isOpen_ne.mem_nhds h.1)
  have h2 : ∀ᶠ p in 𝓝 (A, B), res (p : Ambient n × Ambient n).1 p.2 ≠ 0 :=
    (continuousAt_res h.1).eventually (isOpen_ne.mem_nhds h.2)
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem V2_sub_Ind : V2 (n := n) ⊆ Ind := by
  intro z hz
  obtain ⟨-, -, h3, -⟩ := gs_orthonormal hz.1 hz.2.1 hz.2.2
  refine ⟨fun h => ?_, ?_⟩
  · have := hz.1
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · rw [h3]
    intro h
    have := hz.2.1
    rw [h, norm_zero] at this
    exact zero_ne_one this

theorem gs_mem_V2 {p : Ambient n × Ambient n} (hp : p ∈ Ind) : (gsx p.1, gsu p.1 p.2) ∈ V2 :=
  ⟨norm_gsx hp.1, norm_gsu hp, inner_gsx_gsu hp⟩

theorem gs_continuousOn :
    ContinuousOn (fun p : Ambient n × Ambient n => (gsx p.1, gsu p.1 p.2)) Ind := fun p hp =>
  (continuousAt_gs (A := p.1) (B := p.2) hp).continuousWithinAt

/-- **V₂ is tame.** -/
theorem tame_V2 : ∃ k, Tame (TopCat.of ↥(univ : Set (V2T n))) k := by
  obtain ⟨Q, m, -, hKQ, hQΩ, hQ⟩ :=
    exists_tame_between (isCompact_V2 (n := n)) Ind_isOpen V2_sub_Ind
  let f : C(↥(univ : Set (V2T n)), ↥Q) :=
    ⟨fun x => ⟨x.1.1, hKQ x.1.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let g : C(↥Q, ↥(univ : Set (V2T n))) :=
    ⟨fun y => ⟨⟨(gsx (y : Ambient n × Ambient n).1, gsu (y : Ambient n × Ambient n).1
        (y : Ambient n × Ambient n).2), gs_mem_V2 (hQΩ y.2)⟩, trivial⟩,
      ((gs_continuousOn.comp_continuous continuous_subtype_val fun y => hQΩ y.2).subtype_mk
        _).subtype_mk _⟩
  have hgf : g.comp f = ContinuousMap.id _ := by
    refine ContinuousMap.ext fun x => Subtype.ext (Subtype.ext ?_)
    obtain ⟨h1, -, -, h4⟩ := gs_orthonormal x.1.2.1 x.1.2.2.1 x.1.2.2.2
    change ((gsx x.1.1.1, gsu x.1.1.1 x.1.1.2) : Ambient n × Ambient n) = x.1.1
    rw [h1, h4]
  refine ⟨m, tame_of_factor (TopCat.ofHom f) (TopCat.ofHom g) hQ fun q => ?_⟩
  have h1 : TopCat.ofHom f ≫ TopCat.ofHom g = 𝟙 (TopCat.of ↥(univ : Set (V2T n))) :=
    congrArg TopCat.ofHom hgf
  rw [h1, HqMap_id]
  exact fun x y h => h

/-- The empty part of the pair is tame. -/
theorem tame_empty : Tame (TopCat.of ↥((univ : Set (V2T n)) ∩ ∅)) 1 := by
  have hE : IsEmpty ↥((univ : Set (V2T n)) ∩ ∅) := ⟨fun x => x.2.2⟩
  have hT := tame_convex (∅ : Set ℝ) convex_empty
  have hc : ∀ {β : Type} [TopologicalSpace β] (h : ↥((univ : Set (V2T n)) ∩ ∅) → β),
      Continuous h := fun h => ⟨fun s _ => by
        rw [Set.eq_empty_of_isEmpty (h ⁻¹' s)]
        exact isOpen_empty⟩
  have hE' : IsEmpty ↥(∅ : Set ℝ) := ⟨fun x => x.2⟩
  let f : C(↥((univ : Set (V2T n)) ∩ ∅), ↥(∅ : Set ℝ)) := ⟨fun x => (x.2.2).elim, hc _⟩
  let g : C(↥(∅ : Set ℝ), ↥((univ : Set (V2T n)) ∩ ∅)) :=
    ⟨fun x => (x.2).elim, ⟨fun s _ => by
      rw [Set.eq_empty_of_isEmpty ((fun x : ↥(∅ : Set ℝ) => (x.2).elim) ⁻¹' s)]
      exact isOpen_empty⟩⟩
  refine tame_of_factor (TopCat.ofHom f) (TopCat.ofHom g) hT fun q => ?_
  have hgf : g.comp f = ContinuousMap.id _ := ContinuousMap.ext fun x => (x.2.2).elim
  have h1 : TopCat.ofHom f ≫ TopCat.ofHom g = 𝟙 (TopCat.of ↥((univ : Set (V2T n)) ∩ ∅)) :=
    congrArg TopCat.ofHom hgf
  rw [h1, HqMap_id]
  exact fun x y h => h

/-- **The cohomology of V₂ is finite dimensional in every degree.** -/
theorem V2_finite (q : ℕ) : Module.Finite (ZMod 2)
    (H (triv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))) q) := by
  obtain ⟨k, hk⟩ := tame_V2 (n := n)
  have hrel : Module.Finite (ZMod 2)
      (Hrel (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)) q) := by
    cases q with
    | zero => exact finite_rel_zero _ (hk.finite 0)
    | succ q => exact finite_rel_succ _ q (hk.finite (q + 1)) (tame_empty.finite q)
  let e := (ordinaryEquiv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ))
    (𝟙 _) (Category.comp_id _) q).trans
      (RelativeKronecker.equiv (pairOf (inter_subset_left : (univ : Set (V2T n)) ∩ ∅ ⊆ univ)) q)
  haveI := hrel
  exact Module.Finite.equiv e.symm

end

end Finsler.RoundV2Finite
