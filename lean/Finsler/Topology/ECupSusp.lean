module

public import Finsler.Topology.ECup
public import Finsler.Topology.PairSuspensionProduct

/-! The suspension isomorphisms are linear over cup with classes of the base.

For a subset P of a space X, an open set O and a class c on X, the cup with c annihilates no
nonzero class of (P, P ∩ O) in degree q if and only if the cup with the pullback of c to X × ℝ
annihilates no nonzero class of the suspended pair in degree q + 1: the suspension isomorphism
is the composite of the projection of the negative part (a map over X), an excision and the
connecting map of a triple, and the injectivity of the cup transports along each of them
(`ECup`). Iterating, the same holds for the b-fold suspension and for the products with ℝ^b
(the homeomorphism with the b-fold product commutes with the projections to the base). -/

@[expose] public section

namespace Finsler.ECupSusp

open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.PairSuspension Finsler.PairSuspensionProduct Finsler.ECup
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The projection of the cylinder to the base. -/
def cylProj (X : TopCat.{0}) : Cyl X ⟶ X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- **The suspension is linear over cup with classes of the base.** -/
theorem susp_iff {X : TopCat.{0}} {p : ℕ} (c : cohomologyZMod2 X p) (P : Set X) {O : Set X}
    (hO : IsOpen O) (q : ℕ) :
    CupInjW c (inter_subset_left : P ∩ O ⊆ P) q ↔
      CupInjW ((cohPullback (cylProj X) p).hom c)
        (inter_subset_left : cyl P ∩ suspO O ⊆ cyl P) (q + 1) := by
  rw [cupInjW_over (cylProj X) c (pairMapX (base_sub_dn P O) (inter_subset_left : P ∩ O ⊆ P)
    (projMap P O) (fun _ hy => ⟨hy.1, hy.2⟩)) rfl (proj_bijective P O q)
    (proj_bijective P O (p + q))]
  rw [← cupInjW_incl _ (base_sub_dn P O) (up_sub_susp P O) (base_sub_up P O) (dn_sub_susp P O)
    (exc_bijective P O hO q) (exc_bijective P O hO (p + q))]
  exact cupInjW_delta _ (up_sub_susp P O) (inter_subset_left : cyl P ∩ suspO O ⊆ cyl P)
    (delta_bijective P O q) (delta_bijective P O (p + q))

/-- The projection of the b-fold product with the real line to the base. -/
def iterProj (X : TopCat.{0}) : (b : ℕ) → (iterSpace X b ⟶ X)
  | 0 => 𝟙 X
  | b + 1 => cylProj (iterSpace X b) ≫ iterProj X b

/-- **The b-fold suspension is linear over cup with classes of the base.** -/
theorem iter_iff {X : TopCat.{0}} {p : ℕ} (c : cohomologyZMod2 X p) (P : Set X) {O : Set X}
    (hO : IsOpen O) (q : ℕ) : ∀ b : ℕ,
    CupInjW c (inter_subset_left : P ∩ O ⊆ P) q ↔
      CupInjW ((cohPullback (iterProj X b) p).hom c)
        (inter_subset_left : iterCyl P b ∩ iterOpen O b ⊆ iterCyl P b) (q + b)
  | 0 => by
    have e : (cohPullback (iterProj X 0) p).hom c = c :=
      Finsler.DiagonalCohomology.pullback_id X p c
    rw [e]
    exact Iff.rfl
  | b + 1 => by
    have e : (cohPullback (iterProj X (b + 1)) p).hom c =
        (cohPullback (cylProj (iterSpace X b)) p).hom ((cohPullback (iterProj X b) p).hom c) :=
      Finsler.Cup.pullback_comp _ _ p c
    rw [e]
    exact (iter_iff c P hO q b).trans
      (susp_iff _ (iterCyl P b) (iterOpen_isOpen hO b) (q + b))

/-- The projection of Z × ℝ^b to the base. -/
def prdProj (Z : TopCat.{0}) (b : ℕ) : Prd Z b ⟶ Z := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

theorem iterProj_iterHomeo (Z : TopCat.{0}) : ∀ (b : ℕ) (p : Z × (Fin b → ℝ)),
    (iterProj Z b).hom (iterHomeo Z b p) = p.1
  | 0, _ => rfl
  | b + 1, p => by
    rw [iterHomeo_succ]
    exact iterProj_iterHomeo Z b (p.1, fun i => p.2 (Fin.castSucc i))

/-- **The products with ℝ^b are linear over cup with classes of the base.** -/
theorem prod_iff {Z : TopCat.{0}} {p : ℕ} (c : cohomologyZMod2 Z p) (P : Set Z) {O : Set Z}
    (hO : IsOpen O) (b q : ℕ) :
    CupInjW c (inter_subset_left : P ∩ O ⊆ P) q ↔
      CupInjW ((cohPullback (prdProj Z b) p).hom c)
        (inter_subset_left : prodCyl P b ∩ prodOpen O b ⊆ prodCyl P b) (q + b) := by
  rw [iter_iff c P hO q b]
  have e : (cohPullback (TopCat.ofHom (X := Prd Z b) (Y := iterSpace Z b)
      ⟨iterHomeo Z b, (iterHomeo Z b).continuous⟩) p).hom
        ((cohPullback (iterProj Z b) p).hom c) = (cohPullback (prdProj Z b) p).hom c := by
    have hcomp : TopCat.ofHom (X := Prd Z b) (Y := iterSpace Z b)
        ⟨iterHomeo Z b, (iterHomeo Z b).continuous⟩ ≫ iterProj Z b = prdProj Z b := by
      ext y
      exact iterProj_iterHomeo Z b y
    rw [← Finsler.Cup.pullback_comp, hcomp]
  rw [← e]
  exact cupInjW_over (TopCat.ofHom ⟨iterHomeo Z b, (iterHomeo Z b).continuous⟩) _ _ rfl
    (prod_bijective P O b (q + b)) (prod_bijective P O b (p + (q + b)))

end

end Finsler.ECupSusp
