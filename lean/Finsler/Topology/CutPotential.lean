module

public import Finsler.Topology.LadderEvent
public import Finsler.Topology.LocalizeK

/-! The potential of a cutoff at a cut, and its change between two cuts. For a cut b the pair is
(t_b, M) with the pair of its loops fixed by the half rotation inside; the potential of the
cutoff j in the degrees q, q + 1 is `LadderEvent.phi` for these pairs. For cuts a ≤ b the triple
is M ⊆ t_a ⊆ t_b with the fixed triple inside, so the crossing groups are the K-Borel cohomology
of (t_b, t_a) and the reflection Borel cohomology of the fixed crossing pair. The two statements
of `LadderEvent` read: at a far cutoff the potential at b is at most the potential at a, and in
general the two differ by at most six times a bound for the dimensions of the crossing groups.
The hypotheses on the crossing groups are local statements and are not proved here. -/

@[expose] public section

namespace Finsler.CutPotential

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.SobolevEnergy Finsler.SobolevReflectionAction
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed Finsler.BorelExact
open Finsler.BorelFreeK Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK
open Finsler.BorelCoverK Finsler.LocalCoverK Finsler.TotalExact Finsler.GradedLadder
open Finsler.FixedLadder Finsler.LadderEvent

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The fixed loops of a smaller sublevel lie in those of a larger one. -/
theorem fixLev_mono {a b : ℝ} (hab : a ≤ b) : fixLev F a ⊆ fixLev F b :=
  union_subset_union_left _ (inter_subset_inter_left _ (energyCut_mono F hab))

/-- The loops of the fixed part of a sublevel are fixed by the half rotation. -/
theorem half_fixLev (b : ℝ) (u : SphereLoop n) (hu : u ∈ fixLev F b) : half +ᵥ u = u :=
  ((mem_fixLev_iff F b u).mp hu).2

/-- The reflection Borel cohomology of the fixed pair of t_b, by root degree. -/
abbrev fixR (b : ℝ) : ℕ → Type := fun l =>
  HR (rComplex (consts_subset_fixLev F b) kInv_consts (kInv_fixLev F b)) l

/-- The reflection Borel cohomology of the fixed crossing pair of two cuts, by root degree. -/
abbrev crossR {a b : ℝ} (hab : a ≤ b) : ℕ → Type := fun l =>
  HR (rComplex (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b)) l

/-- The K-Borel cohomology of the crossing pair (t_b, t_a). -/
abbrev crossK {a b : ℝ} (hab : a ≤ b) (q : ℕ) : Type :=
  HR (borelInv (kCommuting (lev_mono F hab) (kInv_lev F a) (kInv_lev F b))) q

/-- The potential of the cutoff j in the degrees q and q + 1 at the cut b. -/
def cutPhi (b : ℝ) (j q : ℕ) : ℤ :=
  phi (consts_subset_lev F b) kInv_consts (kInv_lev F b) (consts_subset_fixLev F b) kInv_consts
    (kInv_fixLev F b) subset_rfl (fixLev_subset_lev F b) (half_fixLev F b) j q

/-- The total normalized restriction of the crossing pair of two cuts. -/
def crossEps {a b : ℝ} (hab : a ≤ b) (q : ℕ) :=
  epsTot (lev_mono F hab) (kInv_lev F a) (kInv_lev F b) (fixLev_mono F hab) (kInv_fixLev F a)
    (kInv_fixLev F b) (fixLev_subset_lev F a) (fixLev_subset_lev F b) (half_fixLev F b) q

/-- The connecting map of the reflection Borel sequence of the fixed triple of two cuts. -/
def fixDelta {a b : ℝ} (hab : a ≤ b) (l : ℕ) :=
  delta (shortExact_incl (consts_subset_fixLev F a) (fixLev_mono F hab) kInv_consts
    (kInv_fixLev F a) (kInv_fixLev F b)) l

/-- A far cutoff between two cuts: the potential at the upper cut is at most the potential at
the lower cut. -/
theorem cutPhi_far {a b : ℝ} (hab : a ≤ b) (j q : ℕ)
    (hV : FinTot (fixR F a)) (hV' : FinTot (fixR F b)) (hW : FinTot (crossR F hab))
    (hAq : Module.Finite (ZMod 2) (HK F a q)) (hA : Module.Finite (ZMod 2) (HK F a (q + 1)))
    (hA' : Module.Finite (ZMod 2) (HK F b (q + 1)))
    (hC : Module.Finite (ZMod 2) (crossK F hab (q + 1)))
    (hd : ∀ x : fixR F a j, fixDelta F hab j x = 0)
    (hl₀ : LinearMap.range (cut (crossR F hab) j) ≤ LinearMap.range (crossEps F hab q))
    (hl₁ : Function.Injective (crossEps F hab (q + 1)))
    (hl₁P : LinearMap.range (crossEps F hab (q + 1)) = LinearMap.range (cut (crossR F hab) j))
    (hl₂ : Function.Injective (crossEps F hab (q + 1 + 1)))
    (hl₂P : LinearMap.range (crossEps F hab (q + 1 + 1)) ≤
      LinearMap.range (cut (crossR F hab) j)) :
    cutPhi F b j q ≤ cutPhi F a j q :=
  phi_far (consts_subset_lev F a) (lev_mono F hab) kInv_consts (kInv_lev F a) (kInv_lev F b)
    (consts_subset_fixLev F a) (fixLev_mono F hab) kInv_consts (kInv_fixLev F a)
    (kInv_fixLev F b) subset_rfl (fixLev_subset_lev F a) (fixLev_subset_lev F b)
    (half_fixLev F b) j q hV hV' hW hAq hA hA' hC hd hl₀ hl₁ hl₁P hl₂ hl₂P

/-- A general cutoff between two cuts: the potentials differ by at most six times a bound for
the dimensions of the total fixed crossing group and of the K-Borel crossing groups of the
degrees q + 1 and q + 2. -/
theorem cutPhi_near {a b : ℝ} (hab : a ≤ b) (j q : ℕ)
    (hV : FinTot (fixR F a)) (hV' : FinTot (fixR F b)) (hW : FinTot (crossR F hab))
    (hAq : Module.Finite (ZMod 2) (HK F a q)) (hA : Module.Finite (ZMod 2) (HK F a (q + 1)))
    (hA' : Module.Finite (ZMod 2) (HK F b (q + 1)))
    (hC : Module.Finite (ZMod 2) (crossK F hab (q + 1)))
    (hC₂ : Module.Finite (ZMod 2) (crossK F hab (q + 1 + 1)))
    {M : ℕ} (hWM : totRank (crossR F hab) ≤ M)
    (hM₁ : finrank (ZMod 2) (crossK F hab (q + 1)) ≤ M)
    (hM₂ : finrank (ZMod 2) (crossK F hab (q + 1 + 1)) ≤ M) :
    cutPhi F b j q ≤ cutPhi F a j q + 6 * (M : ℤ) ∧
      cutPhi F a j q ≤ cutPhi F b j q + 6 * (M : ℤ) :=
  phi_near (consts_subset_lev F a) (lev_mono F hab) kInv_consts (kInv_lev F a) (kInv_lev F b)
    (consts_subset_fixLev F a) (fixLev_mono F hab) kInv_consts (kInv_fixLev F a)
    (kInv_fixLev F b) subset_rfl (fixLev_subset_lev F a) (fixLev_subset_lev F b)
    (half_fixLev F b) j q hV hV' hW hAq hA hA' hC hC₂ hWM hM₁ hM₂

end

end Finsler.CutPotential
