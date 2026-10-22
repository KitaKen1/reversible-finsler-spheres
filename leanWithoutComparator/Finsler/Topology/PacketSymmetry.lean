module

public import Finsler.Topology.CirclePacketFamily
public import Finsler.Topology.LensK

/-! invariant deformed sublevels, lens sets and paired orbit
regions for the actual packet global descent. -/

@[expose] public section

namespace Finsler.PacketSymmetry

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.FiniteCirclePackets
open Finsler.CirclePacketFamily Finsler.ReversalFamily Finsler.PolygonDescentK
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.AmbientK Finsler.AmbientSymmetry
open Finsler.RevLabel Finsler.FlowLens Finsler.InvPairs
open scoped ContDiff NNReal

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1200000

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]

theorem deformed_rev (F : ReversibleMetric n) (d : ι → Packet n (2 * M))
    (y : ZMod (2 * M) → Ambient n) :
    deformed M F (packetFamily M d) (revA (2 * M) y) = deformed M F (packetFamily M d) y := by
  have hβ : ∀ p : ι × Bool, (packetFamily M d p).β (revA (2 * M) y) =
      (packetFamily M d (Finsler.ReversalFamily.flip p)).β y := by
    rintro ⟨i, o⟩
    cases o <;> simp [packetFamily, reversePacket, Finsler.ReversalFamily.flip,
      Finsler.InvolutionConjugacy.conjFun, revA_revA]
  unfold deformed
  rw [pen_revA]
  simp only [hβ]
  exact congrArg (fun z => pen F (2 * M) 1 y + z)
    (Equiv.sum_comp Finsler.ReversalFamily.flip (fun p => (packetFamily M d p).β y))

variable {F : ReversibleMetric n} {hfin : (primeImages F).Finite}
variable {s : ι → Set (Sphere n)} {hs : ∀ i, s i ∈ primeImages F} {k N : ι → ℕ}
variable {c η : ℝ} {d : ι → Packet n (2 * M)}
variable (hd : ∀ i, Spec F hfin (s i) (hs i) (k i) (N i) c η (d i))
variable (hkn : ∀ i, k i * N i = M)

include hd hkn

theorem deformed_half (y : ZMod (2 * M) → Ambient n) :
    deformed M F (packetFamily M d) (rotA (2 * M) (M : ZMod (2 * M)) y) =
      deformed M F (packetFamily M d) y := by
  unfold deformed
  rw [Finsler.AmbientSymmetry.pen_rotA]
  congr 1
  exact Finset.sum_congr rfl fun p _ => (family_half M F hfin s hs k N hd hkn p).2.2.2.1 y

theorem deformed_rho (Q : Om n (2 * M)) :
    deformed M F (packetFamily M d) ((ambK M).ρ Q).1 = deformed M F (packetFamily M d) Q.1 :=
  deformed_rev F d Q.1

theorem deformed_sigma (Q : Om n (2 * M)) :
    deformed M F (packetFamily M d) ((ambK M).σ Q).1 = deformed M F (packetFamily M d) Q.1 :=
  deformed_half hd hkn Q.1

theorem inv_sub (a : ℝ) : Inv (ambK M)
    (sub (fun Q : Om n (2 * M) => deformed M F (packetFamily M d) Q.1) a) :=
  Finsler.LensK.inv_sub (ambK M) (deformed_rho hd hkn) (deformed_sigma hd hkn) a

variable {a₀ b₀ : ℝ} (G : Global M F (packetFamily M d) a₀ b₀)

theorem inv_lensY (a b T : ℝ) : Inv (ambK M)
    (lensY (descentOf G.lipschitz G.nonzero G.differentiable G.supported G.nonpos) a b T) :=
  Finsler.LensK.inv_lensY (ambK M) (deformed_rho hd hkn) (deformed_sigma hd hkn)
    _ G.rho G.sigma a b T

theorem inv_lensN (a T : ℝ) : Inv (ambK M)
    (lensN (descentOf G.lipschitz G.nonzero G.differentiable G.supported G.nonpos) a T) :=
  Finsler.LensK.inv_lensN (ambK M) (deformed_rho hd hkn) (deformed_sigma hd hkn)
    _ G.rho G.sigma a T

def orbitBig (d : ι → Packet n (2 * M)) (i : ι) : Set (Om n (2 * M)) :=
  (d i).big ∪ (reversePacket M (d i)).big

omit hkn in
theorem orbitBig_open (i : ι) : IsOpen (orbitBig d i) :=
  ((hd i).1.1.2.2.2.2.2.2.2.2.2.2.2.2.1).union
    ((hd i).2.1.2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem orbitBig_invariant (i : ι) : Inv (ambK M) (orbitBig d i) := by
  have hp := family_half M F hfin s hs k N hd hkn (i, true)
  have hn := family_half M F hfin s hs k N hd hkn (i, false)
  constructor
  · intro Q hQ
    rcases hQ with hQ | hQ
    · right
      change (ambK M).ρ ((ambK M).ρ Q) ∈ (d i).big
      rwa [(ambK M).ρρ]
    · exact Or.inl hQ
  · intro Q hQ
    rcases hQ with hQ | hQ
    · exact Or.inl ((hp.2.2.2.2.1 Q).mpr hQ)
    · exact Or.inr ((hn.2.2.2.2.1 Q).mpr hQ)

omit hkn in
theorem orbitBig_disjoint
    {U : ι → Set (ZMod (2 * M) → Ambient n)} (hsub : ∀ i, (d i).U ⊆ U i)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hUr : ∀ i j, Disjoint (U i) (revA (2 * M) ⁻¹' U j))
    (i j : ι) (hij : i ≠ j) : Disjoint (orbitBig d i) (orbitBig d j) := by
  have han := family_analytic M F hfin s hs k N hd
  have hb : ∀ o₁ o₂ : Bool, Disjoint (packetFamily M d (i, o₁)).big
      (packetFamily M d (j, o₂)).big := by
    intro o₁ o₂
    apply Set.disjoint_left.mpr
    intro Q hQi hQj
    have hi := (han (i, o₁)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hQi
    have hj := (han (j, o₂)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hQj
    exact Set.disjoint_left.mp
      (family_disjoint M hsub hU hUr (i, o₁) (j, o₂) (fun he => hij (Prod.mk.inj he).1))
      ((han (i, o₁)).2.2.2.2.2.2.1 hi) ((han (j, o₂)).2.2.2.2.2.2.1 hj)
  exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hb true true, hb true false⟩,
    disjoint_union_right.mpr ⟨hb false true, hb false false⟩⟩

omit hkn in
theorem orbitBig_covers_critical (p : ι × Bool) (Q : Om n (2 * M))
    (hQ : Q.1 ∈ (packetFamily M d p).C) : Q ∈ orbitBig d p.1 := by
  have han := family_analytic M F hfin s hs k N hd p
  have hsmall := han.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hQ
  have hbig := han.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hsmall
  rcases p with ⟨i, o⟩
  cases o
  · exact Or.inr hbig
  · exact Or.inl hbig

end

end Finsler.PacketSymmetry
