module

public import Finsler.Geometry.LabelAmbient
public import Finsler.Topology.LensTransport
public import Finsler.Topology.ProductModel
public import Finsler.Topology.ProductShift
public import Finsler.Topology.LensCore
public import Finsler.Topology.ModelTrap

/-! The flow of a field agreeing with the ambient split field, read in frame coordinates. The
frame coordinates cOf Q = (zOf Q, xiOf Q) are a left inverse of the coordinate map near every
point with invertible frame coordinates, so the derivative of cOf in the direction of the
ambient split field is the split field (V₀(z), J ξ). Hence, if the orbit of a globally Lipschitz
field V which agrees with the ambient split field on a set U stays in U, with invertible frame
coordinates, up to a time T, its coordinates solve the equation of the split field, and by
uniqueness of solutions they are the product curve (the flow of V₀ times (e^t x, e^{-t} y)).
This is the converse of the identification of v0.117, which starts from the product curve. -/

@[expose] public section

namespace Finsler.LabelTransport

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)

/-- The frame coordinates are differentiable where they are invertible. -/
theorem cOf_differentiableAt (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))) :
    DifferentiableAt ℝ (cOf m N G₁ G₂ ψ) Q :=
  ((zOf (n := n) m N).differentiableAt).prodMk
    ((xiOf_contDiffAt m N G₁ G₂ ψ hG₁ hG₂ hQ).differentiableAt (by simp))

/-- Near a point with invertible frame coordinates, cOf ∘ coord is the identity. -/
theorem cOf_coord_eventuallyEq (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {z : ZMod N → Ambient n} (hz : IsUnit (matA m N G₁ G₂ ψ z)) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    (cOf m N G₁ G₂ ψ ∘ coord m N G₁ G₂) =ᶠ[𝓝 (z, ξ)] id := by
  have hO : IsOpen (Prod.fst ⁻¹' {z : ZMod N → Ambient n | IsUnit (matA m N G₁ G₂ ψ z)} :
      Set ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)))) :=
    (isOpen_isUnit_root m N G₁ G₂ ψ hG₁ hG₂).preimage continuous_fst
  filter_upwards [hO.mem_nhds (show (z, ξ) ∈ Prod.fst ⁻¹' _ from hz)] with q hq
  obtain ⟨h1, h2⟩ := inverse_coord m N G₁ G₂ ψ hq q.2
  exact Prod.ext h1 h2

/-- **The derivative of the frame coordinates along the ambient split field** is the split
field. -/
theorem fderiv_cOf_splitW (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Q : ZMod (m * N) → Ambient n} (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q))) :
    fderiv ℝ (cOf m N G₁ G₂ ψ) Q (splitW m N G₁ G₂ ψ V₀ Q) =
      (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q)) := by
  have hc := coord_inverse m N G₁ G₂ ψ hQ
  have hcd : DifferentiableAt ℝ (coord m N G₁ G₂) (zOf m N Q, xiOf m N G₁ G₂ ψ Q) :=
    ((coord_contDiff m N G₁ G₂ hG₁ hG₂).differentiable (by simp)) _
  have hd' : DifferentiableAt ℝ (cOf m N G₁ G₂ ψ)
      (coord m N G₁ G₂ (zOf m N Q, xiOf m N G₁ G₂ ψ Q)) := by
    rw [hc]
    exact cOf_differentiableAt m N G₁ G₂ ψ hG₁ hG₂ hQ
  have h := (hd'.hasFDerivAt.comp (zOf m N Q, xiOf m N G₁ G₂ ψ Q) hcd.hasFDerivAt).fderiv
  have he := (cOf_coord_eventuallyEq m N G₁ G₂ ψ hG₁ hG₂ hQ
    (xiOf m N G₁ G₂ ψ Q)).fderiv_eq (𝕜 := ℝ)
  rw [he, fderiv_id, hc] at h
  have h2 := congrArg (fun L => L (V₀ (zOf m N Q), swapJ (xiOf m N G₁ G₂ ψ Q))) h
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply] at h2
  rw [h2]
  rfl

/-- The split field on the product is Lipschitz if V₀ is. -/
theorem lipschitz_split {K₀ : ℝ≥0} (hV₀ : LipschitzWith K₀ V₀) :
    ∃ K : ℝ≥0, LipschitzWith K (fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
      ((V₀ q.1, swapJ q.2) : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)))) :=
  ⟨_, (hV₀.comp LipschitzWith.prod_fst).prodMk
      ((swapJ (b := b) (p := p)).lipschitzWith.comp LipschitzWith.prod_snd)⟩

/-- **The coordinates of an orbit near the critical circle are the product curve.** -/
theorem cOf_globalSolution (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0}
    (hV : LipschitzWith K V) {U : Set (ZMod (m * N) → Ambient n)}
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {K₀ : ℝ≥0} (hV₀ : LipschitzWith K₀ V₀)
    (Q : ZMod (m * N) → Ambient n) {T : ℝ}
    (hin : ∀ t ∈ Icc 0 T, ODE.globalSolution V hV Q t ∈ U ∧
      IsUnit (matA m N G₁ G₂ ψ (zOf m N (ODE.globalSolution V hV Q t)))) :
    ∀ t ∈ Icc 0 T, cOf m N G₁ G₂ ψ (ODE.globalSolution V hV Q t) =
      prodCurve N V₀ hV₀ (zOf m N Q) (xiOf m N G₁ G₂ ψ Q) t := by
  obtain ⟨KY, hY⟩ := lipschitz_split N V₀ (b := b) (p := p) hV₀
  set Y := fun q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ)) =>
    ((V₀ q.1, swapJ q.2) : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) with hYdef
  have hc : ∀ s ∈ Icc 0 T, HasDerivAt (fun r => cOf m N G₁ G₂ ψ (ODE.globalSolution V hV Q r))
      (Y (cOf m N G₁ G₂ ψ (ODE.globalSolution V hV Q s))) s := by
    intro s hs
    obtain ⟨hsU, hsu⟩ := hin s hs
    have h1 := (cOf_differentiableAt m N G₁ G₂ ψ hG₁ hG₂ hsu).hasFDerivAt.comp_hasDerivAt s
      (ODE.hasDerivAt_globalSolution V hV Q s)
    rw [hU _ hsU, fderiv_cOf_splitW m N G₁ G₂ ψ V₀ hG₁ hG₂ hsu] at h1
    exact h1
  have hp : ∀ s, HasDerivAt (prodCurve N V₀ hV₀ (zOf m N Q) (xiOf m N G₁ G₂ ψ Q))
      (Y (prodCurve N V₀ hV₀ (zOf m N Q) (xiOf m N G₁ G₂ ψ Q) s)) s := fun s =>
    hasDerivAt_prodCurve N V₀ hV₀ _ _ s
  intro t ht
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ y => Y y) (s := fun _ => univ)
    (K := KY) (fun _ _ => hY.lipschitzOnWith)
    (fun s hs => (hc s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hc s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => trivial)
    ((continuous_iff_continuousAt.mpr fun s => (hp s).continuousAt).continuousOn)
    (fun s _ => (hp s).hasDerivWithinAt)
    (fun _ _ => trivial)
    (by rw [ODE.globalSolution_zero, prodCurve_zero]; rfl)
  exact heq ht

section Transport

open CategoryTheory Finsler.FlowLens Finsler.ProductModel Finsler.AmbientDescent
open Finsler.LabelDeform Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.LensContinuation

/-- Euclidean coefficients back to frame coefficients. -/
def unE (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)) :
    (Fin b → ℝ) × (Fin p → ℝ) :=
  ((EuclideanSpace.equiv (Fin b) ℝ) u, (EuclideanSpace.equiv (Fin p) ℝ) y)

omit [NeZero m] [NeZero N] in
theorem unE_euc (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : unE (eucX ξ) (eucY ξ) = ξ :=
  Prod.ext ((EuclideanSpace.equiv (Fin b) ℝ).apply_symm_apply ξ.1)
    ((EuclideanSpace.equiv (Fin p) ℝ).apply_symm_apply ξ.2)

omit [NeZero m] [NeZero N] in
theorem eucX_unE (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)) :
    eucX (unE u y) = u := (EuclideanSpace.equiv (Fin b) ℝ).symm_apply_apply u

omit [NeZero m] [NeZero N] in
theorem eucY_unE (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)) :
    eucY (unE u y) = y := (EuclideanSpace.equiv (Fin p) ℝ).symm_apply_apply y

omit [NeZero m] [NeZero N] in
theorem unE_smul (s t : ℝ) (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)) :
    unE (s • u) (t • y) = (s • (unE u y).1, t • (unE u y).2) :=
  Prod.ext (map_smul _ _ _) (map_smul _ _ _)

variable (Z₀ : Set (ZMod N → Ambient n)) (U : Set (ZMod (m * N) → Ambient n)) (ρ : ℝ)

/-- The label set on the ambient polygons. -/
def labelSetA : Set (Om n (m * N)) :=
  {Q | IsUnit (matA m N G₁ G₂ ψ (zOf m N Q.1)) ∧ zOf m N Q.1 ∈ Z₀ ∧
    ‖eucX (xiOf m N G₁ G₂ ψ Q.1)‖ < ρ ∧ ‖eucY (xiOf m N G₁ G₂ ψ Q.1)‖ < ρ ∧ Q.1 ∈ U}

/-- The label set in the product model. -/
def labelSetM : Set (Model (Om n N) b (EuclideanSpace ℝ (Fin p))) :=
  {w | IsUnit (matA m N G₁ G₂ ψ w.1.1) ∧ w.1.1 ∈ Z₀ ∧ ‖w.2.1‖ < ρ ∧ ‖w.2.2‖ < ρ ∧
    coord m N G₁ G₂ (w.1.1, unE w.2.1 w.2.2) ∈ U ∧
    ∀ j, coord m N G₁ G₂ (w.1.1, unE w.2.1 w.2.2) j ≠ 0}

variable {Z₀ U ρ}

/-- The coordinates of a point of the ambient label set, as a point of the product model. -/
def toModel (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0) (Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ) :
    labelSetM m N G₁ G₂ ψ Z₀ U ρ :=
  ⟨(⟨zOf m N Q.1.1, hZ₀ _ Q.2.2.1⟩, eucX (xiOf m N G₁ G₂ ψ Q.1.1),
      eucY (xiOf m N G₁ G₂ ψ Q.1.1)), by
    obtain ⟨hu, hz, hx, hy, hU⟩ := Q.2
    have hc : coord m N G₁ G₂ (zOf m N Q.1.1,
        unE (eucX (xiOf m N G₁ G₂ ψ Q.1.1)) (eucY (xiOf m N G₁ G₂ ψ Q.1.1))) = Q.1.1 := by
      rw [unE_euc]
      exact coord_inverse m N G₁ G₂ ψ hu
    exact ⟨hu, hz, hx, hy, by rw [hc]; exact hU, by rw [hc]; exact Q.1.2⟩⟩

/-- The point of the ambient label set with given coordinates in the product model. -/
def ofModel (w : labelSetM m N G₁ G₂ ψ Z₀ U ρ) : labelSetA m N G₁ G₂ ψ Z₀ U ρ :=
  ⟨⟨coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2), w.2.2.2.2.2.2⟩, by
    obtain ⟨hu, hz, hx, hy, hU, -⟩ := w.2
    obtain ⟨h1, h2⟩ := inverse_coord m N G₁ G₂ ψ hu (unE w.1.2.1 w.1.2.2)
    refine ⟨?_, ?_, ?_, ?_, hU⟩
    · change IsUnit (matA m N G₁ G₂ ψ (zOf m N (coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2))))
      rw [h1]
      exact hu
    · change zOf m N (coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2)) ∈ Z₀
      rw [h1]
      exact hz
    · change ‖eucX (xiOf m N G₁ G₂ ψ (coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2)))‖ < ρ
      rw [h2, eucX_unE]
      exact hx
    · change ‖eucY (xiOf m N G₁ G₂ ψ (coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2)))‖ < ρ
      rw [h2, eucY_unE]
      exact hy⟩

/-- **The label sets are homeomorphic.** -/
def labelHomeo (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂) (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0) :
    labelSetA m N G₁ G₂ ψ Z₀ U ρ ≃ₜ labelSetM m N G₁ G₂ ψ Z₀ U ρ where
  toFun := toModel m N G₁ G₂ ψ hZ₀
  invFun := ofModel m N G₁ G₂ ψ
  left_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    change coord m N G₁ G₂ (zOf m N Q.1.1,
      unE (eucX (xiOf m N G₁ G₂ ψ Q.1.1)) (eucY (xiOf m N G₁ G₂ ψ Q.1.1))) = Q.1.1
    rw [unE_euc]
    exact coord_inverse m N G₁ G₂ ψ Q.2.1
  right_inv w := by
    obtain ⟨h1, h2⟩ := inverse_coord m N G₁ G₂ ψ w.2.1 (unE w.1.2.1 w.1.2.2)
    apply Subtype.ext
    refine Prod.ext (Subtype.ext h1) (Prod.ext ?_ ?_)
    · change eucX (xiOf m N G₁ G₂ ψ (coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2))) = w.1.2.1
      rw [h2, eucX_unE]
    · change eucY (xiOf m N G₁ G₂ ψ (coord m N G₁ G₂ (w.1.1.1, unE w.1.2.1 w.1.2.2))) = w.1.2.2
      rw [h2, eucY_unE]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hz : Continuous fun Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ => zOf m N Q.1.1 :=
      (zOf (n := n) m N).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hxi : Continuous fun Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ => xiOf m N G₁ G₂ ψ Q.1.1 := by
      rw [continuous_iff_continuousAt]
      intro Q
      have hv : ContinuousAt (fun Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ => Q.1.1) Q :=
        (continuous_subtype_val.comp continuous_subtype_val).continuousAt
      exact ContinuousAt.comp (g := xiOf m N G₁ G₂ ψ)
        (f := fun Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ => Q.1.1) (x := Q)
        (xiOf_contDiffAt m N G₁ G₂ ψ hG₁ hG₂ Q.2.1).continuousAt hv
    exact (hz.subtype_mk _).prodMk ((eucX.continuous.comp hxi).prodMk (eucY.continuous.comp hxi))
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have h1 : Continuous fun w : labelSetM m N G₁ G₂ ψ Z₀ U ρ => w.1.1.1 :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun w : labelSetM m N G₁ G₂ ψ Z₀ U ρ => unE w.1.2.1 w.1.2.2 :=
      ((EuclideanSpace.equiv (Fin b) ℝ).continuous.comp
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))).prodMk
      ((EuclideanSpace.equiv (Fin p) ℝ).continuous.comp
        (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
    exact (coord_contDiff m N G₁ G₂ hG₁ hG₂).continuous.comp (h1.prodMk h2)

section Systems

variable (F : ReversibleMetric n)
  {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0} (hL : LipschitzWith K V)
  (hV0 : ∀ P : ZMod (m * N) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)
  {K₀ : ℝ≥0} (hL₀ : LipschitzWith K₀ V₀) (hV00 : ∀ z : ZMod N → Ambient n, V₀ z ≠ 0 → ∀ j, z j ≠ 0)
  {O₀ : Set (ZMod N → Ambient n)}
  (hg₀ : ∀ z ∈ O₀, DifferentiableAt ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z)
  (hsupp₀ : ∀ z, V₀ z ≠ 0 → z ∈ O₀)
  (hle₀ : ∀ z ∈ O₀, fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z (V₀ z) ≤ 0)
  (hh : Continuous fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)

/-- The root energy of a point of the product model is the energy along the zero section. -/
theorem energy_model (w : Model (Om n N) b (EuclideanSpace ℝ (Fin p))) :
    (cone b (EuclideanSpace ℝ (Fin p)) hh).energy w =
      model m N F G₁ G₂ (w.1.1, unE w.2.1 w.2.2) := by
  rw [cone_energy]
  unfold model sqX sqY
  rw [psi_zero, eucX_unE, eucY_unE]

/-- **The functions correspond on the label sets.** -/
theorem energy_toModel {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)}
    {ρ : ℝ} (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ, g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (w : labelSetA m N G₁ G₂ ψ Z₀ U ρ) :
    (cone b (EuclideanSpace ℝ (Fin p)) hh).energy (toModel m N G₁ G₂ ψ hZ₀ w : _) = g w.1.1 := by
  rw [energy_model, hmodel w.1 w.2]
  change model m N F G₁ G₂ (zOf m N w.1.1,
    unE (eucX (xiOf m N G₁ G₂ ψ w.1.1)) (eucY (xiOf m N G₁ G₂ ψ w.1.1))) = _
  rw [unE_euc]
  rfl

/-- **The flows correspond along orbits in the ambient label set.** -/
theorem flow_corr_amb (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ, g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {T : ℝ} (hT : 0 ≤ T)
    (w : labelSetA m N G₁ G₂ ψ Z₀ U ρ)
    (hw : ∀ s, 0 ≤ s → s ≤ T → (descentOf hL hV0 hg hsupp hle).flow s w.1 ∈
      labelSetA m N G₁ G₂ ψ Z₀ U ρ) :
    (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
        ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow T
          (toModel m N G₁ G₂ ψ hZ₀ w : _)) =
      g ((descentOf hL hV0 hg hsupp hle).flow T w.1).1 := by
  have hflow : ∀ s, 0 ≤ s → ((descentOf hL hV0 hg hsupp hle).flow s w.1).1 =
      ODE.globalSolution V hL w.1.1 s := by
    intro s hs
    change ODE.globalSolution V hL w.1.1 (max s 0) = _
    rw [max_eq_left hs]
  have hin : ∀ s ∈ Icc 0 T, ODE.globalSolution V hL w.1.1 s ∈ U ∧
      IsUnit (matA m N G₁ G₂ ψ (zOf m N (ODE.globalSolution V hL w.1.1 s))) := by
    intro s hs
    have h := hw s hs.1 hs.2
    rw [← hflow s hs.1]
    exact ⟨h.2.2.2.2, h.1⟩
  have hc := cOf_globalSolution m N G₁ G₂ ψ V₀ hG₁ hG₂ hL hU hL₀ w.1.1 hin T ⟨hT, le_rfl⟩
  rw [hmodel _ (hw T hT le_rfl), hflow T hT, hc, energy_model]
  rw [descent_flow]
  change model m N F G₁ G₂ (ODE.globalSolution V₀ hL₀ (zOf m N w.1.1) (max T 0),
    unE (Real.exp T • eucX (xiOf m N G₁ G₂ ψ w.1.1))
      (Real.exp (-T) • eucY (xiOf m N G₁ G₂ ψ w.1.1))) = _
  rw [max_eq_left hT, unE_smul, unE_euc]
  rfl

/-- **The flows correspond along orbits in the label set of the product model.** -/
theorem flow_corr_model (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ, g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {T : ℝ} (hT : 0 ≤ T)
    (w : labelSetA m N G₁ G₂ ψ Z₀ U ρ)
    (hw : ∀ s, 0 ≤ s → s ≤ T →
      (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s
        (toModel m N G₁ G₂ ψ hZ₀ w : _) ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ) :
    (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
        ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow T
          (toModel m N G₁ G₂ ψ hZ₀ w : _)) =
      g ((descentOf hL hV0 hg hsupp hle).flow T w.1).1 := by
  set z := zOf m N w.1.1 with hz
  set ξ := xiOf m N G₁ G₂ ψ w.1.1 with hξ
  have hpt : ∀ s, 0 ≤ s →
      ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s
        (toModel m N G₁ G₂ ψ hZ₀ w : _)).1.1 = (prodCurve N V₀ hL₀ z ξ s).1 ∧
      unE ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s
          (toModel m N G₁ G₂ ψ hZ₀ w : _)).2.1
        ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s
          (toModel m N G₁ G₂ ψ hZ₀ w : _)).2.2 = (prodCurve N V₀ hL₀ z ξ s).2 := by
    intro s hs
    rw [descent_flow]
    refine ⟨?_, ?_⟩
    · change ODE.globalSolution V₀ hL₀ z (max s 0) = _
      rw [max_eq_left hs]
      rfl
    · change unE (Real.exp s • eucX ξ) (Real.exp (-s) • eucY ξ) = _
      rw [unE_smul, unE_euc]
      rfl
  have hpc : ∀ s ∈ Icc 0 T, coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ s) ∈ U ∧
      IsUnit (matA m N G₁ G₂ ψ (prodCurve N V₀ hL₀ z ξ s).1) := by
    intro s hs
    have h := hw s hs.1 hs.2
    obtain ⟨h1, h2⟩ := hpt s hs.1
    have e : coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ s) =
        coord m N G₁ G₂ (((descent b (EuclideanSpace ℝ (Fin p))
          (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s (toModel m N G₁ G₂ ψ hZ₀ w : _)).1.1,
          unE ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow
            s (toModel m N G₁ G₂ ψ hZ₀ w : _)).2.1
          ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow
            s (toModel m N G₁ G₂ ψ hZ₀ w : _)).2.2) := by
      rw [h1, h2]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact h.2.2.2.2.1
    · rw [← h1]
      exact h.1
  have hγ := globalSolution_eq_coord m N G₁ G₂ ψ V₀ hG₁ hG₂ hL hU hL₀ z ξ hpc T ⟨hT, le_rfl⟩
  have hQ : coord m N G₁ G₂ (z, ξ) = w.1.1 := coord_inverse m N G₁ G₂ ψ w.2.1
  rw [hQ] at hγ
  -- the end point as a point of the ambient label set
  set wT : labelSetM m N G₁ G₂ ψ Z₀ U ρ :=
    ⟨(descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow T
      (toModel m N G₁ G₂ ψ hZ₀ w : _), hw T hT le_rfl⟩ with hwT
  have hcoordT : (ofModel m N G₁ G₂ ψ wT).1.1 = coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ T) := by
    change coord m N G₁ G₂ (wT.1.1.1, unE wT.1.2.1 wT.1.2.2) = _
    obtain ⟨h1, h2⟩ := hpt T hT
    rw [hwT]
    rw [h1, h2]
  have hflowT : ((descentOf hL hV0 hg hsupp hle).flow T w.1).1 =
      coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ T) := by
    change ODE.globalSolution V hL w.1.1 (max T 0) = _
    rw [max_eq_left hT]
    exact hγ
  rw [hflowT, ← hcoordT, hmodel _ (ofModel m N G₁ G₂ ψ wT).2, hcoordT]
  obtain ⟨hu, -⟩ := hpc T ⟨hT, le_rfl⟩
  obtain ⟨hc1, hc2⟩ := inverse_coord m N G₁ G₂ ψ (hpc T ⟨hT, le_rfl⟩).2
    (prodCurve N V₀ hL₀ z ξ T).2
  have hcOf : cOf m N G₁ G₂ ψ (coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ T)) =
      prodCurve N V₀ hL₀ z ξ T := by
    rw [← Prod.mk.eta (p := prodCurve N V₀ hL₀ z ξ T)]
    exact Prod.ext hc1 hc2
  rw [hcOf, energy_model]
  obtain ⟨h1, h2⟩ := hpt T hT
  rw [h1, h2]

/-- **Transport of a label to the product model.** If whole orbits up to the lens time stay in
the label sets in both systems (trapping), the lens pair of the deformed penalized energy in
the ambient label set has the cohomology of the lens pair of the product model in its label
set. -/
theorem label_transport (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ,
      g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {a c T : ℝ} (hT : 0 ≤ T)
    (hS₁ : ∀ w, w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ → g w.1 < c →
      a ≤ g ((descentOf hL hV0 hg hsupp hle).flow T w).1 → ∀ s, 0 ≤ s → s ≤ T →
      (descentOf hL hV0 hg hsupp hle).flow s w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ)
    (hS₂ : ∀ w, w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ →
      (cone b (EuclideanSpace ℝ (Fin p)) hh).energy w < c →
      a ≤ (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
        ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow T w) →
      ∀ s, 0 ≤ s → s ≤ T →
        (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s w ∈
          labelSetM m N G₁ G₂ ψ Z₀ U ρ) (k : ℕ) :
    Nonempty (H (triv (pairOf (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
        (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T))) k ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
        (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh)
        (labelSetM m N G₁ G₂ ψ Z₀ U ρ) a c T))) k) := by
  have hbij := Finsler.LensTransport.part_bijective (descentOf hL hV0 hg hsupp hle)
    (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh)
    (labelHomeo m N G₁ G₂ ψ hG₁ hG₂ hZ₀)
    (fun w => energy_toModel m N G₁ G₂ ψ F hh hZ₀ hmodel w) hS₁ hS₂
    (fun w hw => flow_corr_amb m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00 hg₀ hsupp₀ hle₀ hh
      hG₁ hG₂ hZ₀ hmodel hU hT w hw)
    (fun w hw => flow_corr_model m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00 hg₀ hsupp₀ hle₀
      hh hG₁ hG₂ hZ₀ hmodel hU hT w hw) k
  exact ⟨(LinearEquiv.ofBijective _ hbij).symm⟩

include hh in
/-- **A label is the root label shifted by the normal index.** For tight cuts a ≤ c (in the
sense of the normal shift for product models over the root band) with 4(c - a) < ρ², T ≥ 1, if
whole orbits stay in the ambient label set (trapping in the ambient system) and whole orbits of
the root descent stay in Z₀ for the widened cuts, the lens pair of the deformed penalized energy
in the ambient label set has in degree n + b the dimension of the lens pair of the root
functional in Z₀ in degree n, and no cohomology below the degree b. -/
theorem label_shift (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0) (hρ : 0 < ρ)
    (hZρ : ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)), ‖u‖ < ρ →
      ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧ coord m N G₁ G₂ (z, unE u y) ∈ U ∧
        ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ,
      g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q)
    {a₀ b₀ : ℝ} {Wrest : Set (Om n N)} (hsel : IsOpen {z : Om n N | z.1 ∈ Z₀})
    (hrest : IsOpen Wrest) (hdis : Disjoint {z : Om n N | z.1 ∈ Z₀} Wrest)
    (hK : IsCompact {z : Om n N | a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀})
    (hstrict : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → z ∉ {z : Om n N | z.1 ∈ Z₀} ∪ Wrest →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c T : ℝ, 1 ≤ T → a ≤ c → 4 * (c - a) < ρ ^ 2 →
      a₀ ≤ a - (c - a) / (Real.exp (2 * T) - 1) → c + (c - a) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (c + (c - a) / (Real.exp (2 * T) - 1)) - (a - (c - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ z : Om n N, c ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ c + (c - a) / (Real.exp (2 * T) - 1) →
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
          (m : ℝ) ^ 2 * pen F N (1 / m) z.1) →
      (∀ w, w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ → g w.1 < c →
        a ≤ g ((descentOf hL hV0 hg hsupp hle).flow T w).1 → ∀ s, 0 ≤ s → s ≤ T →
        (descentOf hL hV0 hg hsupp hle).flow s w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ) →
      (∀ z : Om n N, z ∈ {z : Om n N | z.1 ∈ Z₀} →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 < c + (c - a) / (Real.exp (2 * T) - 1) →
        a - (c - a) / (Real.exp (2 * T) - 1) ≤
          (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow T z).1 →
        ∀ s, 0 ≤ s → s ≤ T → (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow s z ∈
          {z : Om n N | z.1 ∈ Z₀}) →
      (∀ k : ℕ, Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
          (fun Q : Om n (m * N) => g Q.1) (descentOf hL hV0 hg hsupp hle)
          (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T))) (k + b)) =
        Module.finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
          baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1) {z : Om n N | z.1 ∈ Z₀} c ∩
            baseO (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) a T ⊆
          baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
            {z : Om n N | z.1 ∈ Z₀} c))) k)) ∧
      (∀ k : ℕ, k < b → ∀ x : H (triv (pairOf (partY_sub_partU
          (fun Q : Om n (m * N) => g Q.1) (descentOf hL hV0 hg hsupp hle)
          (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T))) k, x = 0) := by
  obtain ⟨d, hd, hshift⟩ := Finsler.ProductShift.exists_shift
    (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) b (EuclideanSpace ℝ (Fin p)) hh hsel hrest hdis hK hstrict
  refine ⟨d, hd, fun a c T hT hac h4 ha₀ hb₀ hd' hstrip hS₁ hbase => ?_⟩
  obtain ⟨hsh1, hsh2⟩ := hshift a c T hT hac ha₀ hb₀ hd' hstrip
  -- the label set of the model contains the points over Z₀ with small fibres
  have hS : ∀ w : Model (Om n N) b (EuclideanSpace ℝ (Fin p)), w.1 ∈ {z : Om n N | z.1 ∈ Z₀} →
      ‖w.2.1‖ < ρ → ‖w.2.2‖ < ρ → w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ := by
    intro w hw hu hy
    obtain ⟨h1, h2, h3⟩ := hZρ w.1.1 hw w.2.1 w.2.2 hu hy
    exact ⟨h1, hw, hu, hy, h2, h3⟩
  have hS' : ∀ w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ, w.1 ∈ {z : Om n N | z.1 ∈ Z₀} ∧ ‖w.2.2‖ < ρ :=
    fun w hw => ⟨hw.2.1, hw.2.2.2.1⟩
  -- trapping in the model
  have hS₂ := fun w (hw : w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ) hwc hwa s hs hsT =>
    Finsler.ModelTrap.orbit_stay b (EuclideanSpace ℝ (Fin p))
      (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh hS hS' hT (by nlinarith) hbase w hw hwc hwa s hs hsT
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  -- the core of the model label set is that of all fibres over Z₀
  set a' : ℝ := a - (ρ ^ 2 - 4 * (c - a)) / 4 with ha'def
  have ha' : a' < a := by
    rw [ha'def]
    linarith
  have hca' : 2 * (c - a') < ρ ^ 2 := by
    rw [ha'def]
    linarith
  have hcore : ∀ w, (cone b (EuclideanSpace ℝ (Fin p)) hh).energy w < c →
      a' < (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
        ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow T w) →
      (w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ ↔ w ∈ over b (EuclideanSpace ℝ (Fin p))
        {z : Om n N | z.1 ∈ Z₀}) := fun w hw hw' =>
    Finsler.ModelTrap.core_iff b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀)
      hh hS (fun w hw => (hS' w hw).1) hρ hT hca' w hw hw'
  have he₁ := fun k => label_transport m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00 hg₀ hsupp₀
    hle₀ hh hG₁ hG₂ hZ₀ hmodel hU hT0 hS₁ hS₂ k
  have he₂ := fun k => Finsler.LensCore.nonempty_core_equiv
    (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh)
    (Finsler.ConeLens.energy_continuous (cone b (EuclideanSpace ℝ (Fin p)) hh)) ha' hcore k
  refine ⟨fun k => ?_, fun k hk x => ?_⟩
  · obtain ⟨e₁⟩ := he₁ (k + b)
    obtain ⟨e₂⟩ := he₂ (k + b)
    rw [e₁.finrank_eq, e₂.finrank_eq]
    exact hsh1 k
  · obtain ⟨e₁⟩ := he₁ k
    obtain ⟨e₂⟩ := he₂ k
    have hz := hsh2 k hk (e₂ (e₁ x))
    have h1 : e₁ x = 0 := (LinearEquiv.map_eq_zero_iff e₂).mp hz
    exact (LinearEquiv.map_eq_zero_iff e₁).mp h1

end Systems

section Margin

/-- A flow whose field is bounded by κ moves points by at most κ t in time t. -/
theorem norm_globalSolution_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {X : E → E} {K : ℝ≥0} (hX : LipschitzWith K X) {κ : ℝ}
    (hκ : ∀ x, ‖X x‖ ≤ κ) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖ODE.globalSolution X hX x t - x‖ ≤ κ * t := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := ODE.globalSolution X hX x)
    (a := 0) (b := t) (C := κ)
    (fun s _ => (ODE.hasDerivAt_globalSolution X hX x s).hasDerivWithinAt)
    (fun s _ => hκ _) t ⟨ht, le_rfl⟩
  rwa [ODE.globalSolution_zero, sub_zero] at h

variable (F : ReversibleMetric n)
  {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0} (hL : LipschitzWith K V)
  (hV0 : ∀ P : ZMod (m * N) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)
  {K₀ : ℝ≥0} (hL₀ : LipschitzWith K₀ V₀)

include hL₀ in
/-- **The margin of the ambient label sets.** If the root field is bounded by κ, every point
at distance at most κ from Z₀' lies in Z₀, ρ' e ≤ ρ, and the frame coordinates are invertible
with image in U and nonzero vertices over Z₀ for Euclidean coefficients below ρ, then the flow
of a field agreeing with the ambient split field on U keeps the points of the small label set
(Z₀', ρ') in the large label set (Z₀, ρ) up to the time one. -/
theorem ambient_margin (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ Z₀' : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ ρ' κ : ℝ}
    (hZρ : ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)), ‖u‖ < ρ →
      ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧ coord m N G₁ G₂ (z, unE u y) ∈ U ∧
        ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0)
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) (hκ : ∀ z, ‖V₀ z‖ ≤ κ)
    (hZ : ∀ z ∈ Z₀', ∀ z', ‖z' - z‖ ≤ κ → z' ∈ Z₀) (hρ : ρ' * Real.exp 1 ≤ ρ)
    (Q : Om n (m * N)) (hQ : Q ∈ labelSetA m N G₁ G₂ ψ Z₀' U ρ') (s : ℝ) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) :
    (descentOf hL hV0 hg hsupp hle).flow s Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ := by
  obtain ⟨hu, hz, hx, hy, hUQ⟩ := hQ
  set z := zOf m N Q.1 with hzdef
  set ξ := xiOf m N G₁ G₂ ψ Q.1 with hξdef
  have hρ' : 0 ≤ ρ' := (norm_nonneg _).trans hx.le
  -- the product curve stays over Z₀ with Euclidean coefficients below ρ
  have hpc : ∀ t ∈ Icc (0 : ℝ) 1, (prodCurve N V₀ hL₀ z ξ t).1 ∈ Z₀ ∧
      ‖eucX (prodCurve N V₀ hL₀ z ξ t).2‖ < ρ ∧ ‖eucY (prodCurve N V₀ hL₀ z ξ t).2‖ < ρ := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · apply hZ z hz
      have h1 := norm_globalSolution_sub_le hL₀ hκ z ht.1
      have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ z)
      calc ‖ODE.globalSolution V₀ hL₀ z t - z‖ ≤ κ * t := h1
        _ ≤ κ * 1 := mul_le_mul_of_nonneg_left ht.2 hκ0
        _ = κ := mul_one κ
    · change ‖eucX ((Real.exp t • ξ.1, Real.exp (-t) • ξ.2) : (Fin b → ℝ) × (Fin p → ℝ))‖ < ρ
      have e : eucX ((Real.exp t • ξ.1, Real.exp (-t) • ξ.2) : (Fin b → ℝ) × (Fin p → ℝ)) =
          Real.exp t • eucX ξ := by
        have e2 : ((Real.exp t • ξ.1, Real.exp (-t) • ξ.2) : (Fin b → ℝ) × (Fin p → ℝ)) =
            unE (Real.exp t • eucX ξ) (Real.exp (-t) • eucY ξ) := by
          rw [unE_smul, unE_euc]
        rw [e2, eucX_unE]
      rw [e, norm_smul, Real.norm_of_nonneg (Real.exp_pos t).le]
      calc Real.exp t * ‖eucX ξ‖ ≤ Real.exp 1 * ‖eucX ξ‖ :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (norm_nonneg _)
        _ < Real.exp 1 * ρ' := mul_lt_mul_of_pos_left hx (Real.exp_pos 1)
        _ ≤ ρ := by linarith [mul_comm ρ' (Real.exp 1)]
    · change ‖eucY ((Real.exp t • ξ.1, Real.exp (-t) • ξ.2) : (Fin b → ℝ) × (Fin p → ℝ))‖ < ρ
      have e : eucY ((Real.exp t • ξ.1, Real.exp (-t) • ξ.2) : (Fin b → ℝ) × (Fin p → ℝ)) =
          Real.exp (-t) • eucY ξ := by
        have e2 : ((Real.exp t • ξ.1, Real.exp (-t) • ξ.2) : (Fin b → ℝ) × (Fin p → ℝ)) =
            unE (Real.exp t • eucX ξ) (Real.exp (-t) • eucY ξ) := by
          rw [unE_smul, unE_euc]
        rw [e2, eucY_unE]
      rw [e, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
      have h2 : ρ' ≤ ρ := by
        have := Real.add_one_le_exp 1
        nlinarith
      calc Real.exp (-t) * ‖eucY ξ‖ ≤ 1 * ‖eucY ξ‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < ρ := by rw [one_mul]; exact lt_of_lt_of_le hy h2
  have hreg : ∀ t ∈ Icc (0 : ℝ) 1, coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ t) ∈ U ∧
      IsUnit (matA m N G₁ G₂ ψ (prodCurve N V₀ hL₀ z ξ t).1) := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hpc t ht
    obtain ⟨h4, h5, -⟩ := hZρ _ h1 _ _ h2 h3
    rw [unE_euc] at h5
    exact ⟨h5, h4⟩
  have hγ := globalSolution_eq_coord m N G₁ G₂ ψ V₀ hG₁ hG₂ hL hU hL₀ z ξ hreg s ⟨hs, hs1⟩
  have hQc : coord m N G₁ G₂ (z, ξ) = Q.1 := coord_inverse m N G₁ G₂ ψ hu
  rw [hQc] at hγ
  have hflow : ((descentOf hL hV0 hg hsupp hle).flow s Q).1 =
      coord m N G₁ G₂ (prodCurve N V₀ hL₀ z ξ s) := by
    change ODE.globalSolution V hL Q.1 (max s 0) = _
    rw [max_eq_left hs]
    exact hγ
  obtain ⟨h1, h2, h3⟩ := hpc s ⟨hs, hs1⟩
  obtain ⟨-, hu'⟩ := hreg s ⟨hs, hs1⟩
  obtain ⟨hc1, hc2⟩ := inverse_coord m N G₁ G₂ ψ hu' (prodCurve N V₀ hL₀ z ξ s).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hflow, hc1]
    exact hu'
  · rw [hflow, hc1]
    exact h1
  · rw [hflow, hc2]
    exact h2
  · rw [hflow, hc2]
    exact h3
  · rw [hflow]
    exact (hreg s ⟨hs, hs1⟩).1

end Margin

end Transport

end

end Finsler.LabelTransport
