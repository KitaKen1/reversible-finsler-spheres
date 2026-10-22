module

public import Finsler.Loop.NativeSequentialMiddleSeams
public import Finsler.Loop.NativeSequentialTripleComparison

/-! A REAL OPEN collar of each original excluded seam, chosen BEFORE
all GH powers/tests/degrees: BOTH actual original and common middle
loops lie in the SAME true positive short-length cut. Together with
the actual positive-split domain this covers the WHOLE raw-half source.
No uniform time width over the entire noncompact H1 space is assumed. -/
@[expose] public section
namespace Finsler.NativeSequentialCollarGeometry
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1SelfCutNeighborhood Finsler.NativeSequentialCutParameters
open Finsler.CochainComparison Finsler.NativeSequentialTripleComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev radius := NativeClosingArcPowerVanishing.radius m hm F
abbrev scale := NativeClosingArcPowerVanishing.supportScale m hm F
abbrev prefixSource := prefixDomain (m + 1) (radius m hm F)
abbrev suffixSource := suffixDomain (m + 1) (radius m hm F)

def prefixOriginal : prefixSource m hm F ⟶ triple (m + 1) := TopCat.ofHom
  ⟨fun z => (left (prefixInner (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z),
      right (prefixInner (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z), right z.val.1), by
    have hi := continuous_prefixInner (n := m + 1) (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)
    exact ((continuous_left (n := m + 1)).comp hi).prodMk
      (((continuous_right (n := m + 1)).comp hi).prodMk
        ((continuous_right (n := m + 1)).comp (continuous_fst.comp continuous_subtype_val)))⟩

def suffixOriginal : suffixSource m hm F ⟶ triple (m + 1) := TopCat.ofHom
  ⟨fun z => (left z.val.1, left (suffixInner (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z),
      right (suffixInner (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z)), by
    have hi := continuous_suffixInner (n := m + 1) (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)
    exact ((continuous_left (n := m + 1)).comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (((continuous_left (n := m + 1)).comp hi).prodMk ((continuous_right (n := m + 1)).comp hi))⟩

def prefixCommon : prefixSource m hm F ⟶ triple (m + 1) := TopCat.ofHom
  ⟨fun z => commonTriple (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)
    (NativeSequentialCutParameters.prefixCommon z),
    (commonTriple _).hom.continuous.comp continuous_prefixCommon⟩

def suffixCommon : suffixSource m hm F ⟶ triple (m + 1) := TopCat.ofHom
  ⟨fun z => commonTriple (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)
    (NativeSequentialCutParameters.suffixCommon z),
    (commonTriple _).hom.continuous.comp continuous_suffixCommon⟩

def prefixInterior : Set (prefixSource m hm F) := NativeSequentialPrefixMiddle.inputs (m + 1) (radius m hm F)
def suffixInterior : Set (suffixSource m hm F) := NativeSequentialSuffixMiddle.inputs (m + 1) (radius m hm F)

def prefixCollar : Set (prefixSource m hm F) := {z |
  SobolevLength.length F (prefixOriginal m hm F z).2.1 < scale m hm F ∧
    SobolevLength.length F (prefixCommon m hm F z).2.1 < scale m hm F}

def suffixCollar : Set (suffixSource m hm F) := {z |
  SobolevLength.length F (suffixOriginal m hm F z).2.1 < scale m hm F ∧
    SobolevLength.length F (suffixCommon m hm F z).2.1 < scale m hm F}

theorem prefix_interior_open : IsOpen (prefixInterior m hm F) := by
  apply isOpen_lt _ continuous_const
  fun_prop

theorem suffix_interior_open : IsOpen (suffixInterior m hm F) := by
  apply isOpen_lt continuous_const
  fun_prop

theorem prefix_collar_open : IsOpen (prefixCollar m hm F) :=
  (isOpen_lt ((SelfCutOscillation.continuous_length F).comp
    (continuous_fst.comp (continuous_snd.comp (prefixOriginal m hm F).hom.continuous))) continuous_const).inter
  (isOpen_lt ((SelfCutOscillation.continuous_length F).comp
    (continuous_fst.comp (continuous_snd.comp (prefixCommon m hm F).hom.continuous))) continuous_const)

theorem suffix_collar_open : IsOpen (suffixCollar m hm F) :=
  (isOpen_lt ((SelfCutOscillation.continuous_length F).comp
    (continuous_fst.comp (continuous_snd.comp (suffixOriginal m hm F).hom.continuous))) continuous_const).inter
  (isOpen_lt ((SelfCutOscillation.continuous_length F).comp
    (continuous_fst.comp (continuous_snd.comp (suffixCommon m hm F).hom.continuous))) continuous_const)

theorem prefix_seam_in_collar (z : NativeSequentialMiddleSeams.prefixSeam m hm F) :
    z.val ∈ prefixCollar m hm F := by
  constructor
  · have h := NativeClosingArcPowerVanishing.left_short m hm F (NativeSequentialMiddleSeams.prefixArc m hm F z)
    have he := congrArg (fun f => f z) (NativeSequentialMiddleSeams.prefix_arc_factor m hm F)
    change NativeClosingArcPowerVanishing.leftRetained m hm F (NativeSequentialMiddleSeams.prefixArc m hm F z) =
      NativeSequentialMiddleSeams.prefixOriginal m hm F z at he
    exact (congrArg (SobolevLength.length F) he).symm.trans_lt h
  · exact NativeOrderedDoubleCutDiagonal.middle_short m hm F (NativeSequentialMiddleSeams.prefixDiagonal m hm F z)

theorem suffix_seam_in_collar (z : NativeSequentialMiddleSeams.suffixSeam m hm F) :
    z.val ∈ suffixCollar m hm F := by
  constructor
  · have h := NativeClosingArcPowerVanishing.right_short m hm F (NativeSequentialMiddleSeams.suffixArc m hm F z)
    have he := congrArg (fun f => f z) (NativeSequentialMiddleSeams.suffix_arc_factor m hm F)
    change NativeClosingArcPowerVanishing.rightTested m hm F (NativeSequentialMiddleSeams.suffixArc m hm F z) =
      NativeSequentialMiddleSeams.suffixOriginal m hm F z at he
    exact (congrArg (SobolevLength.length F) he).symm.trans_lt h
  · exact NativeOrderedDoubleCutDiagonal.middle_short m hm F (NativeSequentialMiddleSeams.suffixDiagonal m hm F z)

theorem prefix_cover : prefixInterior m hm F ∪ prefixCollar m hm F = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases h : (z.val.2 : ℝ) < 1
  · exact Or.inl h
  · have he : (z.val.2 : ℝ) = 1 := le_antisymm z.val.2.property.2 (le_of_not_gt h)
    exact Or.inr (prefix_seam_in_collar m hm F ⟨z, he⟩)

theorem suffix_cover : suffixInterior m hm F ∪ suffixCollar m hm F = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases h : 0 < (z.val.2 : ℝ)
  · exact Or.inl h
  · have he : (z.val.2 : ℝ) = 0 := le_antisymm (le_of_not_gt h) z.val.2.property.1
    exact Or.inr (suffix_seam_in_collar m hm F ⟨z, he⟩)

theorem prefix_homotopy_short (s : _root_.unitInterval)
    (z : NativeSequentialPrefixMiddle.inputs (m + 1) (radius m hm F))
    (hz : z.val ∈ prefixCollar m hm F) :
    SobolevLength.length F ((prefixHomotopy (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)) (s, z)).2.1 < scale m hm F :=
  (prefix_middle_length _ F s z).trans_lt hz.2

theorem suffix_homotopy_short (s : _root_.unitInterval)
    (z : NativeSequentialSuffixMiddle.inputs (m + 1) (radius m hm F))
    (hz : z.val ∈ suffixCollar m hm F) :
    SobolevLength.length F ((suffixHomotopy (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)) (s, z)).2.1 < scale m hm F :=
  (suffix_middle_length _ F s z).trans_lt hz.2

end
end Finsler.NativeSequentialCollarGeometry
