module

public import Finsler.Topology.CupAssociativity
public import Finsler.Topology.CupCommutativity
public import Finsler.Topology.CupIteration

/-! Actual cup products at an explicitly specified total degree.
The real degree transports make the three-factor diagonal simplification
usable directly on the existing LEFT-associated fundamental cross. -/
@[expose] public section
namespace Finsler.CupAtDegree
open CategoryTheory SphereOddDegree Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def cup (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) : cohomologyZMod2 X N :=
  CupUnit.absoluteCast X h (cupZMod2 a b)

theorem cast_trans (X : TopCat.{0}) {a b c : ℕ} (h : a = b) (h' : b = c)
    (x : cohomologyZMod2 X a) :
    CupUnit.absoluteCast X h' (CupUnit.absoluteCast X h x) = CupUnit.absoluteCast X (h.trans h') x := by
  subst b
  subst c
  rfl

theorem cast_self (X : TopCat.{0}) (n : ℕ) (h : n = n) (x : cohomologyZMod2 X n) :
    CupUnit.absoluteCast X h x = x := rfl

theorem cast_add (X : TopCat.{0}) {a b : ℕ} (h : a = b) (x y : cohomologyZMod2 X a) :
    CupUnit.absoluteCast X h (x + y) = CupUnit.absoluteCast X h x + CupUnit.absoluteCast X h y := by
  subst b
  rfl

theorem add_left (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (a b : cohomologyZMod2 X p) (c : cohomologyZMod2 X q) :
    cup X p q N h (a + b) c = cup X p q N h a c + cup X p q N h b c := by
  have he : cupZMod2 (a + b) c = cupZMod2 a c + cupZMod2 b c :=
    map_add (cupHomologyLeft X p q (classRepr X q c) (classRepr_isCocycle X q c)).hom a b
  exact (congrArg (CupUnit.absoluteCast X h) he).trans (cast_add X h _ _)

theorem comm (X : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cup X p q N h a b = cup X q p N (by omega) b a := by
  subst N
  simpa only [cup, cast_self] using (CupCommutativity.comm X p q a b).symm

theorem assoc (X : TopCat.{0}) (p q r u v N : ℕ)
    (hu : p + q = u) (hv : q + r = v) (hL : u + r = N) (hR : p + v = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) (c : cohomologyZMod2 X r) :
    cup X u r N hL (cup X p q u hu a b) c = cup X p v N hR a (cup X q r v hv b c) := by
  subst u
  subst v
  subst N
  apply CupIteration.absoluteCast_injective X (Nat.add_assoc p q r)
  simpa only [cup, cast_self, cast_trans] using CupAssociativity.absolute_assoc X p q r a b c

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q N : ℕ) (h : p + q = N)
    (a : cohomologyZMod2 Y p) (b : cohomologyZMod2 Y q) :
    (cohPullback f N).hom (cup Y p q N h a b) =
      cup X p q N h ((cohPullback f p).hom a) ((cohPullback f q).hom b) := by
  subst N
  exact Cup.naturality f p q a b

theorem diagonal_triple_reduction (X : TopCat.{0}) (n m N : ℕ) (hN : n + (m + n) = N)
    (a b : cohomologyZMod2 X n) (c : cohomologyZMod2 X m) (ha : cupZMod2 a a = 0) :
    cup X n (m + n) N hN (a + b) (cup X m n (m + n) rfl c a) =
      cup X (n + n) m N (by omega) (cup X n n (n + n) rfl a b) c := by
  rw [comm X m n (m + n) rfl c a]
  rw [← assoc X n n m (n + n) (m + n) N rfl (by omega) (by omega) hN (a + b) a c]
  rw [add_left]
  have hz : cup X n n (n + n) rfl a a = 0 := ha
  rw [hz, zero_add, comm X n n (n + n) rfl b a]

theorem diagonal_triple_reduction_at (X : TopCat.{0}) (n m u N : ℕ)
    (hu : n + n = u) (hN : n + (m + n) = N)
    (a b : cohomologyZMod2 X n) (c : cohomologyZMod2 X m) (ha : cupZMod2 a a = 0) :
    cup X n (m + n) N hN (a + b) (cup X m n (m + n) rfl c a) =
      cup X u m N (by omega) (cup X n n u hu a b) c := by
  subst u
  exact diagonal_triple_reduction X n m N hN a b c ha

end
end Finsler.CupAtDegree
