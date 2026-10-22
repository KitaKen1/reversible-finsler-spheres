module

public import Finsler.Topology.PrismShuffle
public import Mathlib.Data.List.Count

/-! Finite Boolean words for the actual recursive shuffle. False is a
horizontal step, true a vertical step. This avoids dependent path casts
when taking the initial cap block and the remaining shuffle tail. -/

@[expose] public section
namespace Finsler.ShuffleWords

open CategoryTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

def horizontal : List Bool → ℕ
  | [] => 0
  | false :: w => horizontal w + 1
  | true :: w => horizontal w

def vertical : List Bool → ℕ
  | [] => 0
  | false :: w => vertical w
  | true :: w => vertical w + 1

theorem counts_length (w : List Bool) : horizontal w + vertical w = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [horizontal, vertical, List.length_cons] <;> omega

theorem horizontal_append (u v : List Bool) : horizontal (u ++ v) = horizontal u + horizontal v := by
  induction u with
  | nil => simp [horizontal]
  | cons b u ih => cases b <;> simp [horizontal, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem vertical_append (u v : List Bool) : vertical (u ++ v) = vertical u + vertical v := by
  induction u with
  | nil => simp [vertical]
  | cons b u ih => cases b <;> simp [vertical, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem horizontal_take_mono (w : List Bool) {i j : ℕ} (hij : i ≤ j) :
    horizontal (w.take i) ≤ horizontal (w.take j) := by
  induction w generalizing i j with
  | nil => simp [horizontal]
  | cons b w ih =>
    cases i with
    | zero => simp [horizontal]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have h := ih (show i ≤ j by omega)
        cases b <;> simp only [List.take_succ_cons, horizontal] <;> omega

theorem vertical_take_mono (w : List Bool) {i j : ℕ} (hij : i ≤ j) :
    vertical (w.take i) ≤ vertical (w.take j) := by
  induction w generalizing i j with
  | nil => simp [vertical]
  | cons b w ih =>
    cases i with
    | zero => simp [vertical]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have h := ih (show i ≤ j by omega)
        cases b <;> simp only [List.take_succ_cons, vertical] <;> omega

theorem horizontal_take_le (w : List Bool) (i : ℕ) : horizontal (w.take i) ≤ horizontal w := by
  have h := horizontal_append (w.take i) (w.drop i)
  rw [List.take_append_drop] at h
  omega

theorem vertical_take_le (w : List Bool) (i : ℕ) : vertical (w.take i) ≤ vertical w := by
  have h := vertical_append (w.take i) (w.drop i)
  rw [List.take_append_drop] at h
  omega

def words : ℕ → ℕ → Finset (List Bool)
  | 0, 0 => {[]}
  | p + 1, 0 => (words p 0).image (List.cons false)
  | 0, q + 1 => (words 0 q).image (List.cons true)
  | p + 1, q + 1 => (words p (q + 1)).image (List.cons false) ∪
      (words (p + 1) q).image (List.cons true)

theorem mem_words (p q : ℕ) (w : List Bool) :
    w ∈ words p q ↔ horizontal w = p ∧ vertical w = q := by
  induction p generalizing q w with
  | zero =>
    induction q generalizing w with
    | zero =>
      cases w with
      | nil => simp [words, horizontal, vertical]
      | cons b w => cases b <;> simp [words, horizontal, vertical]
    | succ q ih =>
      cases w with
      | nil => simp [words, horizontal, vertical]
      | cons b w => cases b <;> simp [words, Finset.mem_image, ih, horizontal, vertical]
  | succ p ih =>
    induction q generalizing w with
    | zero =>
      cases w with
      | nil => simp [words, horizontal, vertical]
      | cons b w => cases b <;> simp [words, Finset.mem_image, ih, horizontal, vertical]
    | succ q ihq =>
      cases w with
      | nil => simp [words, horizontal, vertical]
      | cons b w => cases b <;> simp [words, Finset.mem_image, ih, ihq, horizontal, vertical]

theorem word_length {p q : ℕ} {w : List Bool} (hw : w ∈ words p q) : w.length = p + q := by
  obtain ⟨hp, hq⟩ := (mem_words p q w).mp hw
  rw [← counts_length, hp, hq]

private theorem image_disjoint (s t : Finset (List Bool)) :
    Disjoint (s.image (List.cons false)) (t.image (List.cons true)) := by
  apply Finset.disjoint_left.mpr
  intro w hw ht
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ht
  cases hv

theorem sum_succ_zero {M : Type*} [AddCommMonoid M] (p : ℕ) (f : List Bool → M) :
    ∑ w ∈ words (p + 1) 0, f w = ∑ w ∈ words p 0, f (false :: w) := by
  rw [words, Finset.sum_image]
  intro a _ b _ h
  exact List.cons.inj h |>.2

theorem sum_zero_succ {M : Type*} [AddCommMonoid M] (q : ℕ) (f : List Bool → M) :
    ∑ w ∈ words 0 (q + 1), f w = ∑ w ∈ words 0 q, f (true :: w) := by
  rw [words, Finset.sum_image]
  intro a _ b _ h
  exact List.cons.inj h |>.2

theorem sum_succ_succ {M : Type*} [AddCommMonoid M] (p q : ℕ) (f : List Bool → M) :
    ∑ w ∈ words (p + 1) (q + 1), f w =
      (∑ w ∈ words p (q + 1), f (false :: w)) +
      ∑ w ∈ words (p + 1) q, f (true :: w) := by
  rw [words, Finset.sum_union (image_disjoint _ _), Finset.sum_image, Finset.sum_image]
  all_goals
    intro a _ b _ h
    exact List.cons.inj h |>.2

end Finsler.ShuffleWords
