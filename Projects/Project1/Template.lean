/-
  Project 1 Template

  Complete the proofs below.
-/

import Mathlib.Tactic

def V : Array ℕ := [1, 2, 3].toArray
#eval Array.foldl (fun a b => (a + b)) 0 V 1 2

structure SegmentTree (α : Type u) [Monoid α] (n : ℕ) where
  n := n
  m := n
  -- TODO maybe store original vector
  a : Vector α (2*m)

  -- assumptions
  h_n_pow2 : ∃ k, m = 2^k -- temporary
  h_children (h0j : 0 < j) (hjm: j < m) :
    (a.get ⟨j, by omega⟩) = (a.get ⟨2*j, by omega⟩) * (a.get ⟨2*j+1, by omega⟩)

theorem foldl_single (a : List α) (op : α → α → α) (init : α) (h : a.length = 1) :
    a.foldl op init = op init (a[0]) := by
  cases a with
  | nil => trivial
  | cons x xs =>
    simp
    cases xs with
    | nil => simp
    | cons y ts => simp_all

theorem foldl_single2 (a : Array α) (op : α → α → α) (init : α) (h : a.size = 1) :
    a.foldl op init = op init (a[0]) := by
  have h_list := foldl_single a.toList op init (by simp_all)
  rw [Array.foldl_toList op] at h_list
  assumption

lemma SegmentTree.h_coverage_interval (α : Type u) [Monoid α] (n : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
      let l := Nat.log2 j
      let k := j - 2^l
      let H := st.h_n_pow2.choose
      let h := H - l
      let L := 2^h * k
      let R := L + 2^h - 1
      st.a.get ⟨j, by omega⟩ = (st.a.toArray.extract (st.m+L) (st.m+R+1)).foldl (fun a b => a * b) 1
    := by
  set l := Nat.log2 j with h_l
  set k := j - 2^l with h_k
  set H := st.h_n_pow2.choose with h_H
  set h := H - l with h_h
  set L := 2^h * k with h_L
  set R := L + 2^h - 1 with h_R
  have H_spec := st.h_n_pow2.choose_spec
  simp only []
  by_cases hjm : st.m ≤ j
  · have h_LeqR : L = R := by
      subst R
      subst h
      have exp0 : H ≤ l := by
        subst l
        rw [H_spec] at hjm
        subst H
        rw [Nat.le_log2 ?_]
        · assumption
        · omega
      rw [Nat.sub_eq_zero_of_le exp0]
      simp

    rw [← h_h, ← h_k, ← h_L, ← h_R, h_LeqR]
    set slice := (st.a.toArray.extract (st.m + R) (st.m + R + 1)) with h_slice
    rw [foldl_single2]
    · simp
      rw [Array.getElem_extract]
      simp




  · sorry



def build (α : Type u) [Monoid α] (n : ℕ) (h_n_pow2 : ∃ k, n = 2^k)
    (xs : Vector α n) : SegmentTree α n := by
  sorry
