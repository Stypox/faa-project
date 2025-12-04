/-
  Project 1 Template

  Complete the proofs below.
-/

import Mathlib.Tactic

def V : Array ℕ := [1, 2, 3].toArray
#eval Array.foldl (fun a b => (a + b)) 0 V 1 2

structure SegmentTree (α : Type u) [Monoid α] (n : ℕ) where
  n : ℕ := n
  m : ℕ := n
  H : ℕ
  -- TODO maybe store original vector
  a : Vector α (2*m)

  -- assumptions
  h_H : m = 2^H -- temporary
  h_children (j : ℕ) (h0j : 0 < j) (hjm: j < m) :
    (a.get ⟨j, by omega⟩) = (a.get ⟨2*j, by omega⟩) * (a.get ⟨2*j+1, by omega⟩)

theorem foldl_single (α : Type u) (a : List α) (op : α → α → α) (init : α) (h : a.length = 1) :
    a.foldl op init = op init (a[0]) := by
  cases a with
  | nil => trivial
  | cons x xs =>
    simp
    cases xs with
    | nil => simp
    | cons y ts => simp_all

theorem foldl_single2 (α : Type u) (a : Array α) (op : α → α → α) (init : α) (h : a.size = 1) :
    a.foldl op init = op init (a[0]) := by
  have h_list := foldl_single α a.toList op init (by simp_all)
  rw [Array.foldl_toList op] at h_list
  assumption

def my_foldl (α : Type u) [Monoid α] (n : ℕ) (as : Vector α n) (l r : ℕ) : α :=
  if h_start : l < as.size then
    if l < r then
      as.get ⟨l, h_start⟩ * my_foldl α n as (l+1) r
    else
      as.get ⟨l, h_start⟩
  else
    1

theorem foldl_single3 (α : Type u) [Monoid α] (n : ℕ) (as : Vector α n) (l r : ℕ)
    (h_l : l < as.size) (h_lr : l ≥ r) :
    my_foldl α n as l r = as.get ⟨l, h_l⟩ := by
  unfold my_foldl
  split_ifs with h_start_stop_2
  · omega
  · rfl

theorem foldl_combine (α : Type u) [Monoid α] (n : ℕ) (as : Vector α n)
    (l1 r1 l2 r2 : ℕ) :-- (h_next : r1 + 1 = l2) :
    (my_foldl α n as l1 r1) * (my_foldl α n as l2 r2) = my_foldl α n as l1 r2 := by
  sorry

lemma SegmentTree.h_coverage_interval (α : Type u) [Monoid α] (n : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
      let l := Nat.log2 j
      let k := j - 2^l
      let h := st.H - l
      let L := 2^h * k
      let R := L + 2^h - 1
      st.a.get ⟨j, hj2m⟩ = my_foldl α (2*st.m) st.a (st.m+L) (st.m+R)
    := by
  set l := Nat.log2 j with h_l
  set k := j - 2^l with h_k
  set h := st.H - l with h_h
  set L := 2^h * k with h_L
  set R := L + 2^h - 1 with h_R
  simp only []

  by_cases hjm : st.m ≤ j
  · have exp0 : st.H ≤ l := by
      subst l
      rw [h_H] at hjm
      rw [Nat.le_log2 ?_]
      · assumption
      · omega
    have h_LeqR : L = R := by
      subst R
      subst h
      rw [Nat.sub_eq_zero_of_le exp0]
      simp
    have h_leqm : st.m = 2^l := by
      subst l
      rw [Nat.le_antisymm_iff]
      constructor
      · rw [h_H] at hjm
        rw [← Nat.le_log2 ?_] at hjm
        rw [h_H]
        exact Nat.pow_le_pow_right (n:=2) (by omega) (i:=st.H) (j:=j.log2) hjm
        omega
      · rw [h_H]
        rw [Nat.pow_le_pow_iff_right (by omega)]
        rw [Nat.le_iff_lt_add_one]
        rw [Nat.log2_lt]
        rw [Nat.pow_add_one 2 st.H]
        rw [← h_H]
        rw [Nat.mul_comm st.m 2]
        assumption
        omega

    rw [← h_h, ← h_k, ← h_L, ← h_R, h_LeqR]
    set slice := (st.a.toArray.extract (st.m + R) (st.m + R + 1)) with h_slice
    rw [foldl_single3]
    · simp [Vector.get]
      subst R
      subst L
      subst h
      apply getElem_congr_idx
      rw [Nat.sub_eq_zero_of_le exp0]
      simp
      subst k
      rw [h_leqm]
      omega
    · omega

  · rw [st.h_children j h0j (by omega)]
    rw [st.h_coverage_interval]
    rw [st.h_coverage_interval]
    have a := foldl_combine α (2 * st.m) st.a
      (st.m + 2 ^ (st.H - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2))
      (st.m + (2 ^ (st.H - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2) + 2 ^ (st.H - (2 * j).log2) - 1))
      (st.m + 2 ^ (st.H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2))
      (st.m + (2 ^ (st.H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2) + 2 ^ (st.H - (2 * j + 1).log2) - 1))
      --(by sorry)



lemma SegmentTree.h_coverage_interval2 (α : Type u) [Monoid α] (n l k H h L R : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m)
    (h_l : l = Nat.log2 j) (h_k : k = j - 2^l) (h_H : st.m = 2^H)
    (h_h : h = H - l) (h_L : L = 2^h * k) (h_R : R = L + 2^h - 1) (hjm: st.m ≤ j)
    (i : Fin st.a.size)
    (h_i : i = Fin.mk (n:=st.a.size) j hj2m)
    (aa bb : α)
    (h_aa : aa = st.a.get i)
    (h_bb : bb = (st.a.toArray.extract (st.m+L) (st.m+R+1)).foldl (α:=α) (β:=α) (fun a b => a * b) 1)
    : aa = bb := by

  have exp0 : H ≤ l := by
    subst l
    rw [h_H] at hjm
    rw [Nat.le_log2 ?_]
    · assumption
    · omega
  have h_LeqR : L = R := by
    subst R
    subst h
    rw [Nat.sub_eq_zero_of_le exp0]
    simp
  have h_leqm : st.m = 2^l := by
    subst l
    rw [Nat.le_antisymm_iff]
    constructor
    · rw [h_H]
      exact Nat.pow_le_pow_right (n:=2) (by omega) (i:=H) (j:=j.log2) exp0
    · rw [h_H]
      rw [Nat.pow_le_pow_iff_right (by omega)]
      rw [Nat.le_iff_lt_add_one]
      rw [Nat.log2_lt]
      rw [Nat.pow_add_one 2 H]
      rw [← h_H]
      rw [Nat.mul_comm st.m 2]
      assumption
      omega

  set slice := (st.a.toArray.extract (st.m + R) (st.m + R + 1)) with h_slice
  rw [h_aa, h_bb]
  rw [foldl_single2]
  rw [Array.getElem_extract]
  simp [Vector.get]
  subst R
  subst L
  subst h
  apply getElem_congr_idx
  rw [Nat.sub_eq_zero_of_le exp0]
  simp
  subst k
  rw [h_i]
  simp
  rw [h_leqm]
  omega


def build (α : Type u) [Monoid α] (n : ℕ) (h_n_pow2 : ∃ k, n = 2^k)
    (xs : Vector α n) : SegmentTree α n := by
  sorry
