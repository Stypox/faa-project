import Mathlib.Tactic
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers
import Projects.Project1.Helpers

set_option autoImplicit false


structure CoverageIntervalDefs (j H : ℕ) where
  h0j : 0 < j
  hj2m : j < 2*2^H
  l : ℕ
  k : ℕ
  h : ℕ
  L : ℕ
  R : ℕ
  C : ℕ
  h_l : l = Nat.log2 j
  h_k : k = j - 2^l
  h_h : h = H - l
  h_L : L = 2^h * k
  h_R : R = L + 2^h
  h_C : C = (L + R) / 2

def CoverageIntervalDefs.from_assumptions (j H : ℕ) (h0j : 0 < j) (hj2m: j < 2*2^H) :
  CoverageIntervalDefs j H := {
    h0j := h0j,
    hj2m := hj2m,
    l := Nat.log2 j,
    k := j - 2^(Nat.log2 j),
    h := H - Nat.log2 j,
    L := 2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)),
    R := 2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + 2^(H - Nat.log2 j),
    C := (2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + (2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + 2^(H - Nat.log2 j))) / 2
    h_l := rfl,
    h_k := rfl,
    h_h := rfl,
    h_L := rfl,
    h_R := rfl,
    h_C := rfl,
  }

def CoverageIntervalDefs.from_st {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n) (h0j : 0 < j) (hj2m: j < 2*st.m) :
  CoverageIntervalDefs j st.H := CoverageIntervalDefs.from_assumptions j st.H h0j (by simp [← st.h_m_pow2H, hj2m])

lemma CoverageIntervalDefs.j_neq_0 {j H : ℕ} (d : CoverageIntervalDefs j H) : j ≠ 0 := by
  have h0j := d.h0j
  omega

lemma CoverageIntervalDefs.j_geq_1 {j H : ℕ} (d : CoverageIntervalDefs j H) : j ≥ 1 := by
  have h0j := d.h0j
  omega

lemma CoverageIntervalDefs.L_lt_R {j H : ℕ} (d : CoverageIntervalDefs j H) : d.L < d.R := by
  rw [d.h_R]
  simp


-- riscriverei:

-- def CoverageIntervalDefs.isLeaf {j H : ℕ} (d : CoverageIntervalDefs j H) := 2^H ≤ j
-- def CoverageIntervalDefs.leaf_pow2_h_eq_1 {j H : ℕ} (d : CoverageIntervalDefs j H) := 2^d.h = 1
-- def CoverageIntervalDefs.leaf_interval_R {j H : ℕ} (d : CoverageIntervalDefs j H) := d.R = d.L+1
-- def CoverageIntervalDefs.leaf_interval_L {j H : ℕ} (d : CoverageIntervalDefs j H) := d.L = j-2^H

-- e poi:

-- lemma CoverageIntervalDefs.leaf_props {j H : ℕ} (d : CoverageIntervalDefs j H) :
--  (d.isLeaf ∨ d.leaf_pow2_h_eq_1 ∨ d.leaf_interval_R ∨ d.leaf_interval_L) ↔
--  (d.isLeaf ∧ d.leaf_pow2_h_eq_1 ∧ d.leaf_interval_R ∧ d.leaf_interval_L)
-- := by ...

-- cosi' da qualsiasi proprieta' di foglia si passa facilmente (credo) a qualsiasi altra.
-- E farei piu' o meno la stessa cosa per i nodi interni.


lemma CoverageIntervalDefs.leaf_l_eq_H {j H : ℕ} (d : CoverageIntervalDefs j H) (h_leaf : 2^H ≤ j) : d.l = H := by
  rw [d.h_l]
  rw [Nat.le_antisymm_iff]
  constructor
  · rw [Nat.le_iff_lt_add_one]
    rw [Nat.log2_lt]
    · rw [Nat.pow_add_one 2 H]
      rw [Nat.mul_comm (2^H) 2]
      exact d.hj2m
    · exact d.j_neq_0
  · rw [Nat.le_log2 ?_]
    · exact h_leaf
    · exact d.j_neq_0

lemma CoverageIntervalDefs.leaf_pow2_h_eq_1 {j H : ℕ} (d : CoverageIntervalDefs j H) (h_leaf : 2^H ≤ j) : 2^d.h = 1 := by
  rw [d.h_h]
  rw [Nat.sub_eq_zero_of_le (by simp [d.leaf_l_eq_H h_leaf])]
  omega

lemma CoverageIntervalDefs.leaf_interval_L {j H : ℕ} (d : CoverageIntervalDefs j H) (h_leaf : 2^H ≤ j) :
  d.L = j-2^H
:= by
  rw [d.h_L]
  rw [d.leaf_pow2_h_eq_1 h_leaf]
  simp
  rw [d.h_k]
  rw [d.leaf_l_eq_H h_leaf]

lemma CoverageIntervalDefs.leaf_interval_R {j H : ℕ} (d : CoverageIntervalDefs j H) : 2^H ≤ j ↔ d.R = d.L+1 := by
  constructor
  · intro h_leaf
    rw [d.h_R]
    rw [d.leaf_pow2_h_eq_1 h_leaf]
  · intro h_RL
    rw [d.h_R, d.h_L] at h_RL
    rw [Nat.add_right_inj] at h_RL
    rw [Nat.pow_eq_one] at h_RL
    rw [or_iff_right (by trivial)] at h_RL
    rw [d.h_h] at h_RL
    rw [Nat.sub_eq_zero_iff_le] at h_RL
    have h_RL : 2^H ≤ 2^d.l := by refine Nat.pow_le_pow_right (by omega) h_RL
    rw [d.h_l] at h_RL
    rw [Nat.log2_eq_log_two] at h_RL
    simp
    trans 2 ^ Nat.log 2 j
    · assumption
    · rw [← Nat.le_log_iff_pow_le (by omega) d.j_neq_0]

lemma CoverageIntervalDefs.not_in_leaf {j H : ℕ} (d : CoverageIntervalDefs j H)
  (p q : ℕ) (h_sub : ¬(p ≤ d.L ∧ d.R ≤ q)) (h_disjoint : ¬(q ≤ d.L ∨ d.R ≤ p)) : j < 2^H
:= by
  by_contra h_jm
  simp_all
  have h_RL := d.leaf_interval_R.mp (by assumption)
  rw [d.h_R, d.h_L, d.h_h, d.h_k] at h_RL
  rw [d.h_R, d.h_L, d.h_h, d.h_k] at h_sub
  rw [d.h_R, d.h_L, d.h_h, d.h_k] at h_disjoint
  rw[h_RL] at h_sub
  rw[h_RL] at h_disjoint
  obtain ⟨hd1, hd2⟩ := h_disjoint
  rw [Nat.lt_add_one_iff] at hd2
  apply h_sub at hd2
  rw [Nat.lt_add_one_iff] at hd2
  grw[hd2] at hd1
  rw [lt_self_iff_false] at hd1
  exact hd1

lemma CoverageIntervalDefs.internal_l_lt_H {j H : ℕ} (d : CoverageIntervalDefs j H) (h_internal : 2^H > j) : d.l < H := by
  rw [d.h_l]
  simp at h_internal
  rw [← Nat.log2_lt (by exact d.j_neq_0)] at h_internal
  omega
lemma CoverageIntervalDefs.internal_l_lt_H' {j H : ℕ} (d : CoverageIntervalDefs j H) (h_internal : 2^H > j) : 0 < H - j.log2 := by
  simp [← d.h_l, d.internal_l_lt_H h_internal]
lemma CoverageIntervalDefs.internal_l_lt_H'' {j H : ℕ} (d : CoverageIntervalDefs j H) (h_internal : 2^H > j) : 0 < H - (Nat.log 2 j) := by
  simp [← Nat.log2_eq_log_two, d.internal_l_lt_H' h_internal]

lemma CoverageIntervalDefs.internal_0_lt_h {j H : ℕ} (d : CoverageIntervalDefs j H) (h_internal : 2^H > j) : 0 < d.h := by
  rw [d.h_h]
  rw [Nat.sub_pos_iff_lt]
  exact d.internal_l_lt_H h_internal

lemma CoverageIntervalDefs.internal_L_lt_C_lt_R {j H : ℕ} (d : CoverageIntervalDefs j H) (h_internal : 2^H > j) :
  d.L < d.C ∧ d.C < d.R
:= by
  rw [d.h_C, d.h_R]
  suffices (2^d.h ≥ 2) by omega
  rw [show (2 ^ d.h ≥ 2) = (2 ≤ 2 ^ d.h) from rfl]
  rw [← Nat.clog_le_iff_le_pow (by omega)]
  rw [Nat.clog_eq_one (by omega) (by omega)]
  exact d.internal_0_lt_h h_internal

lemma CoverageIntervalDefs.C_eq_L_plus_half {j H : ℕ} (d : CoverageIntervalDefs j H) (h_internal : 2^H > j) : d.C = d.L + 2 ^ (d.h - 1) := by
  rw [d.h_C, d.h_R]
  rw [← Nat.add_assoc d.L d.L (2 ^ d.h)]
  rw [← Nat.mul_two d.L]
  rw [← Nat.pow_pred_mul (d.internal_0_lt_h h_internal)]
  rw [← Nat.add_mul d.L (2 ^ (d.h - 1)) 2]
  rw [Nat.mul_div_left (d.L + 2 ^ (d.h - 1)) (by omega)]

lemma CoverageIntervalDefs.Lj_eq_L2j {j H : ℕ} (d : CoverageIntervalDefs j H)
  (dLeft : CoverageIntervalDefs (2*j) H) (h_internal : 2^H > j) :
  d.L = dLeft.L
:= by
  rw [d.h_L, dLeft.h_L, d.h_k, dLeft.h_k, d.h_h, dLeft.h_h, d.h_l, dLeft.h_l]
  rw [Nat.mul_comm 2 j]
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  rw [Nat.log_mul_base (by omega) d.j_neq_0]
  rw [Nat.sub_add_eq H (Nat.log 2 j) 1]
  nth_rw 1 [← Nat.pow_pred_mul (by exact d.internal_l_lt_H'' h_internal)]
  rw [Nat.mul_assoc (2 ^ (H - Nat.log 2 j - 1)) 2 (j - 2 ^ Nat.log 2 j)]
  rw [Nat.mul_right_inj (by simp)]
  omega

lemma CoverageIntervalDefs.Cj_eq_R2j {j H : ℕ} (d : CoverageIntervalDefs j H)
  (dLeft : CoverageIntervalDefs (2*j) H) (h_internal : 2^H > j) :
  d.C = dLeft.R
:= by
  rw [d.C_eq_L_plus_half h_internal, dLeft.h_R, d.Lj_eq_L2j dLeft h_internal, d.h_h, dLeft.h_h, d.h_l, dLeft.h_l]
  rw [Nat.add_right_inj]
  rw [Nat.log2_two_mul d.j_neq_0]
  grind

lemma CoverageIntervalDefs.Rj_eq_R2jp1 {j H : ℕ} (d : CoverageIntervalDefs j H)
  (dRight : CoverageIntervalDefs (2*j+1) H) (h_internal : 2^H > j) :
  d.R = dRight.R
:= by
  rw [d.h_R, dRight.h_R, d.h_L, dRight.h_L, d.h_k, dRight.h_k, d.h_h, dRight.h_h, d.h_l, dRight.h_l]
  rw [Nat.mul_comm 2 j]
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  rw [Nat.log_of_one_lt_of_le (n:=j*2+1) (by omega) (by have := d.j_neq_0; omega)]
  rw [Nat.succ_div_of_not_dvd (by omega)]
  simp
  rw [←mul_add_one, ←mul_add_one]
  nth_rw 1 [← Nat.pow_pred_mul (by exact d.internal_l_lt_H'' h_internal)]
  rw [Nat.sub_add_eq H (Nat.log 2 j) 1]
  rw [Nat.mul_assoc (2 ^ (H - Nat.log 2 j - 1)) 2 (j - 2 ^ Nat.log 2 j + 1)]
  rw [Nat.mul_right_inj (by simp)]
  rw [Nat.pow_add_one 2 (Nat.log 2 j)]
  rw [Nat.mul_add_one 2 (j - 2 ^ Nat.log 2 j)]
  rw [Nat.mul_sub 2 j (2 ^ Nat.log 2 j)]
  have : 2 ^ Nat.log 2 j ≤ j := (Nat.le_log2 d.j_neq_0).mp (by rw [← Nat.log2_eq_log_two])
  rw [← Nat.sub_add_comm (by omega)]
  rw [← Nat.sub_add_comm (by omega)]
  omega

lemma CoverageIntervalDefs.Cj_eq_L2jp1 {j H : ℕ} (d : CoverageIntervalDefs j H)
  (dRight : CoverageIntervalDefs (2*j+1) H) (h_internal : 2^H > j) :
  d.C = dRight.L
:= by
  have Rj_eq_R2jp1 := Nat.eq_sub_of_add_eq (d.h_R.symm.trans (d.Rj_eq_R2jp1 dRight h_internal))
  rw [d.C_eq_L_plus_half h_internal, Rj_eq_R2jp1, dRight.h_R, dRight.h_L, dRight.h_k, d.h_h, dRight.h_h, d.h_l, dRight.h_l]
  rw [odd_log2 j d.j_geq_1]
  rw [Nat.log2_two_mul d.j_neq_0]
  rw [← Nat.mul_add_one]
  rw [← Nat.pow_pred_mul (d.internal_l_lt_H' h_internal)]
  rw [Nat.sub_add_eq H j.log2 1]
  rw [← mul_tsub (2 ^ (H - j.log2 - 1)) (2 * j + 1 - 2 ^ (j.log2 + 1) + 1) 2]
  rw [← Nat.mul_add_one (2 ^ (H - j.log2 - 1)) (2 * j + 1 - 2 ^ (j.log2 + 1) + 1 - 2)]
  suffices 2*j ≥ 2^(j.log2 + 1) by rw [← Nat.sub_add_comm (by omega)]; simp
  simp [Nat.pow_add_one']
  rw [← Nat.le_log2 d.j_neq_0]

lemma CoverageIntervalDefs.R2j_eq_L2jp1 {j H : ℕ} (dLeft : CoverageIntervalDefs (2*j) H)
  (dRight : CoverageIntervalDefs (2*j+1) H) (h_internal : 2^H > j) :
  dLeft.R = dRight.L
:= by
  let d := CoverageIntervalDefs.from_assumptions j H (have := dLeft.h0j; by omega) (by omega)
  rw [← d.Cj_eq_R2j dLeft h_internal, ← d.Cj_eq_L2jp1 dRight h_internal]


-- helper lemma
lemma SegmentTree.coverage_interval {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
  let d := CoverageIntervalDefs.from_st n j st h0j hj2m
  st.a.get ⟨j, hj2m⟩ = (st.a.toArray.extract (st.m+d.L) (st.m+d.R)).foldl (fun a b => a * b) 1
:= by
  set d := CoverageIntervalDefs.from_st n j st h0j hj2m
  simp only [st.h_m_pow2H]

  by_cases h_leaf : 2^st.H ≤ j
  · -- in this case a[j] is a leaf of the tree
    rw [d.leaf_interval_R.mp h_leaf, d.leaf_interval_L h_leaf]

    rw [foldl_single_array (h:=?_)] -- without (h:=?_) it says "don't know how to synthesize placeholder"
    · rw [Array.getElem_extract]
      simp [Vector.get]
      apply getElem_congr_idx
      rw [Nat.add_sub_of_le h_leaf]
    · simp
      rw [Nat.min_eq_left ?_]
      · omega
      · omega

  · simp at h_leaf
    have h_leaf' : j < st.m := by simpa [st.h_m_pow2H]
    rw [st.h_children j h0j h_leaf']   -- in this case a[j] is an internal node of the tree
    rw [st.coverage_interval (h0j := by omega)]
    rw [st.coverage_interval (h0j := by omega)]

    set dLeft := CoverageIntervalDefs.from_st n (2 * j) st (by omega) (by omega) with h_dL
    set dRight := CoverageIntervalDefs.from_st n (2 * j + 1) st (by omega) (by omega) with h_dR
    rw [← st.h_m_pow2H, ← d.Lj_eq_L2j dLeft h_leaf, ← d.Cj_eq_R2j dLeft h_leaf,
      ← d.Cj_eq_L2jp1 dRight h_leaf, ← d.Rj_eq_R2jp1 dRight h_leaf]

    have h_Cmid : d.L < d.C ∧ d.C < d.R := d.internal_L_lt_C_lt_R h_leaf
    exact foldl_combine α (2*st.m) (st.m + d.L) (st.m + d.C) (st.m + d.R) st.a ⟨by omega, by omega⟩

lemma SegmentTree.H_geq_log2j {α : Type*} [Monoid α] {n : ℕ} (st : SegmentTree α n)
  (j : ℕ) (h_j0 : j > 0) (h_j2m : j < 2 * st.m) :
  st.H + 1 ≥ Nat.log 2 j
:= by
  apply (Nat.pow_le_pow_iff_right (a:=2) (by omega)).mp
  rw [Nat.pow_add_one 2 st.H]
  rw [← st.h_m_pow2H]
  grw [Nat.pow_log_le_self 2 (x:=j) (by omega)]
  omega
