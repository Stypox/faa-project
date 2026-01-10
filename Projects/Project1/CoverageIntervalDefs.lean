import Mathlib.Tactic
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false


structure CoverageIntervalDefs (j H : ℕ) where
  h0j : 0 < j
  hj2m : j < 2*2^H
  l : ℕ
  k : ℕ
  h : ℕ
  L : ℕ
  R : ℕ
  h_l : l = Nat.log2 j
  h_k : k = j - 2^l
  h_h : h = H - l
  h_L : L = 2^h * k
  h_R : R = L + 2^h

def CoverageIntervalDefs.from_assumptions (j H : ℕ) (h0j : 0 < j) (hj2m: j < 2*2^H) :
  CoverageIntervalDefs j H := {
    h0j := h0j,
    hj2m := hj2m,
    l := Nat.log2 j,
    k := j - 2^(Nat.log2 j),
    h := H - Nat.log2 j,
    L := 2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)),
    R := 2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + 2^(H - Nat.log2 j),
    h_l := rfl,
    h_k := rfl,
    h_h := rfl,
    h_L := rfl,
    h_R := rfl
  }

def CoverageIntervalDefs.from_st {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n) (h0j : 0 < j) (hj2m: j < 2*st.m) :
  CoverageIntervalDefs j st.H := CoverageIntervalDefs.from_assumptions j st.H h0j (by simp [← st.h_m_pow2H, hj2m])

lemma CoverageIntervalDefs.j_neq_0 {j H : ℕ} (d : CoverageIntervalDefs j H) : j ≠ 0 := by
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

lemma CoverageIntervalDefs.leaf_pow2_h_eq_1 {j H : ℕ} (d : CoverageIntervalDefs j H) (h_leaf : 2^H ≤ j) : 2^d.h = 1 := by
  rw [d.h_h]
  rw [Nat.sub_eq_zero_of_le (by simp [d.leaf_l_eq_H h_leaf])]
  omega

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

lemma CoverageIntervalDefs.leaf_interval_L {j H : ℕ} (d : CoverageIntervalDefs j H) (h_leaf : 2^H ≤ j) :
  d.L = j-2^H
:= by
  rw [d.h_L]
  rw [d.leaf_pow2_h_eq_1 h_leaf]
  simp
  rw [d.h_k]
  rw [d.leaf_l_eq_H h_leaf]

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

-- helper lemma
lemma SegmentTree.h_coverage_interval {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n)
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
    rw [st.h_children j h0j (by simp [st.h_m_pow2H]; omega)]   -- in this case a[j] is an internal node of the tree
    rw [st.h_coverage_interval (h0j:=by omega)]
    rw [st.h_coverage_interval (h0j:=by omega)]
    simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]

    set aL := 2^st.H + d.L with h_aL
    set aC := 2^st.H + 2^(d.h-1)*(2*d.k+1) with h_aC  -- = (aL + aR)/2
    set aR := 2^st.H + d.R with h_aR

    rw [show (2^st.H + 2 ^ (st.H - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2)) = aL by {
      rw [h_aL, d.h_L, d.h_k, d.h_h, d.h_l]
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_mul_base (by omega) (by omega)]
      rw [Nat.sub_add_eq st.H (Nat.log 2 j) 1]
      nth_rw 3 [← Nat.pow_pred_mul (by exact d.internal_l_lt_H'' h_leaf)]
      rw [Nat.mul_assoc (2 ^ (st.H - Nat.log 2 j - 1)) 2 (j - 2 ^ Nat.log 2 j)]
      rw [Nat.mul_right_inj (by simp)]
      omega
    }]
    rw [show (2^st.H + (2 ^ (st.H - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2) + 2 ^ (st.H - (2 * j).log2))) = aC by {
      rw [h_aC, d.h_k, d.h_h, d.h_l]
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_mul_base (by omega) (by omega)]
      rw [Nat.sub_add_eq st.H (Nat.log 2 j) 1]
      rw [← Nat.mul_add_one]
      rw [Nat.mul_right_inj (by simp)]
      omega
    }]
    rw [show (2^st.H + 2 ^ (st.H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2)) = aC by {
      rw [h_aC, d.h_k, d.h_h, d.h_l]
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      rw [Nat.succ_div_of_not_dvd (by omega)]
      simp
      rw [Nat.sub_add_eq st.H (Nat.log 2 j) 1]
      rw [Nat.mul_right_inj (by simp)]
      rw [Nat.pow_add_one 2 (Nat.log 2 j)]
      rw [Nat.mul_sub 2 j (2 ^ Nat.log 2 j)]
      rw [tsub_add_eq_add_tsub (by simp; refine (Nat.le_log2 ?_).mp ?_; omega; rw [← Nat.log2_eq_log_two];)]
      omega
    }]
    rw [show (2^st.H + (2 ^ (st.H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2) + 2 ^ (st.H - (2 * j + 1).log2))) = aR by {
      rw [h_aR, d.h_R, d.h_L, d.h_k, d.h_h, d.h_l]
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      rw [Nat.succ_div_of_not_dvd (by omega)]
      simp
      rw [←mul_add_one, ←mul_add_one]
      nth_rw 3 [← Nat.pow_pred_mul (by exact d.internal_l_lt_H'' h_leaf)]
      rw [Nat.sub_add_eq st.H (Nat.log 2 j) 1]
      rw [Nat.mul_assoc (2 ^ (st.H - Nat.log 2 j - 1)) 2 (j - 2 ^ Nat.log 2 j + 1)]
      rw [Nat.mul_right_inj (by simp)]
      rw [Nat.pow_add_one 2 (Nat.log 2 j)]
      rw [Nat.mul_add_one 2 (j - 2 ^ Nat.log 2 j)]
      rw [Nat.mul_sub 2 j (2 ^ Nat.log 2 j)]
      rw [← Nat.sub_add_comm (by grw [show 2 ^ Nat.log 2 j * 2 ≤ 2 * j by {rw [Nat.mul_comm 2 j]; simp; refine (Nat.le_log2 ?_).mp ?_; omega; rw [← Nat.log2_eq_log_two];}]; omega)]
      rw [← Nat.sub_add_comm (by simp; refine (Nat.le_log2 ?_).mp ?_; omega; rw [← Nat.log2_eq_log_two];)]
      omega
    }]

    apply foldl_combine α (2*st.m) aL aC aR st.a ⟨?_, ?_⟩
    · -- aL <= aC
      rw [h_aL, h_aC, d.h_L, d.h_k, d.h_h, d.h_l]
      simp
      nth_rw 1 [← Nat.pow_pred_mul (by exact d.internal_l_lt_H' h_leaf)]
      rw [Nat.mul_assoc (2 ^ (st.H - j.log2 - 1)) 2 (j - 2 ^ j.log2)]
      rw [Nat.mul_le_mul_left_iff (by simp)]
      omega
    · -- aC <= aR
      rw [h_aC, h_aR, d.h_R, d.h_L, d.h_k, d.h_h, d.h_l]
      simp
      rw [← Nat.mul_add_one (2 ^ (st.H - j.log2)) (j - 2 ^ j.log2)]
      nth_rw 3 [← Nat.pow_pred_mul (by exact d.internal_l_lt_H' h_leaf)]
      rw [Nat.mul_assoc (2 ^ (st.H - j.log2 - 1)) 2 (j - 2 ^ j.log2 + 1)]
      rw [Nat.mul_le_mul_left_iff (by simp)]
      omega

lemma SegmentTree.H_geq_log2j {α : Type*} [Monoid α] {n : ℕ} (st : SegmentTree α n)
  (j : ℕ) (h_j0 : j > 0) (h_j2m : j < 2 * st.m) :
  st.H + 1 ≥ Nat.log 2 j
:= by
  apply (Nat.pow_le_pow_iff_right (a:=2) (by omega)).mp
  rw [Nat.pow_add_one 2 st.H]
  rw [← st.h_m_pow2H]
  grw [Nat.pow_log_le_self 2 (x:=j) (by omega)]
  omega


lemma odd_log2' (i : ℕ) (h_pos: 1 ≤ i) : Nat.log 2 (2*i + 1) = Nat.log 2 (2*i) := by
  rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
  rw [Nat.succ_div_of_not_dvd (by omega)]
  rw [← Nat.log_of_one_lt_of_le (by omega) (by omega)]

lemma odd_log2 (i : ℕ) (h_pos: 1 ≤ i) : (2*i + 1).log2 = (2*i).log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact odd_log2' i h_pos

lemma log_sublinear (n : ℕ) : Nat.log 2 (n - 1) ≤ n := by
  if hn : n > 1 then {
    have a := Nat.log_lt_self 2 (x:=(n - 1)) (by omega)
    grw [a]
    simp
  } else {
    simp_all
  }




lemma succ_div_even_eq_div_even (a b: ℕ) :  (2 * a + 1) / (2 * b) = (2 * a) / (2 * b) := by
  rw [Nat.succ_div_of_not_dvd ?_]
  by_contra h_contra
  have h22b : 2 ∣ 2*b := by omega
  grw[← h22b] at h_contra
  rw [Nat.dvd_add_right (by omega)] at h_contra
  contradiction


lemma succ_div_even_eq_div_even_pow2 (j: ℕ) :  ∀ g > 0, (2 * j + 1) / 2 ^ g = (2 * j) / 2 ^ g := by
  intro g g0
  rw [← Nat.two_pow_pred_mul_two (by omega)]
  rw [Nat.mul_comm (2 ^ (g - 1)) 2]
  exact succ_div_even_eq_div_even j (2^(g-1))

  --rw [Nat.div_eq_iff (Nat.two_pow_pos g)]
  --constructor
  --· rw [Nat.div_mul_self_eq_mod_sub_self]
  --  trans (2*j)
  --  · grind
  --  · omega
  --· rw [Nat.div_mul_self_eq_mod_sub_self]
  --  rw [← Nat.sub_add_comm (by {grw[Nat.mod_le]})]
  --  rw [Nat.sub_sub (2 * j + 2 ^ g) (2 * j % 2 ^ g) 1]
  --  rw [Nat.add_sub_assoc (by omega) (2 * j)]
  --  simp
  --  rw [Nat.le_sub_iff_add_le (by omega)]
  --  rw [Nat.one_add_le_iff]
  --  by_contra h_contra
  --  simp at h_contra
  --  rw [Nat.le_add_one_iff] at h_contra
  --  cases h_contra <;> expose_names
  --  ·
  --    have h1 : 2 * j % 2 ^ g < 2^g := by omega
  --    grw[← h] at h1
  --    simp_all
  --  ·
  --    have h : (2 ^ g) % 2 = (2 * j % 2 ^ g + 1) % 2 := by omega
  --    --simp at h
  --    rw [Nat.pow_mod 2 g 2] at h
  --    rw [show 2 % 2 = 0 from rfl] at h
  --    rw [Nat.zero_pow (by omega)] at h
  --    rw [show 0 % 2 = 0 from rfl] at h
  --    rw [Nat.add_mod (2 * j % 2 ^ g) 1 2] at h
  --    rw [show 1 % 2 = 1 from rfl] at h
  --    rw [Nat.mod_mod_of_dvd (2 * j) (by omega)] at h
  --    rw [Nat.mul_mod_right 2 j] at h
  --    simp at h
