import Mathlib.Tactic

set_option autoImplicit false

def V : Array ℕ := [1, 2, 3].toArray
#eval Array.foldl (fun a b => (a + b)) 0 V 1 2

structure SegmentTree (α : Type*) [Monoid α] (n : ℕ) where
  n := n
  m := n -- temporary
  -- TODO maybe store original vector
  a : Vector α (2*m)

  -- assumptions
  h_n_pow2 : ∃ k, m = 2^k -- temporary
  h_children (j : ℕ) (h0j : 0 < j) (hjm: j < m) :
    (a.get ⟨j, by omega⟩) = (a.get ⟨2*j, by omega⟩) * (a.get ⟨2*j+1, by omega⟩)

-- helper lemma
lemma foldl_single {α : Type*} (a : List α) (op : α → α → α) (init : α) (h : a.length = 1) :
    a.foldl op init = op init (a[0]) := by
  cases a with
  | nil => trivial
  | cons x xs =>
    simp
    cases xs with
    | nil => simp
    | cons y ts => simp_all

-- helper lemma
lemma foldl_single2 {α : Type*} (a : Array α) (op : α → α → α) (init : α) (h : a.size = 1) :
    a.foldl op init = op init (a[0]) := by
  have h_list := foldl_single a.toList op init (by simp_all)
  rw [Array.foldl_toList op] at h_list
  assumption

def monoid_foldl (α : Type*) [Monoid α] (n : ℕ) (as : Vector α n) (l r : ℕ) : α :=
  if h_start : l < as.size then
    if l < r then
      as.get ⟨l, h_start⟩ * monoid_foldl α n as (l+1) r
    else
      1
  else
    1

theorem monoid_foldl_single (α : Type*) [Monoid α] (n : ℕ) (as : Vector α n) (l r : ℕ)
    (h_l : l < as.size) (h_lr : l + 1 = r) :
    monoid_foldl α n as l r = as.get ⟨l, h_l⟩ := by
  unfold monoid_foldl
  split_ifs with h_start_stop_2
  · unfold monoid_foldl
    split_ifs
    · omega
    · apply MulOneClass.mul_one
    · apply MulOneClass.mul_one
  · omega

theorem monoid_foldl_combine (α : Type*) [Monoid α] (n : ℕ) (as : Vector α n)
    (l c r : ℕ) (h_lc : l ≤ c) (h_cr : c ≤ r) (h_bounds : r < as.size) :
    (monoid_foldl α n as l c) * (monoid_foldl α n as c r) = monoid_foldl α n as l r := by
  if h_lc0 : l = c then {
    rw [monoid_foldl.eq_def α n as l c]
    split_ifs with h_lbounds h_lgeqc <;> try omega
    rw [← h_lc0]
    apply one_mul
  } else {
    rw [monoid_foldl.eq_def α n as l c]
    split_ifs with h_lbounds h_lgeqc <;> try omega
    rw [mul_assoc (as.get ⟨l, h_lbounds⟩) (monoid_foldl α n as (l + 1) c) (monoid_foldl α n as c r)]
    rw [monoid_foldl_combine] <;> try omega
    rw [monoid_foldl.eq_def α n as l r]
    split_ifs <;> try omega
    rfl
  }

lemma SegmentTree.h_coverage_interval (α : Type*) [Monoid α] (n j : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
      let l := Nat.log2 j
      let k := j - 2^l
      let H := st.h_n_pow2.choose
      let h := H - l
      let L := 2^h * k
      let R := L + 2^h
      st.a.get ⟨j, hj2m⟩ = monoid_foldl α (2*st.m) st.a (st.m+L) (st.m+R)
    := by
  set l := Nat.log2 j with h_l
  set k := j - 2^l with h_k
  set H := st.h_n_pow2.choose with h_H
  set h := H - l with h_h
  set L := 2^h * k with h_L
  set R := L + 2^h with h_R
  have H_spec := st.h_n_pow2.choose_spec
  simp only []

  by_cases hjm : st.m ≤ j
  · have exp0 : H ≤ l := by -- in this case a[j] is a leaf of the tree
      subst l
      rw [H_spec] at hjm
      subst H
      rw [Nat.le_log2 ?_]
      · assumption
      · omega
    have h_LeqR : L = R-1 := by
      subst R
      subst h
      rw [Nat.sub_eq_zero_of_le exp0]
      simp
    have h_leqm : st.m = 2^l := by
      subst l
      rw [Nat.le_antisymm_iff]
      constructor
      · rw [H_spec]
        exact Nat.pow_le_pow_right (n:=2) (by omega) (i:=st.h_n_pow2.choose) (j:=j.log2) exp0
      · rw [H_spec]
        rw [Nat.pow_le_pow_iff_right (by omega)]
        rw [Nat.le_iff_lt_add_one]
        rw [Nat.log2_lt]
        rw [Nat.pow_add_one 2 st.h_n_pow2.choose]
        rw [← H_spec]
        rw [Nat.mul_comm st.m 2]
        assumption
        omega

    rw [← h_h, ← h_k, ← h_L, h_LeqR]
    -- https://leanprover-community.github.io/archive/stream/270676-lean4/topic/(kernel).20declaration.20has.20metavariables.html
    rw [monoid_foldl_single (h_l:=?_)] -- without (h:=?_) it says "don't know how to synthesize placeholder"
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
    · subst h
      rw [Nat.sub_eq_zero_of_le exp0]
      omega
    · rw [show st.a.size = 2 * st.m from rfl]
      subst R
      subst L
      subst h
      rw [Nat.sub_eq_zero_of_le exp0]
      omega

  · rw [st.h_children j h0j (by omega)]   -- in this case a[j] is an internal node of the tree
    rw [st.h_coverage_interval (h0j:=by omega)]
    rw [st.h_coverage_interval (h0j:=by omega)]

    have expNot0 : l < H := by -- in this case a[j] is a leaf of the tree
      subst l
      simp at hjm
      rw [H_spec] at hjm
      subst H
      rw [← Nat.log2_lt (by omega)] at hjm
      omega

    set aL := st.m + L with h_aL
    -- (L+R)/2 = (2^h * k + 2^h * k + 2^h)/2 = 2^(h-1) * (2k+1)
    set aC := st.m + 2^(h-1)*(2*k+1) with h_aC
    set aR := st.m + R with h_aR

    rw [show (st.m + 2 ^ (st.h_n_pow2.choose - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2)) = aL by {
      rw [h_aL]
      subst L
      subst k
      subst l
      subst h
      subst H
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_mul_base (by omega) (by omega)]
      rw [Nat.sub_add_eq st.h_n_pow2.choose (Nat.log 2 j) 1]
      nth_rw 3 [← Nat.pow_pred_mul (by rw [← Nat.log2_eq_log_two]; omega)]
      rw [Nat.mul_assoc (2 ^ (st.h_n_pow2.choose - Nat.log 2 j - 1)) 2 (j - 2 ^ Nat.log 2 j)]
      rw [Nat.mul_right_inj (by simp)]
      omega
    }]
    rw [show (st.m + (2 ^ (st.h_n_pow2.choose - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2) + 2 ^ (st.h_n_pow2.choose - (2 * j).log2))) = aC by {
      rw [h_aC]
      subst L
      subst k
      subst l
      subst h
      subst H
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_mul_base (by omega) (by omega)]
      rw [Nat.sub_add_eq st.h_n_pow2.choose (Nat.log 2 j) 1]
      rw [← Nat.mul_add_one]
      rw [Nat.mul_right_inj (by simp)]
      omega
    }]
    rw [show (st.m + 2 ^ (H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2)) = aC by {
      rw [h_aC]
      subst L
      subst k
      subst l
      subst h
      subst H
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      rw [Nat.succ_div_of_not_dvd (by omega)]
      simp
      rw [Nat.sub_add_eq st.h_n_pow2.choose (Nat.log 2 j) 1]
      rw [Nat.mul_right_inj (by simp)]
      rw [Nat.pow_add_one 2 (Nat.log 2 j)]
      rw [Nat.mul_sub 2 j (2 ^ Nat.log 2 j)]
      rw [tsub_add_eq_add_tsub (by simp; refine (Nat.le_log2 ?_).mp ?_; omega; rw [← Nat.log2_eq_log_two];)]
      omega
    }]
    rw [show (st.m + (2 ^ (H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2) + 2 ^ (H - (2 * j + 1).log2))) = aR by {
      rw [h_aR]
      subst R
      subst L
      subst k
      subst l
      subst h
      subst H
      simp
      rw [Nat.mul_comm 2 j]
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      rw [Nat.succ_div_of_not_dvd (by omega)]
      simp
      rw [←mul_add_one, ←mul_add_one]
      nth_rw 3 [← Nat.pow_pred_mul (by rw [← Nat.log2_eq_log_two]; omega)]
      rw [Nat.sub_add_eq st.h_n_pow2.choose (Nat.log 2 j) 1]
      rw [Nat.mul_assoc (2 ^ (st.h_n_pow2.choose - Nat.log 2 j - 1)) 2 (j - 2 ^ Nat.log 2 j + 1)]
      rw [Nat.mul_right_inj (by simp)]
      rw [Nat.pow_add_one 2 (Nat.log 2 j)]
      rw [Nat.mul_add_one 2 (j - 2 ^ Nat.log 2 j)]
      rw [Nat.mul_sub 2 j (2 ^ Nat.log 2 j)]
      rw [← Nat.sub_add_comm (by grw [show 2 ^ Nat.log 2 j * 2 ≤ 2 * j by {rw [Nat.mul_comm 2 j]; simp; refine (Nat.le_log2 ?_).mp ?_; omega; rw [← Nat.log2_eq_log_two];}]; omega)]
      rw [← Nat.sub_add_comm (by simp; refine (Nat.le_log2 ?_).mp ?_; omega; rw [← Nat.log2_eq_log_two];)]
      omega
    }]

    have a := monoid_foldl_combine α (2*st.m) st.a aL aC aR ?_ ?_ ?_
    · exact a
    · sorry
    · sorry
    · sorry


def build (α : Type*) [Monoid α] (n : ℕ) (h_n_pow2 : ∃ k, n = 2^k)
    (xs : Vector α n) : SegmentTree α n := by
  sorry
