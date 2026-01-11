import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.CoverageIntervalDefs
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false


def update_helper {α : Type} [inst : Monoid α] (n : ℕ) (st : SegmentTree α n) (x : α) (p j L R : ℕ)
  (h_j0 : j > 0) (b : Vector α (2 * st.m)) : TimeM (Vector α (2 * st.m)) := do
  if h_j : j < 2*st.m then
    if h_sub : p = L ∧ p+1 = R then   -- if we got to this case, j is a leaf
      ✓ (b.set j x h_j)
    else if h_empty : p < L ∨ p ≥ R then
      ✓ b
    else if h_int : 2*j+1 < 2*st.m then
      let C := (L+R)/2
      let b ← update_helper n st x p (2*j) L C (by omega) b
      let b ← update_helper n st x p (2*j + 1) C R (by omega) b
      ✓ (b.set j (b.get ⟨2*j, (by omega)⟩ * b.get ⟨2*j +1, (by omega)⟩ ) (by omega))
    else ✓ b
  else ✓ b

def st_prop_except_ancestors {α : Type} [inst: Monoid α] (m j : ℕ) (a: Vector α (2*m)) : Prop :=
  ∀ (i : ℕ) (h_i0 : i > 0) (h_i_neq_j2 : ∀ g > 0, i ≠ j/(2^g)) (h_i_ub : i < m),
    a.get ⟨i, by omega⟩ = a.get ⟨2*i, by omega⟩ * a.get ⟨2*i+1, by omega⟩


lemma update_helper_correctness (α : Type) (inst: Monoid α) (n j x y : ℕ) (val : α) (pos : ℕ) (st : SegmentTree α n)
    (h_j0 : j > 0) (h_j : j < 2*st.m) (hposm: pos < st.m) (b1 : Vector α (2*st.m)) :
  let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
  let b2 := (update_helper n st val pos j x y h_j0 b1).ret
  (d.L = x ∧ d.R = y ∧ st_prop_except_ancestors st.m j b1) →
    st_prop_except_ancestors st.m j b2 ∧ ((x ≤ pos ∧ pos < y) → b2.get ⟨pos + st.m, by omega⟩ = val)
  := by

  set d := CoverageIntervalDefs.from_st n j st h_j0 h_j with h_d
  -- set b2 := (update_helper n st val pos j x y h_j0 b1).ret with h_b2
  -- rw [h_b2]
  simp
  intro h_x h_y
  rw [← h_x, ← h_y]
  intro h_input

  unfold update_helper
  --have H_spec := st.h_m_pow2H
  --have H_spec2: st.H = st.m.log2 := by
  --  rw[H_spec]
  --  rw [Nat.log2_two_pow]
  simp only [TimeM.tick] -- get rid of time measurement

  split_ifs with h_sub h_disjoint h_int <;> simp
  · have h_leaf : st.m ≤ j := by
        obtain ⟨h_pL, h_pR⟩ := h_sub
        rw [h_pL] at h_pR
        rw [st.h_m_pow2H]
        exact d.leaf_interval_R.mpr (by omega)

    unfold st_prop_except_ancestors
    simp [Vector.set, Vector.get, Array.set, List.getElem_set]

    constructor
    · intro i h_i0 h_i_neq_j2 h_i_ub
      split_ifs with h1 h2 h3 h3 <;> try omega
      · specialize h_i_neq_j2 1 (by omega)
        omega
      · specialize h_i_neq_j2 1 (by omega)
        omega
      · exact h_input i h_i0 h_i_neq_j2 h_i_ub

    · have h_tmp : pos + st.m = j := by
        rw[h_sub.left, CoverageIntervalDefs.leaf_interval_L d (by {rw[← st.h_m_pow2H]; exact h_leaf}), ← st.h_m_pow2H]
        rw [tsub_add_cancel_of_le h_leaf]
      intro h_Lpos h_posR hhh
      rw[h_tmp] at hhh
      contradiction

  · constructor
    · assumption
    · grind

  all_goals have h_internal : j < 2^st.H := d.not_in_leaf pos (pos+1) (by grind) (by grind)
  all_goals simp at h_disjoint
  all_goals have h2j12m : 2*j + 1 < 2*st.m := by {
    rw [Nat.lt_iff_add_one_le] at h_internal; rw [Nat.lt_iff_add_one_le]
    rw[← st.h_m_pow2H] at h_internal;
    ring_nf; nth_rw 1 [← one_add_one_eq_two]; rw [← Nat.mul_two 1]
    rw [← Nat.add_mul 1 j 2]; rw [Nat.add_comm 1 j]
    gcongr
  }
  all_goals have h2j2m : 2*j < 2*st.m := by omega

  · --have h_internal : j < 2^st.H := d.not_in_leaf pos (pos+1) (by grind) (by grind)
    --simp at h_disjoint
--
    --have h2j12m : 2*j + 1 < 2*st.m := by {
    --  rw [Nat.lt_iff_add_one_le] at h_internal; rw [Nat.lt_iff_add_one_le]
    --  rw[← st.h_m_pow2H] at h_internal;
    --  ring_nf; nth_rw 1 [← one_add_one_eq_two]; rw [← Nat.mul_two 1]
    --  rw [← Nat.add_mul 1 j 2]; rw [Nat.add_comm 1 j]
    --  gcongr
    --}
    --have h2j2m : 2*j < 2*st.m := by omega

    have h_0_lt_h := d.internal_0_lt_h h_internal
    set C := (d.L+d.R)/2 with h_C
    -- deduplicare 'sta roba
    have hCL : C = d.L + 2 ^ (d.h - 1) := by
      subst C
      rw [d.h_R]
      rw [← Nat.add_assoc d.L d.L (2 ^ d.h)]
      rw [← Nat.mul_two d.L]
      rw [← Nat.pow_pred_mul (by omega)]
      rw [← Nat.add_mul d.L (2 ^ (d.h - 1)) 2]
      rw [Nat.mul_div_left (d.L + 2 ^ (d.h - 1)) (by omega)]

    have h_C_eq : C = 2^(d.h-1)*(2*d.k+1) := by
      rw [hCL]
      rw [d.h_L]
      rw [← Nat.two_pow_pred_mul_two (by omega)]
      grind

    set dLeft := CoverageIntervalDefs.from_st n (2 * j) st (by omega) (by omega) with h_dL
    set dRight := CoverageIntervalDefs.from_st n (2 * j + 1) st (by omega) (by omega) with h_dR

    -- deduplicare 'sta roba
    have h_intervs :
      (dLeft.L = d.L ∧ dLeft.R = C)
      ∧ (dRight.L = C ∧ dRight.R = d.R) := by
      have hll : dLeft.L = d.L := by
        rw[d.h_L, d.h_k, d.h_h, d.h_l]
        rw[dLeft.h_L, dLeft.h_k, dLeft.h_h, dLeft.h_l]
        rw [Nat.log2_two_mul (by omega)]
        rw [Nat.pow_add_one']
        rw [← Nat.mul_sub 2 j (2 ^ j.log2)]
        rw [← Nat.mul_assoc (2 ^ (st.H - (j.log2 + 1))) 2 (j - 2 ^ j.log2)]
        rw [← Nat.pow_add_one 2 (st.H - (j.log2 + 1))]
        rw [← tsub_tsub_assoc ?_ (by omega)]
        grind
        rw [← Nat.log2_lt (by omega)] at h_internal
        omega

      have hlr : dLeft.R = C := by
        rw[hCL]
        rw[dLeft.h_R]
        rw[hll]
        rw [Nat.add_right_inj]
        rw[d.h_h, d.h_l]
        rw[dLeft.h_h, dLeft.h_l]
        simp
        rw [Nat.log2_two_mul (by omega)]
        grind

      have hrl : dRight.L = dLeft.R := by
        rw[dLeft.h_R, dLeft.h_L, dLeft.h_k, dLeft.h_h, dLeft.h_l]
        rw[dRight.h_L, dRight.h_k, dRight.h_h, dRight.h_l]
        rw[odd_log2 j (by omega)]
        rw [← Nat.mul_add_one (2 ^ (st.H - (2 * j).log2)) (2 * j - 2 ^ (2 * j).log2)]
        rw [← Nat.sub_add_comm ?_]
        rw [← Nat.le_log2 (by omega)]

      have hrr : dRight.R = d.R := by
        rw[dRight.h_R, hrl, hlr, hCL, d.h_R]
        --rw [Nat.add_assoc d.L (2 ^ (d.h - 1)) (2 ^ dRight.h)]
        nth_rw 3 [← Nat.two_pow_pred_mul_two (by omega)]
        rw [Nat.mul_two (2 ^ (d.h - 1))]
        rw [← Nat.add_assoc d.L (2 ^ (d.h - 1)) (2 ^ (d.h - 1))]
        simp
        rw[d.h_h, d.h_l]
        rw[dRight.h_h, dRight.h_l]
        rw[odd_log2 j (by omega)]
        rw [Nat.log2_two_mul (by omega)]
        grind

      constructor
      · constructor
        · exact hll
        · exact hlr
      · constructor
        · rw[hrl, hlr]
        · rw[hrr]


    have h_updateLeft := update_helper_correctness α inst n (2*j) x C val pos st
      (by omega) (by omega) (by omega) b1
    simp [← h_dL] at h_updateLeft
    rw[← h_x, ← h_y] at h_updateLeft
    simp [h_intervs] at h_updateLeft

    have h_prop_left : st_prop_except_ancestors st.m (2 * j) b1 := by
      unfold st_prop_except_ancestors
      intro i h_i0 h_i h_i_ub
      exact h_input i h_i0 (by{
        intro g g0
        specialize h_i (g+1)
        simp at h_i
        rw [Nat.pow_add_one'] at h_i
        rw [Nat.mul_div_mul_left j (2 ^ g) (by omega)] at h_i
        assumption
      }) h_i_ub
    simp [h_prop_left] at h_updateLeft
    set bLeft := (update_helper n st val pos (2 * j) d.L C (by omega) b1).ret with h_bLeft

    have h_updateRight := update_helper_correctness α inst n (2*j+1) C y val pos st
      (by omega) (by omega) (by omega) bLeft
    simp [← h_dR] at h_updateRight
    rw[← h_x, ← h_y] at h_updateRight
    simp [h_intervs] at h_updateRight

    have h_prop_right : st_prop_except_ancestors st.m (2 * j + 1) bLeft := by
      unfold st_prop_except_ancestors
      intro i h_i0 h_i h_i_ub
      have roba := h_updateLeft.left i h_i0 (by{
        have h_tmp := succ_div_even_eq_div_even_pow2
        intro g g0
        specialize h_i g
        specialize h_tmp j g
        simp [g0] at h_tmp
        rw[h_tmp] at h_i
        simp [g0] at h_i
        --rw [Nat.pow_add_one'] at h_i
        --rw [Nat.mul_div_mul_left j (2 ^ g) (by omega)] at h_i
        assumption
      }) h_i_ub
      exact roba
    simp [h_prop_right] at h_updateRight
    set bRight := (update_helper n st val pos (2 * j + 1) C d.R (by omega) bLeft).ret with h_bRight

    constructor
    · unfold st_prop_except_ancestors
      intro i h_i0 h_i_not_anc h_i_ub
      simp [Vector.set, Vector.get, Array.set, List.getElem_set]
      split_ifs <;> expose_names
      all_goals try grind
      --· rw[h_1] at h_2; rw [Nat.add_eq_left] at h_2; contradiction
      --· rw[h] at h_1; rw [Nat.Simproc.eq_add_gt i ?_] at h_1; contradiction
      --  grind
      --· rw[h] at h_2; rw [right_eq_mul₀ (by grind)] at h_2
      --  contradiction
      --· grind
      --· grind
      all_goals try have hij : i = j/(2^1) := by omega
      · specialize h_i_not_anc 1
        simp at h_i_not_anc
        simp at hij
        contradiction
      · specialize h_i_not_anc 1
        simp at h_i_not_anc
        simp at hij
        contradiction
      · have h_updateRight := h_updateRight.left
        unfold st_prop_except_ancestors at h_updateRight

        have h_uRI := h_updateRight
        specialize h_uRI i
        simp [h_i0, h_i_ub] at h_uRI
        have h_i_not_anc_2j1 : (∀ g > 0, i ≠ (2 * j + 1) / 2 ^ g) := by{
          intro g g0
          rw[succ_div_even_eq_div_even_pow2 j g g0]
          rw [← Nat.two_pow_pred_mul_two (by omega)]
          rw [Nat.mul_comm (2 ^ (g - 1)) 2]
          rw [Nat.mul_div_mul_left j (2 ^ (g - 1)) (by omega)]
          if hg : g = 1 then { grind } else {
            exact h_i_not_anc (g-1) (by omega)
          }
        }
        simp at h_i_not_anc_2j1
        apply h_uRI at h_i_not_anc_2j1
        simp [Vector.get] at h_i_not_anc_2j1
        exact h_i_not_anc_2j1

    · rw[← st.h_m_pow2H] at h_internal
      simp [h_disjoint]
      simp [Vector.set, Vector.get, Array.set, List.getElem_set]
      split_ifs <;> expose_names
      · rw[h] at h_internal
        rw [add_lt_iff_neg_right st.m] at h_internal
        contradiction
      · by_cases h_C_where : C ≤ pos
        · apply h_updateRight.right at h_C_where
          simp [h_disjoint] at h_C_where
          simp [Vector.get] at h_C_where
          exact h_C_where
        · simp at h_C_where
          subst bRight
          unfold update_helper
          simp only [TimeM.tick]
          simp [h2j12m, h_C_where]
          have h_tmp : ¬pos = C := by omega
          simp [h_tmp]
          simp [h_disjoint] at h_updateLeft
          apply h_updateLeft.right at h_C_where
          simp [Vector.get] at h_C_where
          exact h_C_where

  · contradiction


def update (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : ℕ) : TimeM (SegmentTree α n) := do
  if hposm: p < st.m then
    let b := update_helper n st x p 1 0 st.m (by omega) st.a

    ⟨⟨
      st.m,
      st.H,
      b.ret,
      st.h_m0,
      st.h_mn,
      st.h_m2n,
      st.h_m_pow2H,
      by {
        have h1_2m : 1 < 2*st.m := by{
          rw [Nat.lt_iff_add_one_le]; rw[show 1+1 = 2*1 from rfl]; rw [Nat.mul_le_mul_left_iff (by omega)];
          rw [Nat.one_le_iff_ne_zero]; rw [Nat.ne_zero_iff_zero_lt]; exact st.h_m0}

        have proof := update_helper_correctness α inst n 1 0 st.m x p st (by omega) (by exact h1_2m) hposm st.a

        set d := CoverageIntervalDefs.from_st n 1 st (by omega) (by exact h1_2m) with h_d
        simp at proof
        have h_b : b = update_helper n st x p 1 0 st.m (by omega) st.a := by rfl
        rw[← h_b] at proof
        rw[d.h_R, d.h_L, d.h_k, d.h_h, d.h_l] at proof
        rw [show 2 ^ Nat.log2 1 = 1 from rfl] at proof
        simp at proof
        rw [show Nat.log2 1 = 0 from rfl] at proof
        simp at proof
        rw[← st.h_m_pow2H] at proof
        simp at proof

        suffices hhh: st_prop_except_ancestors st.m 1 st.a by
          apply proof at hhh
          have hhh := hhh.left
          unfold st_prop_except_ancestors at hhh
          intro j h_j hjm
          specialize hhh j
          have h_j0 := h_j
          rw [← gt_iff_lt] at h_j
          apply hhh at h_j
          simp [hjm] at h_j
          apply h_j
          intro g h_g0
          rw [Nat.div_eq_of_lt (by {rw [Nat.one_lt_two_pow_iff]; omega})]
          rw [← ne_eq j 0]
          omega

        unfold st_prop_except_ancestors
        intro i hi
        rw [gt_iff_lt] at hi
        intro hg
        intro him
        apply st.h_children at hi
        apply hi at him
        exact him
      }
    ⟩, b.time⟩
  else ✓ ⟨
      st.m,
      st.H,
      st.a,
      st.h_m0,
      st.h_mn,
      st.h_m2n,
      st.h_m_pow2H,
      st.h_children⟩

theorem update_helper_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p j L R : ℕ)
  (h_j0 : j > 0) (b : Vector α (2 * st.m)) :
  (update_helper n st x p j L R h_j0 b).time ≤ 1 + 2 * (2 + st.H - Nat.log 2 j)
:= by
  unfold update_helper
  split_ifs with h_j2m h_sub h_disjoint <;> simp
  set C := ((L + R) / 2) with h_C
  have h_H_geq_log2j := st.H_geq_log2j j h_j0 h_j2m -- used by omega

  if h_pC : p < C then {
    have h_left := update_helper_time α inst n st x p (2 * j) L C (by omega) b
    have h_right : (update_helper n st x p (2 * j + 1) C R (by omega) ((update_helper n st x p (2 * j) L C (by omega) b).ret)).time = 1 := by
      unfold update_helper
      split_ifs <;> simp
      grind
    grw [h_left, h_right]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    simp
    omega
  } else {
    have h_left : (update_helper n st x p (2 * j) L C (by omega) b).time = 1 := by
      unfold update_helper
      split_ifs <;> simp
      grind
    have h_right := update_helper_time α inst n st x p (2 * j + 1) C R (by omega) (update_helper n st x p (2 * j) L C (by omega) b).ret
    grw [h_left, h_right]
    rw [odd_log2' j (by omega)]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    simp
    omega
  }


theorem update_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : ℕ) :
  (update α inst n st x p).time ≤ 4 + 2 * (Nat.log 2 n + 2) + 1
:= by
  -- TODO deduplicate this proof with that of query_time
  unfold update
  simp
  split_ifs with hposm
  · have h_helper := update_helper_time α inst n st x p 1 0 st.m (by omega) st.a
    grw [h_helper]
    simp
    rw [Nat.add_comm, Nat.mul_add]
    simp
    apply (Nat.pow_le_pow_iff_right (a:=2) (by omega)).mp
    rw [← st.h_m_pow2H]
    cases st.h_m2n with
    | inl h_m2n =>
      rw [h_m2n]
      exact Nat.one_le_pow ?_ 2 (by omega)
    | inr h_m2n =>
      grw [h_m2n]
      have h_pow_log_n : 2 ^ (Nat.log 2 n + 1) > n := by
        if h_n0 : n ≠ 0 then {
          simp
          rw [← Nat.log_lt_iff_lt_pow (by omega) (by omega)]
          simp
        } else {
          simp_all
        }
      nth_rw 2 [show 2 = 1 + 1 from rfl]
      rw [← Nat.add_assoc (Nat.log 2 n) 1 1]
      rw [Nat.pow_add_one 2 (Nat.log 2 n + 1)]
      grw [h_pow_log_n]
      omega
  · simp
