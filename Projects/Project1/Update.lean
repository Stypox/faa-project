import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.CoverageIntervalDefs
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false


-- UPDATE OPERATION:
-- function update: given a SegmentTree st, it contructs and returns a new SegmentTree from st, such that:
  -- all leaves are left unchanged except for the leaf p (= node st.m+p), which will get the new value x IFF it is a valid leaf,
  -- and the internal nodes are updated accordingly, so that the segment tree property h_children holds once again for all of them
  -- (in particular, only the ancestors of the leaf in question will need to be updated)


-- function update_helper produces a new Vector of size 2m that has been updated from position j going "downwards"
-- so that the only modified leaf is p (= node p+m) if it is valid, and for all internal nodes accept for j's proper ancestors the h_children property holds.
-- This is a top-down recursive function that operates in two phases:
-- 1. starting from node j we travel downward to locate leaf p, by recursion
-- 2. when we get to j=m+p we update the node and then return, thus traveling upward to the caller and updating all ancestors of the leaf on our way back
def update_helper {α : Type} [inst : Monoid α] (n : ℕ) (st : SegmentTree α n) (x : α) (p j L R : ℕ)
  (h_j0 : j > 0) (b : Vector α (2 * st.m)) : TimeM (Vector α (2 * st.m)) := do
  if h_j : j < 2*st.m then
    if h_sub : p = L ∧ p+1 = R then   -- if we got to this case, j is a leaf, so we perform the update and return
      ✓ (b.set j x h_j)
    else if h_empty : p < L ∨ p ≥ R then
      ✓ b
    else if h_int : 2*j+1 < 2*st.m then         -- if j is a (valid) internal node containing leaf p within its coverage interval [L, R):
      let C := (L+R)/2
      let b ← update_helper n st x p (2*j) L C (by omega) b           -- we call the function recursively on its children (one will terminate in 1 step)
      let b ← update_helper n st x p (2*j + 1) C R (by omega) b
      ✓ (b.set j (b.get ⟨2*j, (by omega)⟩ * b.get ⟨2*j +1, (by omega)⟩ ) (by omega))   -- and then update node j so that h_children holds for it as well
    else ✓ b
  else ✓ b

-- property of an (almost) segment tree Vector that checks if h_children is valid on all nodes except for j's proper ancestors
-- (which means in particular that it must hold for j).
-- When this property holds for j=1 (= root of the tree), the vector is a correct segment tree vector
def st_prop_except_ancestors {α : Type} [inst: Monoid α] (m j : ℕ) (a: Vector α (2*m)) : Prop :=
  ∀ (i : ℕ) (h_i0 : i > 0) (h_i_neq_j2 : ∀ g > 0, i ≠ j/(2^g)) (h_i_ub : i < m),
    a.get ⟨i, by omega⟩ = a.get ⟨2*i, by omega⟩ * a.get ⟨2*i+1, by omega⟩


-- we want to prove that the function update_helper "is correct" under some validity conditions, which means:
-- when j is a valid node, pos is a valid leaf, the parameters x y correspond to the coverage interval of node j, and st_prop_except_ancestors holds on the input vector for node j,
-- then st_prop_except_ancestors holds on the output of update_helper as well, and if leaf pos was indeed within the coverage interval then its value has been modified
lemma update_helper_correctness (α : Type) (inst: Monoid α) (n j x y : ℕ) (val : α) (pos : ℕ) (st : SegmentTree α n)
    (h_j0 : j > 0) (h_j : j < 2*st.m) (hposm: pos < st.m) (b1 : Vector α (2*st.m)) :
  let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
  let b2 := (update_helper n st val pos j x y h_j0 b1).ret
  (d.L = x ∧ d.R = y ∧ st_prop_except_ancestors st.m j b1) →
    st_prop_except_ancestors st.m j b2 ∧ ((x ≤ pos ∧ pos < y) → b2.get ⟨pos + st.m, by omega⟩ = val)
  := by

  set d := CoverageIntervalDefs.from_st n j st h_j0 h_j with h_d
  simp
  intro h_x h_y
  rw [← h_x, ← h_y]
  intro h_input

  unfold update_helper
  simp only [TimeM.tick] -- get rid of time measurement

  split_ifs with h_sub h_disjoint h_int <;> simp      -- the proof works recursively with 2 base cases, 1 recursive case (and a contraddictory one)

  · have h_leaf : st.m ≤ j := by                        -- if pos = L and pos + 1 = R, node j is exactly the leaf pos, because its coverage interval is [pos, pos+1).
        obtain ⟨h_pL, h_pR⟩ := h_sub                    -- In this case, the input vector b1 remains unchanged except for b1[j] which becomes val,
        rw [h_pL] at h_pR                               -- therefore st_prop_except_ancestors still holds forall internal nodes, and leaf pos was indeed correctly updated
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

  · constructor         -- when pos does not belong in the coverage interval of j, the input vector remains unchanged,
    · assumption        -- therefore st_prop_except_ancestors still trivially holds,
    · grind             -- and there was nothing to update

  all_goals have h_internal : j < 2^st.H := d.not_in_leaf pos (pos+1) (by grind) (by grind)   -- in all remaining cases, j is an internal node, with pos in its coverage interval
  all_goals simp at h_disjoint
  all_goals have h2j12m : 2*j + 1 < 2*st.m := by {
    rw [Nat.lt_iff_add_one_le] at h_internal; rw [Nat.lt_iff_add_one_le]
    rw[← st.h_m_pow2H] at h_internal;
    ring_nf; nth_rw 1 [← one_add_one_eq_two]; rw [← Nat.mul_two 1]
    rw [← Nat.add_mul 1 j 2]; rw [Nat.add_comm 1 j]
    gcongr
  }
  all_goals have h2j2m : 2*j < 2*st.m := by omega

  · rw [← d.h_C]
    set dLeft := CoverageIntervalDefs.from_st n (2 * j) st (by omega) (by omega) with h_dL
    set dRight := CoverageIntervalDefs.from_st n (2 * j + 1) st (by omega) (by omega) with h_dR

    have h_intervs : (dLeft.L = d.L ∧ dLeft.R = d.C) ∧ (dRight.L = d.C ∧ dRight.R = d.R) := by
      split_ands
      · exact (d.Lj_eq_L2j dLeft h_internal).symm
      · exact (d.Cj_eq_R2j dLeft h_internal).symm
      · exact (d.Cj_eq_L2jp1 dRight h_internal).symm
      · exact (d.Rj_eq_R2jp1 dRight h_internal).symm

    have h_updateLeft := update_helper_correctness α inst n (2*j) x d.C val pos st
      (by omega) (by omega) (by omega) b1               -- by way of recursion, update_helper on b1 produced an output bLeft that is correct,
    simp [← h_dL] at h_updateLeft                       -- which means that st_prop_except_ancestors holds on bLeft on all internal nodes except for the proper ancestors of 2j,
    rw [← h_x, ← h_y] at h_updateLeft                   -- (because the proper ancestors of 2j are strictly contained in those of j, therefore b1 meets the precondition for recursion)
    simp [h_intervs] at h_updateLeft                    -- and that, if pos is in the left half of [L, R), bLeft[pos] was updated to val

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
    set bLeft := (update_helper n st val pos (2 * j) d.L d.C (by omega) b1).ret with h_bLeft

    have h_updateRight := update_helper_correctness α inst n (2*j+1) d.C y val pos st
      (by omega) (by omega) (by omega) bLeft            -- as with the left child, we also know by recursion that update_helper on bLeft produced an output (bRight) that is correct,
    simp [← h_dR] at h_updateRight                      -- which means that st_prop_except_ancestors holds on bRight on all internal nodes except for the proper ancestors of 2j+1,
    rw[← h_x, ← h_y] at h_updateRight                   -- (because the proper ancestors of 2j+1 are the same as those of 2j, therefore bLeft meets the precondition for recursion)
    simp [h_intervs] at h_updateRight                   -- and that, if pos is in the right half of [L, R), bRight[pos] was updated to val

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
    set bRight := (update_helper n st val pos (2 * j + 1) d.C d.R (by omega) bLeft).ret with h_bRight


    -- let bFinal be the vector we get from bRight after computing bFinal[j] = bRight[2j]*bRight[2j+1].
    -- with the information we got through recursion, we are now left to prove that:
    -- 1. st_prop_except_ancestors now holds on bFinal forall proper ancestors of j
    -- 2. bFinal[pos] = val, regardless of where pos falls in the interval [L, R)

    constructor
    · unfold st_prop_except_ancestors                                 -- we know from 'st_prop_except_ancestors st.m (2 * j + 1) bRight'
      intro i h_i0 h_i_not_anc h_i_ub                                 -- that h_children also holds on bFinal forall internal nodes that are not proper ancestors of 2j+1,
      simp [Vector.set, Vector.get, Array.set, List.getElem_set]      -- which means it holds on bFinal forall internal nodes that are not ancestors of j;
      split_ifs <;> expose_names                                      -- but bFinal[j] = bFinal[2j]*bFinal[2j+1], therefore it holds on j (the "improper ancestor") as well,
      all_goals try grind                                             -- which means it now holds forall internal nodes that are not proper ancestors of j
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
      · by_cases h_C_where : d.C ≤ pos              -- if pos is in the right half of [L, R),
        · apply h_updateRight.right at h_C_where    -- the leaf was correctly updated in bRight
          simp [h_disjoint] at h_C_where
          simp [Vector.get] at h_C_where
          exact h_C_where
        · simp at h_C_where                         -- if pos is in the left half of [L, R),
          subst bRight                              -- the leaf was correctly updated in bLeft,
          unfold update_helper                      -- and then it was left unchanged in bRight because it does not belong in the coverage interval of the right child
          simp only [TimeM.tick]
          simp [h2j12m, h_C_where]
          have h_tmp : ¬pos = d.C := by omega
          simp [h_tmp]
          simp [h_disjoint] at h_updateLeft
          apply h_updateLeft.right at h_C_where
          simp [Vector.get] at h_C_where
          exact h_C_where

  · contradiction


-- function update: given a SegmentTree st, it constructs and returns a new SegmentTree from st, such that:
  -- all leaves are left unchanged except for the leaf p (= node st.m+p), which will get the new value x IFF it is a valid leaf,
  -- and the internal nodes are updated accordingly, so that the segment tree property h_children holds once again for all of them
  -- (in particular, only the ancestors of the leaf in question will need to be updated)
def update (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : ℕ) : TimeM (SegmentTree α n) := do
  if hposm: p < st.m then                                       -- if p denotes a valid leaf:
    let b := update_helper n st x p 1 0 st.m (by omega) st.a    -- the function calls update_helper from the root (j=1) to obtain an update segment tree vector from st.a,
                                                                -- which has cost O(log2 n)
    ⟨⟨
      st.m,
      st.H,
      b.ret,
      st.h_m0,
      st.h_mn,
      st.h_m2n,
      st.h_m_pow2H,
      by {                          -- this function then proves that h_children holds on Vector b leveraging the lemma update_helper_correctness,
                                    -- but we won't count this part in the time computations
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
  else ✓ st    -- if p is not a valid leaf, the original segment tree is returned


theorem update_helper_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p j L R : ℕ)
  (h_j0 : j > 0) (b : Vector α (2 * st.m)) :
  (update_helper n st x p j L R h_j0 b).time ≤ 5 + 2 * (st.H - Nat.log 2 j)   -- the time of update_helper is logarithmic in the height (h = H - l = H - log2 j) of the node j,
:= by                                                                         -- this is computed recursively
  unfold update_helper
  split_ifs with h_j2m h_sub h_disjoint <;> simp; all_goals try omega         -- all base cases take O(1) time,
  expose_names                                                                -- in the recursive case, j is an internal node that calls recursion on its two children,
  set C := ((L + R) / 2) with h_C                                             -- but leaf p can't be in both coverage intervals of the children, therefore one child will terminate immediately,
  have h_H_gt_log2j := st.H_geq_log2j j h_j0 h_j2m -- used by omega           -- while the other will allow recursion to move forward (or actually downward), until it reaches the leaf, performs the update, and then comes back up (updating the leaf's ancestors in the process),
  have h_internal : j < st.m := by omega                                      -- thus walking a total number of steps that is twice the height of j
  have h_H_geq_log2jp1 := st.internal_H_geq_log2jp1 j h_j0 h_internal

  if h_pC : p < C then {
    have h_left := update_helper_time α inst n st x p (2 * j) L C (by omega) b
    have h_right : (update_helper n st x p (2 * j + 1) C R (by omega) ((update_helper n st x p (2 * j) L C (by omega) b).ret)).time = 1 := by
      unfold update_helper
      split_ifs <;> simp
      grind
    grw [h_left, h_right]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    omega
  } else {
    have h_left : (update_helper n st x p (2 * j) L C (by omega) b).time = 1 := by
      unfold update_helper
      split_ifs <;> simp
      grind
    have h_right := update_helper_time α inst n st x p (2 * j + 1) C R (by omega) (update_helper n st x p (2 * j) L C (by omega) b).ret
    grw [h_left, h_right]
    rw [odd_log2' j]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    omega
  }


theorem update_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : ℕ) :
  (update α inst n st x p).time ≤ 9 + 2 * (Nat.log 2 n) -- 4 + 2 * (Nat.log 2 n + 2) + 1
:= by                     -- the time complexity of update is O(log2 n):
  unfold update           -- if pos is not a valid leaf it only takes O(1) time,
  simp                    -- otherwise it calls update_helper with j=1 (the root),
  split_ifs with hposm    -- which in this case has complexity O(H - log2 1) = O(H) = O(log2 m) = O(log2 n)
  · have h_helper := update_helper_time α inst n st x p 1 0 st.m (by omega) st.a
    grw [h_helper]
    simp
    rw [show 9 = 5 + 2*2 from rfl]
    rw [Nat.add_assoc 5 (2 * 2) (2 * Nat.log 2 n)]
    rw [← Nat.mul_add 2 2 (Nat.log 2 n)]
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
      rw [Nat.add_comm]
      rw [← Nat.add_assoc (Nat.log 2 n) 1 1]
      rw [Nat.pow_add_one 2 (Nat.log 2 n + 1)]
      grw [h_pow_log_n]
      omega
  · simp; omega
