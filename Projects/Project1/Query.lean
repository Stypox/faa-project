import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.CoverageIntervalDefs
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false


-- QUERY OPERATION:
-- query function: given an interval [p, q), if we call p1:=max(0, p) and q1:=min(q, st.m)
-- and denote with leaf[] the bottom layer of the tree (= a[m] to a[2m-1]),
-- it returns the result of the computation leaf[p1] * leaf[p1+1] * .... * leaf[q1-2] * leaf[q1-1],
-- or the identity element if q1 ≤ p1

-- the query starts by calling query_aux from the root (j=1) and operates recursively:
-- at each node, if its coverage interval is entirely contained in the query interval, it returns the value stored at that node,
-- otherwise, if the two intervals are disjoint, it returns the identity element,
-- lastly, if the two have a proper intersection, the function will query the children of node j, and aggregate their answers

def query (α : Type) [inst: Monoid α] (n : ℕ) (st : SegmentTree α n) (p q : ℕ) : TimeM α :=
  query_aux 1 0 st.m (by omega)
  where query_aux (j L R: ℕ) (h_j0 : j > 0) : TimeM α := do
    if h_j2m : j < 2*st.m then
      if h_sub : p ≤ L ∧ R ≤ q then   -- the coverage interval is a subinterval of the query interval
        ✓ (st.a.get ⟨j, h_j2m⟩)
      else if h_disjoint : q ≤ L ∨ R ≤ p then   -- the two intervals are disjoint
        ✓ inst.one
      else -- if we got to this case, (j is not a leaf and) the two intervals have a proper, non-empty intersection
        let C := (L+R)/2
        let left ← query_aux (2*j) L C (by omega)
        let right ← query_aux (2*j + 1) C R (by omega)
        ✓ (left * right)
    else ✓ inst.one


#check Array.extract_eq_empty_of_le

-- we want to prove that the function query_aux "is correct" under some validity conditions, which means:
-- when j is a valid node and the parameters x y correspond to the coverage interval of node j,
-- then, given p1:=max(0, p) and q1:=min(q, st.m), the return value is indeed a[m + p1] * a[m + p1 + 1] * .... * a[m + q1 - 2] * a[m + q1 -1],
-- (which corresponds to a.toArray.extract (st.m + max d.L p) (st.m + min d.R q)).foldl (fun a b => a * b) 1)
lemma query_aux_correctness (α : Type) (inst: Monoid α) (n j p q x y : ℕ) (st : SegmentTree α n) (h_j0 : j > 0) (h_j : j < 2*st.m) :
  let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
  d.L = x → d.R = y →
    (query.query_aux α n st p q j x y h_j0).ret = (st.a.toArray.extract (st.m + max d.L p) (st.m + min d.R q)).foldl (fun a b => a * b) 1
  := by

  unfold query.query_aux

  set d := CoverageIntervalDefs.from_st n j st h_j0 h_j with h_d
  have H_spec := st.h_m_pow2H
  have H_spec2: st.H = st.m.log2 := by
    rw[H_spec]
    rw [Nat.log2_two_pow]
  simp only [TimeM.tick] -- get rid of time measurement

  intro h_x h_y
  rw [← h_x, ← h_y]
                                      -- the proof works recursively with 2 base cases and 1 recursive case
  split_ifs with h_sub h_disjoint
  · -- case where coverage interval [L, R) is completely included in query interval [p, q):
    rw [Nat.max_eq_left h_sub.left]               -- we get p1=L and q1=R, thus the desired output is a[m + L] * a[m + L + 1] * .... * a[m + R - 2] * a[m + R - 1],
    rw [Nat.min_eq_left h_sub.right]              -- which, by the lemma coverage_interval, is exactly the value stored in node j
    rw [st.coverage_interval n j h_j0 h_j]

  · -- case where coverage interval [L, R) and query interval [p, q) are disjoint
    cases h_disjoint with                                     -- disjoint intervals implies that either q ≤ L or R ≤ p,
    | inl h_disjoint =>                                       -- with both cases implying q1 ≤ p1, therefore a.toArray.extract (st.m + max d.L p) (st.m + min d.R q)) is empty,
      rw [Nat.min_eq_right (by grw[h_disjoint, d.L_lt_R])]    -- and the application of foldl yields 1
      have h_ineq : q ≤ max d.L p := by omega
      rw [Array.extract_eq_empty_of_le (by omega)]
      rw [Array.foldl_empty]
      rfl
    | inr h_disjoint =>
      have h_ineq : min d.R q ≤ max d.L p := by omega
      rw [Array.extract_eq_empty_of_le (by omega)]
      rw [Array.foldl_empty]
      rfl

  · -- all other cases: the intersection of the two intervals is non-empty and different from [L, R)
    -- (and we are surely not in a leaf node)
    have h_internal : j < 2^st.H := d.not_in_leaf p q (by grind) (by grind)
    rw [← d.h_C]
    set dLeft := CoverageIntervalDefs.from_st n (2 * j) st (by omega) (by omega) with h_dL
    set dRight := CoverageIntervalDefs.from_st n (2 * j + 1) st (by omega) (by omega) with h_dR

    -- conv_lhs simplifies only the left side of the = to remove the time information
    -- (simplifying the right too breaks the proof that we made before adding the time information)
    conv_lhs => simp
    rw [query_aux_correctness α inst n (2*j) p q d.L d.C st (by omega) (by omega)
      (by rw [← h_dL, d.Lj_eq_L2j dLeft h_internal]) (by rw [← h_dL, d.Cj_eq_R2j dLeft h_internal])]
    rw [query_aux_correctness α inst n (2*j+1) p q d.C d.R st (by omega) (by omega)
      (by rw [← h_dR, d.Cj_eq_L2jp1 dRight h_internal]) (by rw [← h_dR, d.Rj_eq_R2jp1 dRight h_internal])]
    rw [← h_dL, ← h_dR]
    rw [← d.Lj_eq_L2j dLeft h_internal, ← d.Cj_eq_R2j dLeft h_internal,
      ← d.Cj_eq_L2jp1 dRight h_internal, ← d.Rj_eq_R2jp1 dRight h_internal]

    -- in the recursive case, we assume by way of recursion that query_aux yields the correct results on the children for query interval [p, q),
    -- (resLeft (= fold1) = a[m+p1] * a[m+p1+1] * ... * a[m+min(q, C)-1]  and   resRight = a[m+max(p, C)] * a[m+max(p,C)+1] * ... * a[m+q1-1])
    -- and we are left to prove that their aggregation is indeed a[m + p1] * a[m + p1 + 1] * .... * a[m + q1 - 2] * a[m + q1 -1]

    -- we divide the goal in 3 cases:
    -- 1. p>=C (that means the intersection of the query interval and the first half of the coverage interval is empty)
    -- 2. q<=C (that means the intersection with the second half is empty)
    -- 2. p < C < q, neither intersection is empty (we will leverage the foldl_combine lemma)
    have h_Cmid : d.L < d.C ∧ d.C < d.R := d.internal_L_lt_C_lt_R h_internal

    if h_pC : d.C ≤ p then                            -- resLeft is actually 1 because [max(L, p), min(q, C)) is an empty interval,
      rw [Array.extract_eq_empty_of_le (by omega)]    -- therefore the result of the query on j is equal to resRight
      rw [Array.foldl_empty]
      rw [one_mul]
      rw [show max d.C p = p from by omega]
      rw [show max d.L p = p from by omega]
    else if h_Cq : q ≤ d.C then                       -- resRight is actually 1 because [max(C, p), min(q, R)) is an empty interval,
      set fold1 := Array.foldl (fun a b ↦ a * b) 1 (st.a.toArray.extract (st.m + max d.L p) (st.m + min d.C q)) with h_f1
      rw [Array.extract_eq_empty_of_le (by omega)]    -- therefore the result of the query on j is equal to resLeft (=fold1)
      rw [Array.foldl_empty]
      rw [mul_one]
      subst fold1
      rw [show min d.C q = q from by omega]
      rw [show min d.R q = q from by omega]
    else                                              -- neither intersection was empty, which means that min(q, C) = C = max(C, p),
      rw [show min d.C q = d.C from by omega]         -- therefore resLeft (= fold1) = a[m+p1] * a[m+p1+1] * ... * a[m+C-1],
      rw [show max d.C p = d.C from by omega]         -- and resRight = a[m+C] * a[m+C+1] * ... * a[m+q1-1],
      rw [foldl_combine]                              -- which means that their product is exactly a[m+p1] * a[m+p1+1] * .... * a[m+q1-2] * a[m+q1-1],
      omega                                           -- as stated by the lemma foldl_combine

#check Nat.lt_pow_succ_log_self
#check Array.foldl_empty

theorem query_correctness (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
  (query α n st p q).ret = (st.a.toArray.extract (st.m + p) (st.m + q)).foldl (fun a b => a * b) 1
:= by                     -- the correctness of query comes directly from that of query_aux
  unfold query
  have h1 : 1 < 2*st.m := by
    rw [show (1 < 2 * st.m) = (Nat.succ 1).le (2 * st.m) from rfl]; simp;
    have h_m0 := st.h_m0; omega
  rw [query_aux_correctness α inst n 1 p q 0 st.m st (by omega) h1]

  all_goals (
    try simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]
    try rw [show Nat.log2 1 = 0 from rfl]
    try rw [show 2 ^ 0 = 1 from rfl]
    try grind
  )

  · rw [show 1 - 1 = 0 from rfl]
    rw [show 2 ^ (st.H - 0) * 0 = 0 from rfl]
    rw [show st.H - 0 = st.H from rfl]
    rw [Nat.zero_add (2 ^ st.H)]
    rw [Nat.zero_max p]
    have htmp := st.h_m_pow2H
    rw[← htmp]
    suffices h_arr_estr : (st.a.toArray.extract (st.m + p) (st.m + min st.m q)) = (st.a.toArray.extract (st.m + p) (st.m + q)) by
      rw[h_arr_estr]
    grind


-- trivial cases for query_aux: the time taken is 1
theorem query_aux_time_out_sub_disjoint (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) (j L R: ℕ) (h_j0 : j > 0)
  (h_out_sub_disjoint : ¬(j < 2*st.m) ∨ (p ≤ L ∧ R ≤ q) ∨ (q ≤ L ∨ R ≤ p)) :
  (query.query_aux α n st p q j L R h_j0).time = 1
:= by
  unfold query.query_aux
  split_ifs with h_j h_sub h_disjoint <;> simp
  grind

-- when the interval [p, q) overlaps with [L, R) without being fully contained,
-- i.e. either p or q are outside the range [L, R), the query_aux recursion continues non-trivially only
-- either left or right and with smaller [L, R) s.t. [p, q) still overlaps with [L, R) the same way,
-- so we can do the proof recursively as well
theorem query_aux_time_semiinterval (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) (j L R: ℕ) (h_j0 : j > 0)
  (h_semiinterval : p ≤ L ∨ q ≥ R) :
  (query.query_aux α n st p q j L R h_j0).time ≤  2 * (2 + st.H - Nat.log 2 j) + 1 -- 5 + 2 * (st.H - Nat.log 2 j)
:= by
  unfold query.query_aux
  split_ifs with h_j2m h_sub h_disjoint <;> simp
  set C := ((L + R) / 2) with h_C
  have h_H_geq_log2j := st.H_geq_log2j j h_j0 h_j2m -- used by omega

  cases h_semiinterval with
  | inl h_pL => if h_Cq : q ≤ C then {
      have h_left := query_aux_time_semiinterval α inst n st p q (2 * j) L C (by omega) (by omega)
      have h_right := query_aux_time_out_sub_disjoint α inst n st p q (2 * j + 1) C R (by omega) (by omega)
      grw [h_left, h_right]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      simp
      omega
    } else {
      have h_left := query_aux_time_out_sub_disjoint α inst n st p q (2 * j) L C (by omega) (by omega)
      have h_right := query_aux_time_semiinterval α inst n st p q (2 * j + 1) C R (by omega) (by omega)
      grw [h_left, Nat.add_left_comm, Nat.add_comm, h_right]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      simp
      rw [Nat.mul_sub 2, Nat.mul_sub 2]
      rw [odd_log2' j]
      rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
      simp
      omega
    }
  | inr h_qR => if h_Cp : p ≤ C then {
      have h_left := query_aux_time_semiinterval α inst n st p q (2 * j) L C (by omega) (by omega)
      have h_right := query_aux_time_out_sub_disjoint α inst n st p q (2 * j + 1) C R (by omega) (by omega)
      grw [h_left, h_right]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      simp
      omega
    } else {
      have h_left := query_aux_time_out_sub_disjoint α inst n st p q (2 * j) L C (by omega) (by omega)
      have h_right := query_aux_time_semiinterval α inst n st p q (2 * j + 1) C R (by omega) (by omega)
      grw [h_left,  Nat.add_left_comm, Nat.add_comm, h_right]
      rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
      simp
      rw [Nat.mul_sub 2, Nat.mul_sub 2]
      rw [odd_log2' j]
      rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
      simp
      omega
    }
termination_by R - L

-- for the general proof, we distinguish three cases based on the position of C with respect to p and q,
-- and notice that when C is outside [p, q) one of the recursive query_aux calls trivially terminates,
-- while when C is in [p, q) the recursive query_aux calls are of the form supported by
-- `query_aux_time_semiinterval`
theorem query_aux_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) (j L R: ℕ) (h_j0 : j > 0) :
  (query.query_aux α n st p q j L R h_j0).time ≤ 4 * (2 + st.H - Nat.log 2 j) + 1  -- 9 + 4 * (st.H - Nat.log 2 j)
:= by
  unfold query.query_aux
  split_ifs with h_j2m h_sub h_disjoint <;> simp
  set C := ((L + R) / 2) with h_C
  have h_H_geq_log2j := st.H_geq_log2j j h_j0 h_j2m -- used by omega

  if h_qC : q < C then {
    have h_left := query_aux_time α inst n st p q (2 * j) L C (by omega)
    have h_right := query_aux_time_out_sub_disjoint α inst n st p q (2 * j + 1) C R (by omega) (by omega)
    grw [h_left, h_right]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    omega
  } else if h_pC : p > C then {
    have h_left := query_aux_time_out_sub_disjoint α inst n st p q (2 * j) L C (by omega) (by omega)
    have h_right := query_aux_time α inst n st p q (2 * j + 1) C R (by omega)
    grw [h_left, Nat.add_left_comm, Nat.add_comm, h_right]
    rw [odd_log2' j]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    omega
  } else {
    have h_left := query_aux_time_semiinterval α inst n st p q (2 * j) L C (by omega) (by omega)
    have h_right := query_aux_time_semiinterval α inst n st p q (2 * j + 1) C R (by omega) (by omega)
    grw [h_left, Nat.add_left_comm, h_right]
    rw [odd_log2' j]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    ring_nf
    omega
  }

-- completes the proof by lifting the general proof about query_aux into the specific
-- case where j=1, L=0, R=m,
-- and then proves the time complexity in terms of n based on the time complexity in terms of m
theorem query_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
  (query α n st p q).time ≤ 17 + 4 * (Nat.log 2 n)  -- 4 * (Nat.log 2 n + 2) + 9
:= by
  unfold query
  have h_aux := query_aux_time α inst n st p q 1 0 st.m (by omega)
  grw [h_aux]
  simp
  rw [Nat.add_comm, Nat.mul_add]
  simp
  rw [← Nat.add_assoc 1 8 (4 * st.H)]
  simp
  rw[show 17 = 9 + 8 from rfl]
  rw [Nat.add_assoc 9 8 (4 * Nat.log 2 n)]
  simp
  rw[show 8 = 4*2 from rfl]
  rw [← Nat.mul_add 4 2 (Nat.log 2 n)]
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
    rw [Nat.add_comm 2 (Nat.log 2 n)]
    nth_rw 4 [show 2 = 1 + 1 from rfl]
    rw [← Nat.add_assoc (Nat.log 2 n) 1 1]
    rw [Nat.pow_add_one 2 (Nat.log 2 n + 1)]
    grw [h_pow_log_n]
    omega
