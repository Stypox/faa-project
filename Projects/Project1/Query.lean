import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.CoverageIntervalDefs
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false

def query (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) : TimeM α :=
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

lemma query_aux_correctness (α : Type) (inst: Monoid α) (n j p q x y : ℕ) (st : SegmentTree α n) (h_j0 : j > 0) (h_j : j < 2*st.m) :
  let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
  d.L = x ∧ d.R = y →
    (query.query_aux α inst n st p q j x y h_j0).ret = (st.a.toArray.extract (st.m + max d.L p) (st.m + min d.R q)).foldl (fun a b => a * b) 1
  := by

  unfold query.query_aux

  set d := CoverageIntervalDefs.from_st n j st h_j0 h_j with h_d
  have H_spec := st.h_m_pow2H
  have H_spec2: st.H = st.m.log2 := by
    rw[H_spec]
    rw [Nat.log2_two_pow]
  simp only [TimeM.tick] -- get rid of time measurement

  intro h_xy
  rw [← h_xy.left, ← h_xy.right]

  split_ifs with h_sub h_disjoint --<;> (
  --  try rw [← h_d];
  --  try rw [← h_d] at h_sub;
  --  try rw [← h_d] at h_disjoint;
  --)
  · -- case where coverage interval [L, R) is completely included in query interval [p, q)
    rw [Nat.max_eq_left h_sub.left]
    rw [Nat.min_eq_left h_sub.right]
    rw [st.coverage_interval n j h_j0 h_j]

  · -- case where coverage interval [L, R) and query interval [p, q) are disjoint
    cases h_disjoint with
    | inl h_disjoint =>
      rw [Nat.min_eq_right (by grw[h_disjoint, d.L_lt_R])]
      suffices h_ineq : q ≤ max d.L p by
        rw [Array.extract_eq_empty_of_le ?_]
        · rw[Array.foldl_empty]
          rfl
        · rw [st.a.size_toArray]
          rw [Nat.two_mul st.m]
          rw [Nat.add_min_add_left st.m q st.m]
          rw [Nat.add_le_add_iff_left]
          trans q
          · omega
          · assumption
      trans d.L <;> omega
    | inr h_disjoint =>
      suffices h_ineq : min d.R q ≤ max d.L p by
        rw [Array.extract_eq_empty_of_le ?_]
        · rw[Array.foldl_empty]
          rfl
        · rw [st.a.size_toArray]
          rw [Nat.two_mul st.m]
          rw [Nat.add_min_add_left st.m (min d.R q) st.m]
          rw [Nat.add_le_add_iff_left]
          trans (min d.R q)
          · omega
          · assumption
      trans d.R
      · omega
      · grw[h_disjoint]
        omega

  · -- all other cases: the intersection of the two intervals is non-empty and different from [L, R)
    -- (and we are surely not in a leaf node)
    have h_internal : j < 2^st.H := d.not_in_leaf p q (by grind) (by grind)
    have h_0_lt_h := d.internal_0_lt_h h_internal

    set C := (d.L+d.R)/2 with h_C
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
    suffices h_intervs :
      (dLeft.L = d.L ∧ dLeft.R = C)
      ∧ (dRight.L = C ∧ dRight.R = d.R)
      by

      -- conv_lhs simplifies only the left side of the = to remove the time information
      -- (simplifying the right too breaks the proof that we made before adding the time information)
      conv_lhs => simp
      rw [query_aux_correctness α inst n (2*j) p q d.L C st (by omega) (by omega)]
      rw [query_aux_correctness α inst n (2*j+1) p q C d.R st (by omega) (by omega)]
      · simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]

        have h_eq_logs : (2 * j + 1).log2 = (2 * j).log2 := by
          rw [Nat.log2_eq_iff (by omega)]
          constructor
          · trans 2*j
            · rw [← Nat.le_log2 (by omega)]
            · omega
          · rw [lt_iff_le_and_ne]
            constructor
            · rw [Nat.add_one_le_iff]
              rw [Nat.add_one (2 * j).log2]
              have hb: 1<2 := by omega
              apply Nat.lt_pow_succ_log_self at hb
              specialize hb (2*j)
              rw [Nat.log2_eq_log_two]
              assumption
            · rw [Nat.pow_add_one']
              by_contra a
              have h_2div : 2 ∣ 2 * 2 ^ (2 * j).log2 := by omega
              rw[← a] at h_2div
              rw [Nat.dvd_add_right (by omega)] at h_2div
              contradiction

        rw[h_eq_logs]
        rw [Nat.log2_two_mul (by omega)]
        rw[← d.h_l]
        rw [Nat.sub_add_eq st.H d.l 1]
        rw[← d.h_h]
        rw [Nat.pow_add_one']
        rw [Nat.sub_add_comm]
        · rw [← Nat.mul_sub 2 j (2 ^ d.l)]
          rw[← d.h_k]
          rw [← Nat.mul_add_one (2 ^ (d.h - 1)) (2 * d.k)]
          rw [← Nat.mul_assoc (2 ^ (d.h - 1)) 2 d.k]
          rw [Nat.two_pow_pred_mul_two h_0_lt_h]
          rw [← Nat.mul_add_one (2 ^ (d.h - 1)) (2 * d.k + 1)]
          rw [Nat.add_assoc (2 * d.k) 1 1]
          rw [show 1 + 1 = 2 from rfl]
          rw [← Nat.mul_add_one 2 d.k]
          rw [← Nat.mul_assoc (2 ^ (d.h - 1)) 2 (d.k + 1)]
          rw [Nat.two_pow_pred_mul_two h_0_lt_h]
          rw [Nat.mul_add_one (2 ^ d.h) d.k]
          rw[← d.h_L, ← d.h_R, ← h_C_eq]

          -- splittare in 3 casi:
          -- 1. p>=C (ovvero l'intersez tra l'intervallo query e la prima meta' del coverage interval e' vuota)
          -- 2. q<=C (ovvero l'intersezione con la seconda meta' e' vuota)
          -- 2. p < C < q, quindi si usa foldl combine
          have h_Cmid : d.L < C ∧ C < d.R := by omega

          if h_pC : C ≤ p then
            rw [Array.extract_eq_empty_of_le ?_]
            · rw[Array.foldl_empty]
              rw [one_mul]
              have htmp: max C p = p := by omega
              rw[htmp]
              have htmp: max d.L p = p := by omega
              rw[htmp]
            · rw [st.a.size_toArray]
              rw [Nat.two_mul st.m, st.h_m_pow2H]
              rw [Nat.add_min_add_left (2^st.H) (min C q) (2^(st.H))]
              rw [Nat.add_le_add_iff_left]
              trans C
              · omega
              · omega
          else if h_Cq : q ≤ C then
            simp at h_pC
            set fold1 := Array.foldl (fun a b ↦ a * b) 1 (st.a.toArray.extract (2^st.H + max d.L p) (2^st.H + min C q)) with h_f1
            rw [Array.extract_eq_empty_of_le ?_]
            · rw[Array.foldl_empty]
              rw[mul_one]
              subst fold1
              have htmp: min C q = q := by omega
              rw[htmp]
              have htmp: min d.R q = q := by omega
              rw[htmp]
            · rw [st.a.size_toArray]
              rw [Nat.two_mul st.m, st.h_m_pow2H]
              rw [Nat.add_min_add_left (2^st.H) (min d.R q) (2^st.H)]
              rw [Nat.add_le_add_iff_left]
              trans C
              · omega
              · omega
          else
            simp at h_pC
            simp at h_Cq
            have htmp : min C q = C := by omega
            rw[htmp]
            have htmp : max C p = C := by omega
            rw[htmp]
            clear htmp
            rw[foldl_combine]
            rw [Nat.add_le_add_iff_left]
            rw [Nat.add_le_add_iff_left]
            constructor
            · omega
            · omega

        · rw [Nat.mul_le_mul_left_iff (by omega)]
          rw [d.h_l]
          rw [← Nat.le_log2 (by omega)]

      · exact h_intervs.right
      · exact h_intervs.left


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


#check Nat.lt_pow_succ_log_self
#check Array.foldl_empty

theorem query_correctness (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
  (query α inst n st p q).ret = (st.a.toArray.extract (st.m + p) (st.m + q)).foldl (fun a b => a * b) 1
:= by
  unfold query
  have h1 : 1 < 2*st.m := by
    have h_m0 := st.h_m0
    rw [show (st.m > 0) = (0 < st.m) from rfl] at h_m0
    rw [Nat.lt_iff_add_one_le] at h_m0
    simp_all
    calc
      1 < 2 := by trivial
      _ = 2*1 := by trivial
      _ ≤ 2*st.m := by grw [h_m0]
  rw [query_aux_correctness α inst n 1 p q 0 st.m st (by omega) h1]
  · simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]
    rw [show 2 ^ Nat.log2 1 = 1 from rfl]
    rw [show 1 - 1 = 0 from rfl]
    rw [Nat.mul_zero (2 ^ (st.H - Nat.log2 1))]
    rw [Nat.zero_max p]
    rw [Nat.zero_add (2 ^ (st.H - Nat.log2 1))]
    rw [show Nat.log2 1 = 0 from rfl]
    rw [Nat.sub_zero st.H]
    have htmp := st.h_m_pow2H
    rw[← htmp]
    suffices h_arr_estr : (st.a.toArray.extract (st.m + p) (st.m + min st.m q)) = (st.a.toArray.extract (st.m + p) (st.m + q)) by
      rw[h_arr_estr]
    rw [← Nat.add_min_add_left st.m st.m q]
    rw [← Nat.two_mul st.m]
    have h_2m_s : 2*st.m = st.a.toArray.size := by grind
    nth_rw 2 [h_2m_s]
    rw [show
        st.a.toArray.extract (st.m + p) (min st.a.toArray.size (st.m + q)) =
          Array.extract.loop st.a.toArray
            ((min (min st.a.toArray.size (st.m + q)) st.a.toArray.size).sub (st.m + p)) (st.m + p)
            (Array.emptyWithCapacity
              ((min (min st.a.toArray.size (st.m + q)) st.a.toArray.size).sub (st.m + p)))
        from rfl]
    nth_rw 1 [Nat.min_right_comm st.a.toArray.size (st.m + q) st.a.toArray.size]
    rw [Nat.min_self st.a.toArray.size]
    rw [show
        st.a.toArray.extract (st.m + p) (st.m + q) =
          Array.extract.loop st.a.toArray ((min (st.m + q) st.a.toArray.size).sub (st.m + p))
            (st.m + p) (Array.emptyWithCapacity ((min (st.m + q) st.a.toArray.size).sub (st.m + p)))
        from rfl]
    grind
  · simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]
    rw [show Nat.log2 1 = 0 from rfl]
    rw [show 2 ^ 0 = 1 from rfl]
    grind

-- trivial cases for query_aux: the time taken is 1
theorem query_aux_time_out_sub_disjoint (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) (j L R: ℕ) (h_j0 : j > 0)
  (h_out_sub_disjoint : ¬(j < 2*st.m) ∨ (p ≤ L ∧ R ≤ q) ∨ (q ≤ L ∨ R ≤ p)) :
  (query.query_aux α inst n st p q j L R h_j0).time = 1
:= by
  unfold query.query_aux
  split_ifs with h_j h_sub h_disjoint <;> simp
  grind

-- when the interval [p, q) overlaps with [L, R) without being fully contained,
-- i.e. p or q are outside the range [L, R), the query_aux recursion continues non-trivially only
-- either left or right and with smaller [L, R) s.t. [p, q) still overlaps with [L, R) the same way,
-- so we can do the proof recursively as well
theorem query_aux_time_semiinterval (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) (j L R: ℕ) (h_j0 : j > 0)
  (h_semiinterval : p ≤ L ∨ q ≥ R) :
  (query.query_aux α inst n st p q j L R h_j0).time ≤ 2 * (2 + st.H - Nat.log 2 j) + 1
:= by
  unfold query.query_aux
  split_ifs with h_j2m h_sub h_disjoint <;> simp
  set C := ((L + R) / 2) with h_C
  have h_H_geq_log2j := st.H_geq_log2j j h_j0 h_j2m -- used by omega

  cases h_semiinterval with
  | inl h_pL => if h_Cq : q < C then {
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
      rw [odd_log2' j (by omega)]
      rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
      simp
      omega
    }
  | inr h_qR => if h_Cp : p < C then {
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
      rw [odd_log2' j (by omega)]
      rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
      simp
      omega
    }
termination_by R - L

-- for the general proof, we distinguish three cases based on the position of C with respect to p and q,
-- and notice that in when C is outside [p, q) one of the recursive query_aux calls trivially terminates,
-- while when C is in [p, q) the recursive query_aux calls are of the form supported by
-- `query_aux_time_semiinterval`
theorem query_aux_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) (j L R: ℕ) (h_j0 : j > 0) :
  (query.query_aux α inst n st p q j L R h_j0).time ≤ 4 * (2 + st.H - Nat.log 2 j) + 1
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
    rw [odd_log2' j (by omega)]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    omega
  } else {
    have h_left := query_aux_time_semiinterval α inst n st p q (2 * j) L C (by omega) (by omega)
    have h_right := query_aux_time_semiinterval α inst n st p q (2 * j + 1) C R (by omega) (by omega)
    grw [h_left, Nat.add_left_comm, h_right]
    rw [odd_log2' j (by omega)]
    rw [Nat.mul_comm 2 j, Nat.log_mul_base (by omega) (by omega)]
    ring_nf
    omega
  }

-- completes the proof by lifting the general proof about query_aux into the specific
-- case where j=1, L=0, R=m,
-- and then proves the time complexity in terms of n based on the time complexity in terms of m
theorem query_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
  (query α inst n st p q).time ≤ 4 * (Nat.log 2 n + 2) + 9
:= by
  unfold query
  have h_aux := query_aux_time α inst n st p q 1 0 st.m (by omega)
  grw [h_aux]
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
    nth_rw 4 [show 2 = 1 + 1 from rfl]
    rw [← Nat.add_assoc (Nat.log 2 n) 1 1]
    rw [Nat.pow_add_one 2 (Nat.log 2 n + 1)]
    grw [h_pow_log_n]
    omega
