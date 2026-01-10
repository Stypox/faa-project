import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.CoverageIntervalDefs
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false


structure BuildHelperStruct (α : Type) [Monoid α] (m j : ℕ) where
  a : Vector α (2*m - j)
  proof (i : ℕ) (h_i_lb : i ≥ j) (h_i0 : i > 0) (h_i_ub : i < m) :
    a.get ⟨2*m-1 - i, by omega⟩ = a.get ⟨2*m-1 - 2*i, by omega⟩ * a.get ⟨2*m-1 - (2*i+1), by omega⟩

def build_helper {α : Type} [inst: Monoid α] (m j : ℕ) (xs : Vector α m)   -- builds the vector that stores the nodes of the tree, but in reverse order
    : TimeM (BuildHelperStruct α m j) := do
  if h2m : j ≥ 2*m then               -- base case: we start with an empty vector
    ✓ ⟨⟨#[], (by simp_all)⟩, by grind⟩ -- we create an empty array, which is O(1)

  else                                -- recursive case
    let ⟨a, proof⟩ ← build_helper m (j+1) xs

    if h0: j = 0 then                 -- "fake node" of index 0: it's not part of the tree but we still add it to the vector,
                                      -- the whole tree was already built by the recursive call
      ✓ ⟨ -- we are doing a single push operation on the array, which is O(1)

        (a.push inst.one).cast (by rw [Nat.sub_add_eq (2 * m) j 1, Nat.sub_one_add_one (by omega)]),
        by {
          intros i h_i_lb h_i0 h_i_ub
          simp [Vector.cast, Vector.get, Array.getElem_push]
          split_ifs with h1 h2 h3 _ h4 h5 <;> try omega
          -- all of the previus cases -> just use `proof`
          specialize proof i (by omega) (by omega) h_i_ub
          simp [Vector.get] at proof
          assumption
        }
      ⟩
    else if h_jm : j ≥ m then         -- leaf of the tree
      ✓ ⟨ -- we are doing a single push operation on the array, which is O(1)
        (a.push xs[j-m]).cast (by omega), -- ...
        by omega -- trivial by default, the quantifiers are all empty
      ⟩
    else                              -- internal node of the tree
      have h_2j2_le_2m : 2*j + 2 ≤ 2*m := by
        simp_all
        rw [Nat.lt_iff_add_one_le] at h_jm
        rw [Nat.Simproc.add_le_le j (by omega)] at h_jm
        grw [h_jm]
        omega
      ✓ ⟨ -- we are doing two array accesses, one multiplication and one push operation on the array, all O(1)
        (a.push (a[2*m-1 - 2*j]'(by {
          rw [Nat.sub_sub, tsub_lt_tsub_iff_left_of_le ?_] <;> omega
        }) * a[2*m-1 - (2*j+1)]'(by {
          rw [Nat.sub_sub, tsub_lt_tsub_iff_left_of_le ?_] <;> omega
        }))).cast (by omega),
        by {
          intros i h_i_lb h_i0 h_i_ub
          simp [Vector.cast, Vector.get, Array.getElem_push]
          split_ifs with h1 h2 h3 _ h4 h5 <;> try omega
          · -- all of the previus cases -> just use `proof`
            specialize proof i (by omega) (by omega) h_i_ub
            simp [Vector.get] at proof
            assumption
          · -- the newly added element
            suffices i = j by simp [this]
            omega
        }
      ⟩

structure mHstruct (n : ℕ) where
  m : ℕ
  H : ℕ
  proofmH : m = 2^H
  proofmn : n ≤ m
  proofnm : m = 1 ∨ m < n*2-1

def compute_m_H (n : ℕ) : TimeM (mHstruct n) := do
  if hn1: n ≤ 1 then
    ✓ ⟨1, 0, by omega, by omega, by omega⟩
  else
    let ⟨m1, H1, proof1_m_pow2H, proof1_mn, proof1_m2n⟩ ← compute_m_H ((n+1)/2)
    have proof2_m_pow2H : m1*2 = 2^(H1+1) := by
      rw [Nat.pow_add_one 2 H1]
      omega
    have proof2_mn : n ≤ m1*2 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)] at proof1_mn
      ring_nf at proof1_mn
      simp at proof1_mn
      assumption
    have proof2_m2n : m1*2 = 1 ∨ m1*2 < n*2-1 := by
      right
      cases proof1_m2n with
      | inl proof1_m2n => omega
      | inr proof1_m2n =>
        suffices m1 + 1 ≤ (n + 1) / 2 * 2 - 1 by omega
        rw [Nat.lt_iff_add_one_le] at proof1_m2n
        apply proof1_m2n

    ✓ ⟨m1*2, H1+1, proof2_m_pow2H, proof2_mn, proof2_m2n⟩ -- just O(1) operations


def build (α : Type) (inst: Monoid α) (n : ℕ) (h_n : n > 0) (xs : Vector α n) : TimeM (SegmentTree α n) := do
  let ⟨m, H, proof_m_pow2H, proof_mn, proof_m2n⟩ ← compute_m_H n
  have h_m : m > 0 := by omega
  let ⟨a, proof⟩ ← build_helper m 0 ((xs ++ (Vector.replicate (m-n) inst.one)).cast (by omega))
  ✓ ⟨
    m,
    H,
    a.reverse,
    h_m,
    proof_mn,
    proof_m2n,
    proof_m_pow2H,
    by {  -- we have the proof of the segment tree property "h_children" in build_helper.proof
          --  already, therefore the "build" function is "correct by construction"
      intro j h0j hjm
      simp [Vector.get]
      have proof := proof j (by omega) h0j hjm
      simp [Vector.get] at proof
      exact proof
    }
  ⟩, (m-n + 2*m)      -- cost of augmenting vector a with identity element before calling build_helper, and then reversing it afterwards


lemma compute_m_H_time_base (n : ℕ) (hn : n ≤ 1) : (compute_m_H n).time = 1 := by
  unfold compute_m_H
  simp_all

lemma compute_m_H_time_rec (n : ℕ) (hn : n > 1) : (compute_m_H n).time = Nat.log 2 (n-1) + 2 := by
  unfold compute_m_H
  split_ifs with hn1 <;> try grind
  simp
  if hn3 : n ≥ 3 then {
    have h_rec := compute_m_H_time_rec ((n + 1) / 2)
    rw [h_rec (by omega)]
    simp
    rw [← Nat.log_mul_base (by omega) (by omega)]
    if h_n_even : Even n then {
      rw [Nat.succ_div_of_not_dvd (by grind)]
      rw [Nat.sub_one_mul (n / 2) 2]
      rw [Nat.div_two_mul_two_of_even (by assumption)]
      have ⟨r, hnr⟩ := h_n_even
      rw [hnr, ← Nat.two_mul r]
      rw [← Nat.mul_sub_one 2 r]
      rw [show 2 * r - 1 = 2 * (r - 1) + 1 from by omega]
      symm
      apply odd_log2'
      omega
    } else {
      rw [Nat.succ_div_of_dvd (by grind)]
      simp
      set n' := n-1 with hn'
      have h_n'_even : Even n' := by grind
      rw [← Nat.Simproc.add_eq_le n' (by omega)] at hn'
      rw [← hn']
      have ⟨r', hn'r'⟩ := h_n'_even
      rw [hn'r', ← Nat.two_mul r']
      apply odd_log2'
      omega
    }
  } else {
    have hn2 : n = 2 := by omega
    rw [hn2]
    simp_all [compute_m_H]
  }

theorem compute_m_H_time (n : ℕ) : (compute_m_H n).time ≤ Nat.log 2 (n-1) + 2 := by
  if hn : n > 1 then {
    simp [compute_m_H_time_rec n hn]
  } else {
    simp [compute_m_H_time_base n (by omega)]
  }

theorem build_helper_time {α : Type} [inst: Monoid α] (m j : ℕ) (xs : Vector α m)
  : (build_helper m j xs).time ≤ 2*m-j+1
:= by
  unfold build_helper
  split_ifs with h2m h0 h_jm <;> simp
  · have h_rec := build_helper_time m (j+1) xs
    simp_all
    rw [Nat.sub_one_add_one (by omega)] at h_rec
    assumption
  · have h_rec := build_helper_time m (j+1) xs
    simp_all
    rw [tsub_add_eq_tsub_tsub (2 * m) j 1] at h_rec
    rw [Nat.sub_one_add_one (by omega)] at h_rec
    assumption
  · have h_rec := build_helper_time m (j+1) xs
    simp_all
    rw [tsub_add_eq_tsub_tsub (2 * m) j 1] at h_rec
    rw [Nat.sub_one_add_one (by omega)] at h_rec
    assumption

theorem build_time (α : Type) (inst: Monoid α) (n : ℕ) (h_n : n > 0) (xs : Vector α n) :
  (build α inst n h_n xs).time ≤ 3 + 10*n      -- 9n + log2 (n-1) - 7 (= log2(n-1)+2 + n-2 + 2x(2n-1)+1 + 2x(2n-1))
:= by
  unfold build
  simp
  have h_compute_m_H_time := compute_m_H_time n
  have h_build_helper_time := fun (xs : Vector α (compute_m_H n).ret.m) ↦ (build_helper_time ((compute_m_H n).ret.m) 0 xs)
  have h_m : (compute_m_H n).ret.m ≤ 2 * n := by {
    cases ((compute_m_H n).ret.proofnm) <;> omega
  }
  have h_2m : 2 * (compute_m_H n).ret.m ≤ 4 * n := by {
    rw[show 4 = 2*2 from rfl]
    rw [Nat.mul_assoc 2 2 n]
    rw [Nat.mul_le_mul_left_iff (by omega)]
    assumption
  }
  grw [h_compute_m_H_time, h_build_helper_time, h_2m, h_m]
  rw [← Nat.sub_one_mul 2 n]
  ring_nf
  simp
  ring_nf
  rw [Nat.Simproc.add_le_le (3 + Nat.log 2 (n - 1)) (by omega)]
  rw [Nat.add_sub_assoc (by omega) 3]
  rw [← Nat.mul_sub n 10 9]
  simp
  exact log_sublinear n


-- def query_old (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) : α :=
--   query_aux 1 (by omega) (by have := st.h_m0; omega)
--   where query_aux (j: ℕ) (h_j0 : j > 0) (h_j : j < 2*st.m) : α :=
--     let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
--     -- si potrebbe fare un primo if che controlla se l'intervallo [p, q) e' vuoto
--     if h_sub : p ≤ d.L ∧ d.R ≤ q then   -- the coverage interval is a subinterval of the query interval
--       st.a.get ⟨j, h_j⟩
--     else if h_disjoint : q ≤ d.L ∨ d.R ≤ p then   -- the two intervals are disjoint
--       inst.one
--     --else if h_jm : j ≥ st.m then
--     --  st.a.get ⟨j, h_j⟩
--     else -- if we got to this case, j is not a leaf (and the two intervals have a proper, non-empty intersection)
--       have h_jm : j < st.m := by
--         rw [st.h_m_pow2H]
--         exact d.not_in_leaf p q h_sub h_disjoint
--       (query_aux (2*j) (by omega) (by omega)) * (query_aux (2*j + 1) (by omega) (by omega))


def query (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) : TimeM α :=
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
    rw [st.h_coverage_interval n j h_j0 h_j]

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

theorem query_correctness (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) :
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
theorem query_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) :
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


lemma update_helper_correctness (α : Type) (inst: Monoid α) (n j x y : ℕ) (val : α) (pos : Nat) (st : SegmentTree α n)
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
      all_goals have h_updateRight := h_updateRight.left
      all_goals unfold st_prop_except_ancestors at h_updateRight
      all_goals have h_uRI := h_updateRight
      all_goals specialize h_uRI i
      all_goals simp [h_i0, h_i_ub] at h_uRI
      all_goals have h_i_not_anc_2j1 : (∀ g > 0, i ≠ (2 * j + 1) / 2 ^ g) := by{
        intro g g0
        rw[succ_div_even_eq_div_even_pow2 j g g0]
        rw [← Nat.two_pow_pred_mul_two (by omega)]
        rw [Nat.mul_comm (2 ^ (g - 1)) 2]
        rw??
        }
      · sorry
      · sorry
      ·

    ·
      sorry
  · contradiction


def update (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : Nat) : TimeM (SegmentTree α n) := do
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


theorem update_time (α : Type) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : Nat) :
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


structure UpdateHelperStruct (α : Type*) [Monoid α] (m j : ℕ) where
  a : Vector α (2*m)
  proof (i : ℕ) (h_i0 : i > 0) (h_i_neq_j2 : ∀ g > 0, i ≠ j/(2^g)) (h_i_ub : i < m) :
    a.get ⟨i, by omega⟩ = a.get ⟨2*i, by omega⟩ * a.get ⟨2*i+1, by omega⟩

def update_old (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : Nat) : SegmentTree α n :=
  let b := update_aux 1 (by omega) (by have := st.h_m0; omega) ⟨st.a, by {
    intro i _ _ h_i_ub
    exact st.h_children i (by omega) h_i_ub
  }⟩
  ⟨
    st.m,
    st.H,
    b.a,
    st.h_m0,
    st.h_mn,
    st.h_m2n,
    st.h_m_pow2H,
    by {
      intro j h_j hjm
      exact b.proof j (by omega) (by {
        -- don't know why omega isn't working for something this trivial
        intro g h_g0
        rw [Nat.div_eq_of_lt (by {rw [Nat.one_lt_two_pow_iff]; omega})]
        omega
      }) hjm
    }
  ⟩

  where update_aux (j : ℕ) (h_j0 : j > 0) (h_j : j < 2*st.m) (b : UpdateHelperStruct α st.m j) : UpdateHelperStruct α st.m j :=
    let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
    if h_sub : p = d.L ∧ p+1 = d.R then
      have h_leaf : st.m ≤ j := by    -- if we got to this case, j is a leaf
        obtain ⟨h_pL, h_pR⟩ := h_sub
        rw [h_pL] at h_pR
        rw [st.h_m_pow2H]
        exact d.leaf_interval_R.mpr (by omega)

      ⟨
        b.a.set j x h_j,
        by {
          intro i h_i0 h_i_neq_j2 h_i_ub
          simp [Vector.set, Vector.get, Array.set, List.getElem_set]
          split_ifs with h1 h2 h3 h3 <;> try omega
          · specialize h_i_neq_j2 1 (by omega)
            omega
          · specialize h_i_neq_j2 1 (by omega)
            omega
          · exact b.proof i h_i0 h_i_neq_j2 h_i_ub
        }
      ⟩
    else if h_empty : p < d.L ∨ p ≥ d.R then
      b
    else
      have h_internal : j < 2^st.H := d.not_in_leaf p (p+1) (by grind) (by grind)

      let b := update_aux (2*j) (by omega) (by rw [st.h_m_pow2H]; omega) ⟨b.a, by {
        intro i h_i0 h_i_neq_j2 h_i_ub
        exact b.proof i h_i0 (by {
          intro g _
          specialize h_i_neq_j2 (g+1) (by omega)
          rw [Nat.pow_add_one 2 g] at h_i_neq_j2
          rw [pow_mul_comm' 2 g] at h_i_neq_j2
          rw [Nat.mul_div_mul_left j (2 ^ g) (by omega)] at h_i_neq_j2
          assumption
        }) (by omega)
      }⟩
      let b := update_aux (2*j + 1) (by omega) (by rw [st.h_m_pow2H]; omega) ⟨b.a, by {
        intro i h_i0 h_i_neq_j2 h_i_ub
        exact b.proof i (by omega) (by {
          intro g h_g0
          specialize h_i_neq_j2 g (by omega)
          rw [show 2 * j / 2 ^ g = (2 * j + 1) / 2 ^ g by {
            rcases g with _ | g <;> try contradiction
            rw [Nat.pow_add_one']
            rw [← Nat.div_div_eq_div_mul (2 * j + 1) 2 (2 ^ g)]
            rw [Nat.mul_div_mul_left j (2 ^ g) (by omega)]
            nth_rw 1 [show j = (2 * j + 1) / 2 by omega]
          }]
          assumption
        }) (by omega)
      }⟩
      ⟨
        b.a.set j (b.a.get ⟨2*j, by rw [st.h_m_pow2H]; omega⟩ * b.a.get ⟨2*j + 1, by rw [st.h_m_pow2H]; omega⟩) h_j,
        by {
          intro i h_i0 h_i_neq_j2 h_i_ub
          simp [Vector.set, Vector.get, Array.set, List.getElem_set]
          split_ifs with h1 h2 h3 h3 <;> try omega
          · simp_all
          · specialize h_i_neq_j2 1 (by omega)
            omega
          · specialize h_i_neq_j2 1 (by omega)
            omega
          · exact b.proof i h_i0 (by {
              intro g h_g0
              if h_g1 : g = 1 then {
                rw [h_g1]
                omega
              } else {
                specialize h_i_neq_j2 (g-1) (by omega)
                rw [← Nat.two_pow_pred_mul_two (by omega)]
                rw [Nat.mul_comm (2 ^ (g - 1)) 2]
                rw [← Nat.div_div_eq_div_mul (2 * j + 1) 2 (2 ^ (g - 1))]
                rw [show (2 * j + 1) / 2 = j by omega]
                assumption
              }
            }) h_i_ub
        }
      ⟩




-- EXAMPLES
section Examples


#check (inferInstance : AddMonoid Nat)
#check Monoid
#check Additive Nat
#check (inferInstance : Monoid Nat)
--#check (inferInstance : Monoid (Additive Nat))

section NatSum

instance NatWithSum : Monoid Nat where
  mul := Nat.add
  one := 0
  mul_one := Nat.add_zero
  one_mul := Nat.zero_add
  mul_assoc := Nat.add_assoc

def n : ℕ := 9

variable (xs : Vector ℕ n :=
  ⟨#[5, 8, 6, 3, 2, 7, 2, 6, 0],
    by decide⟩)


def mH  := compute_m_H n
#check mH
#eval mH.time
def m := mH.ret.1
def H := mH.1.2
#eval #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33].map (fun n ↦ (compute_m_H n).time == Nat.log 2 (n-1) + 2)
#eval #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33].map (fun n ↦ Nat.log 2 (n-1))
#eval m
#eval H

def albero := build ℕ NatWithSum n (by decide) xs

#check albero
#eval albero.time
#eval albero.ret.a
#eval query ℕ NatWithSum 9 albero.ret 2 8

def albero1 := update ℕ NatWithSum 9 albero.ret 5 3
#check albero1
#eval! albero1.ret.a



end NatSum


end Examples
