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

def build_helper {α : Type} [inst: Monoid α] (m j : ℕ) (xs : Vector α m)
    : TimeM (BuildHelperStruct α m j) := do
  if h2m : j ≥ 2*m then
    return ⟨⟨#[], (by simp_all)⟩, by grind⟩

  else
    let ⟨a, proof⟩ ← build_helper m (j+1) xs

    if h0: j = 0 then
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
    else if h_jm : j ≥ m then
      ✓ ⟨ -- we are doing a single push operation on the array, which is O(1)
        (a.push xs[j-m]).cast (by omega), -- ...
        by omega -- trivial by default, the quantifiers are all empty
      ⟩
    else
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

def compute_m_H (n : ℕ) : TimeM (mHstruct n) := do
  if hn1: n ≤ 1 then
    return ⟨1, 0, by omega, by omega⟩
  else
    let ⟨m1, H1, proof1H, proof1n⟩ ← compute_m_H ((n+1)/2)
    have proof2H : m1*2 = 2^(H1+1) := by
      rw [Nat.pow_add_one 2 H1]
      omega
    have proof2n : n ≤ m1*2 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)] at proof1n
      ring_nf at proof1n
      simp at proof1n
      assumption
    ✓ ⟨m1*2, H1+1, proof2H, proof2n⟩ -- just O(1) operations


def build (α : Type) (inst: Monoid α) (n : ℕ) (h_n : n > 0) (xs : Vector α n) : TimeM (SegmentTree α n) := do
  let ⟨m, H, proofmH, proofmn⟩ ← compute_m_H n
  have h_m : m > 0 := by omega
  let ⟨a, proof⟩ ← build_helper m 0 ((xs ++ (Vector.replicate (m-n) inst.one)).cast (by omega))
  ✓ ⟨
    n,
    m,
    H,
    a.reverse,
    h_m,
    proofmH,
    by {
      -- we have the proof in b.proof already, so it's "true by construction"
      intro j h0j hjm
      simp [Vector.get]
      have proof := proof j (by omega) h0j hjm
      simp [Vector.get] at proof
      exact proof
    }
  ⟩, (2*m)

def query (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) : α :=
  query_aux 1 (by omega) (by have := st.h_m; omega)
  where query_aux (j : ℕ) (h_j0 : j > 0) (h_j : j < 2*st.m) : α :=
    let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
    -- si potrebbe fare un primo if che controlla se l'intervallo [p, q) e' vuoto
    if h_sub : p ≤ d.L ∧ d.R ≤ q then
      st.a.get ⟨j, h_j⟩
    else if h_disjoint : q ≤ d.L ∨ d.R ≤ p then
      inst.one
    --else if h_jm : j ≥ st.m then
    --  st.a.get ⟨j, h_j⟩
    else -- if we got to this case, j is not a leaf
      have h_jm : j < st.m := by
        rw [st.h_m_pow2H]
        exact d.not_in_leaf p q h_sub h_disjoint
      (query_aux (2*j) (by omega) (by omega)) * (query_aux (2*j + 1) (by omega) (by omega))

#check Array.extract_eq_empty_of_le

lemma query_aux_correctness (α : Type*) (inst: Monoid α) (n j p q : ℕ) (st : SegmentTree α n) (h_j0 : j > 0) (h_j : j < 2*st.m) :
  let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
  query.query_aux α inst n st p q j h_j0 h_j = (st.a.toArray.extract (st.m + max d.L p) (st.m + min d.R q)).foldl (fun a b => a * b) 1
  := by

  unfold query.query_aux
  set d := CoverageIntervalDefs.from_st n j st h_j0 h_j with h_d
  have H_spec := st.h_m_pow2H
  have H_spec2: st.H = st.m.log2 := by
    rw[H_spec]
    rw [Nat.log2_two_pow]
  simp only []

  split_ifs with h_sub h_disjoint <;> (
    try rw [← h_d];
    try rw [← h_d] at h_sub;
    try rw [← h_d] at h_disjoint;
  )
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

    set C := 2^(d.h-1)*(2*d.k+1) with h_C --(L+R)/2 with h_C
    rw [query_aux_correctness α inst n (2*j) p q st (by omega)]
    rw [query_aux_correctness α inst n (2*j+1) p q st (by omega)]
    simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]

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
      rw[← d.h_L, ← d.h_R, ← h_C]

      -- splittare in 3 casi:
      -- 1. p>=C (ovvero l'intersez tra l'intervallo query e la prima meta' del coverage interval e' vuota)
      -- 2. q<=C (ovvero l'intersezione con la seconda meta' e' vuota)
      -- 2. p < C < q, quindi si usa foldl combine
      have h_Cmid : d.L < C ∧ C < d.R := by
        rw [h_C, d.h_R, d.h_L]
        rw [Nat.mul_add_one (2 ^ (d.h - 1)) (2 * d.k)]
        rw [← Nat.mul_assoc (2 ^ (d.h - 1)) 2 d.k]
        rw [Nat.pow_pred_mul h_0_lt_h]
        rw [Nat.lt_add_right_iff_pos]
        rw [Nat.add_lt_add_iff_left]
        constructor
        · rw [Nat.pow_pos_iff]; left; omega
        · rw [Nat.pow_lt_pow_iff_right (by omega)]
          omega

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



#check Nat.lt_pow_succ_log_self
#check Array.foldl_empty

theorem query_correctness (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) :
  query α inst n st p q =  (st.a.toArray.extract (st.m + p) (st.m + q)).foldl (fun a b => a * b) 1
  := by
  unfold query
  have h1 : 1 < 2*st.m := by
    have htmp := st.h_m
    rw [show (st.m > 0) = (0 < st.m) from rfl] at htmp
    rw [Nat.lt_iff_add_one_le] at htmp
    simp_all
    calc
      1 < 2 := by trivial
      _ = 2*1 := by trivial
      _ ≤ 2*st.m := by grw[htmp]
  rw [query_aux_correctness α inst n 1 p q st (by omega) h1]
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, st.h_m_pow2H]
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

structure UpdateHelperStruct (α : Type*) [Monoid α] (m j : ℕ) where
  a : Vector α (2*m)
  proof (i : ℕ) (h_i0 : i > 0) (h_i_neq_j2 : ∀ g > 0, i ≠ j/(2^g)) (h_i_ub : i < m) :
    a.get ⟨i, by omega⟩ = a.get ⟨2*i, by omega⟩ * a.get ⟨2*i+1, by omega⟩

def update (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : Nat) : SegmentTree α n :=
  let b := update_aux 1 (by omega) (by have := st.h_m; omega) ⟨st.a, by {
    intro i _ _ h_i_ub
    exact st.h_children i (by omega) h_i_ub
  }⟩
  ⟨
    st.n,
    st.m,
    st.H,
    b.a,
    st.h_m,
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
def m := mH.1
def H := mH.2
#eval m
#eval H

def albero := build ℕ NatWithSum n (by decide) xs

#check albero
#eval albero.ret.a
#eval query ℕ NatWithSum 9 albero.ret 2 8

def albero1 := update ℕ NatWithSum 9 albero.ret 5 3
#check albero1
#eval albero1.a



end NatSum


end Examples
