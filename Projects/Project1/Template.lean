import Mathlib.Tactic

set_option autoImplicit false

--def V : Array ℕ := [1, 2, 3].toArray
--#eval Array.foldl (fun a b => (a + b)) 0 V 1 2

structure SegmentTree (α : Type*) [Monoid α] (n : ℕ) where
  n := n
  m := n -- temporary
  -- TODO maybe store original vector
  a : Vector α (2*m)

  -- assumptions
  h_m : m > 0
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


-- helper lemma
lemma foldl_combine (α : Type*) [Monoid α] (n l mid r : ℕ) (a : Vector α n) (h_bounds: l ≤ mid ∧ mid ≤ r):
    ((a.toArray.extract l mid).foldl (fun a b => a * b) 1)
    * ((a.toArray.extract mid r).foldl (fun a b => a * b) 1)
    = (a.toArray.extract l r).foldl (fun a b => a * b) 1
    := by
  expose_names
  set fold1 := Array.foldl (fun a b ↦ a * b) 1 (a.toArray.extract l mid) with h_f1
  --set fold2 := Array.foldl (fun a b ↦ a * b) 1 (a.toArray.extract mid r) with h_f2
  rw [show
      fold1 * Array.foldl (fun a b ↦ a * b) 1 (a.toArray.extract mid r) =
        inst.toMulOneClass.toMul.1 fold1 (Array.foldl (fun a b ↦ a * b) 1 (a.toArray.extract mid r))
      from rfl]
  nth_rw 1 [show (fun a b ↦ a * b) = Mul.mul from rfl]
  rw [← Array.foldl_assoc (op := Mul.mul) (ha:= ?_)]
  · rw [show Mul.mul fold1 1 = fold1 * 1 from rfl]
    rw [mul_one fold1]
    rw [show (fun a b ↦ a * b) = Mul.mul from rfl]
    rw [h_f1]
    rw [show (fun a b ↦ a * b) = Mul.mul from rfl]
    rw [← Array.foldl_append]
    suffices (a.toArray.extract l mid ++ a.toArray.extract mid r) = (a.toArray.extract l r) by
      rw[this]
    simp
    rw [Nat.min_eq_left h_bounds.left]
    rw [Nat.max_eq_right h_bounds.right]
  · --rw [show Mul.mul = inst.toMulOneClass.toMul.1 from rfl]
    refine { assoc := ?_ }
    exact inst.mul_assoc


-- helper lemma
lemma leaf_interval {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n) (h0j : 0 < j) (hj2m: j < 2*st.m) :
  let l := Nat.log2 j
  let k := j - 2^l
  let H := st.h_n_pow2.choose
  let h := H - l
  let L := 2^h * k
  let R := L + 2^h
  st.m ≤ j → (R = L+1 ∧ L = j-st.m) :=
  by
  set l := Nat.log2 j with h_l
  set k := j - 2^l with h_k
  set H := st.h_n_pow2.choose with h_H
  set h := H - l with h_h
  set L := 2^h * k with h_L
  set R := L + 2^h with h_R
  have H_spec := st.h_n_pow2.choose_spec
  simp only []

  intro hjm
  have exp0 : H ≤ l := by -- in this case a[j] is a leaf of the tree
      subst l
      rw [H_spec] at hjm
      subst H
      rw [Nat.le_log2 ?_]
      · assumption
      · omega
  have pow2_0 : 2^h = 1 := by
    subst h
    rw [Nat.sub_eq_zero_of_le exp0]
    omega
  have h_LeqR : R = L+1 := by
    subst R
    rw [pow2_0]
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

  rw [← h_h, ← h_k, ← h_L, ← h_R, h_LeqR]
  simp
  subst L
  rw [pow2_0]
  simp
  subst k
  rw [h_leqm]




lemma SegmentTree.h_coverage_interval {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
      let l := Nat.log2 j
      let k := j - 2^l
      let H := st.h_n_pow2.choose
      let h := H - l
      let L := 2^h * k
      let R := L + 2^h
      st.a.get ⟨j, hj2m⟩ = (st.a.toArray.extract (st.m+L) (st.m+R)).foldl (fun a b => a * b) 1
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
  · -- in this case a[j] is a leaf of the tree
    have h_leaf := hjm
    apply leaf_interval n j st h0j hj2m at h_leaf
    rw [← h_h, ← h_k, ← h_L, ← h_R] at h_leaf
    rw [← h_h, ← h_k, ← h_L, ← h_R, h_leaf.left, h_leaf.right]

    rw [foldl_single2 (h:=?_)] -- without (h:=?_) it says "don't know how to synthesize placeholder"
    · rw [Array.getElem_extract]
      simp [Vector.get]
      apply getElem_congr_idx
      rw [Nat.add_sub_of_le hjm]
    · simp
      rw [Nat.min_eq_left ?_]
      · omega
      · omega

  · rw [st.h_children j h0j (by omega)]   -- in this case a[j] is an internal node of the tree
    rw [st.h_coverage_interval (h0j:=by omega)]
    rw [st.h_coverage_interval (h0j:=by omega)]

    have expNot0 : l < H := by
      subst l
      simp at hjm
      rw [H_spec] at hjm
      subst H
      rw [← Nat.log2_lt (by omega)] at hjm
      omega

    set aL := st.m + L with h_aL
    set aC := st.m + 2^(h-1)*(2*k+1) with h_aC  -- = (aL + aR)/2
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

    apply foldl_combine α (2*st.m) aL aC aR st.a ⟨?_, ?_⟩
    · -- aL <= aC
      rw [h_aL, h_aC]
      subst L
      subst k
      subst l
      subst h
      subst H
      simp
      nth_rw 1 [← Nat.pow_pred_mul (by omega)]
      rw [Nat.mul_assoc (2 ^ (st.h_n_pow2.choose - j.log2 - 1)) 2 (j - 2 ^ j.log2)]
      rw [Nat.mul_le_mul_left_iff (by simp)]
      omega
    · -- aC <= aR
      rw [h_aC, h_aR]
      subst R
      subst L
      subst k
      subst l
      subst h
      subst H
      simp
      rw [← Nat.mul_add_one (2 ^ (st.h_n_pow2.choose - j.log2)) (j - 2 ^ j.log2)]
      nth_rw 3 [← Nat.pow_pred_mul (by omega)]
      rw [Nat.mul_assoc (2 ^ (st.h_n_pow2.choose - j.log2 - 1)) 2 (j - 2 ^ j.log2 + 1)]
      rw [Nat.mul_le_mul_left_iff (by simp)]
      omega


structure BuildHelperStruct (α : Type*) [Monoid α] (m j : ℕ) where
  a : Vector α (2*m - j)
  proof (i : ℕ) (h_i_lb : i ≥ j) (h_i0 : i > 0) (h_i_ub : i < m) :
    a.get ⟨2*m-1 - i, by omega⟩ = a.get ⟨2*m-1 - 2*i, by omega⟩ * a.get ⟨2*m-1 - (2*i+1), by omega⟩

def build_helper {α : Type*} [inst: Monoid α] (m j : ℕ) (xs : Vector α m) -- (h_n_pow2 : ∃ k, m = 2^k) (a : Vector α (2*m -j -1))
    : BuildHelperStruct α m j :=
  if h2m : j ≥ 2*m then
    ⟨⟨#[], (by simp_all)⟩, by grind⟩

  else
    let ⟨a, proof⟩ := build_helper m (j+1) xs

    if h0: j = 0 then
      ⟨
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
      ⟨
        (a.push xs[j-m]).cast (by omega),
        by omega -- trivial by default, the quantifiers are all empty
      ⟩
    else
      have h_2j2_le_2m : 2*j + 2 ≤ 2*m := by
        simp_all
        rw [Nat.lt_iff_add_one_le] at h_jm
        rw [Nat.Simproc.add_le_le j (by omega)] at h_jm
        grw [h_jm]
        omega
      ⟨
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


def build (α : Type*) [Monoid α] (n : ℕ) (h_n : n > 0) (h_n_pow2 : ∃ k, n = 2^k)
    (xs : Vector α n) : SegmentTree α n :=
  let b := (build_helper n 0 xs)
  ⟨
    n,
    n,
    b.a.reverse,
    h_n,
    h_n_pow2,
    by {
      -- we have the proof in b.proof already, so it's "true by construction"
      intro j h0j hjm
      simp [Vector.get]
      have proof := b.proof j (by omega) h0j hjm
      simp [Vector.get] at proof
      exact proof
    }
  ⟩

noncomputable def query (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p : Nat) (q : Nat) : α :=
  query_aux 1 (by omega) (by have := st.h_m; omega)
  where query_aux (j : ℕ) (h_j0 : j > 0) (h_j : j < 2*st.m) : α :=
    --if h_jm : j ≥ st.m then
    --  if p=j ∧ q=j+1 then
    --    st.a.get ⟨j, h_j⟩
    --  else inst.one
    --else
    let l := Nat.log2 j
    let k := j - 2^l
    let H := st.h_n_pow2.choose
    let h := H - l
    let L := 2^h * k
    let R := L + 2^h
    if h_sub : p ≤ L ∧ R ≤ q then
      st.a.get ⟨j, h_j⟩
    else if h_empty : q ≤ L ∨ p ≥ R then
      inst.one
    --else if h_jm : j ≥ st.m then
    --  st.a.get ⟨j, h_j⟩
    else
      have h_jm : j < st.m := by    -- if we got to this case, j is not a leaf
        by_contra h_jm
        simp_all
        have h_leaf := h_jm
        apply leaf_interval n j st h_j0 h_j at h_leaf
        have h_l : l = Nat.log2 j := by rfl
        have h_k : k = j - 2^l := by rfl
        have h_H : H = st.h_n_pow2.choose := by rfl
        have h_h : h = H - l := by rfl
        have h_L : L = 2^h * k := by rfl
        have h_R : R = L + 2^h := by rfl
        rw [← h_h, ← h_k, ← h_L, ← h_R] at h_leaf
        rw[h_leaf.left] at h_sub
        rw[h_leaf.left] at h_empty
        obtain ⟨he1, he2⟩ := h_empty
        rw [Nat.lt_add_one_iff] at he2
        apply h_sub at he2
        rw [Nat.lt_add_one_iff] at he2
        grw[he2] at he1
        rw [lt_self_iff_false L] at he1
        exact he1

      (query_aux (2*j) (by omega) (by omega)) * (query_aux (2*j + 1) (by omega) (by omega))


lemma query_aux_correctness (α : Type*) (inst: Monoid α) (n j p q : ℕ) (st : SegmentTree α n) (h_j0 : j > 0) (h_j : j < 2*st.m) :
  let l := Nat.log2 j
  let k := j - 2^l
  let H := st.h_n_pow2.choose
  let h := H - l
  let L := 2^h * k
  let R := L + 2^h
  query.query_aux α inst n st p q j h_j0 h_j = (st.a.toArray.extract (st.m + max L p) (st.m + min R q)).foldl (fun a b => a * b) 1
  := by

  unfold query.query_aux
  set l := Nat.log2 j with h_l
  set k := j - 2^l with h_k
  set H := st.h_n_pow2.choose with h_H
  set h := H - l with h_h
  set L := 2^h * k with h_L
  set R := L + 2^h with h_R
  have H_spec := st.h_n_pow2.choose_spec
  simp only []
  --rw [← h_H, ← h_h, ← h_k, ← h_L, ← h_R]
  have h_LltR : L < R := by
    subst R
    simp

  split_ifs <;> (
    expose_names;
    try rw [← h_H, ← h_h, ← h_k, ← h_L, ← h_R];
    try rw [← h_H, ← h_h, ← h_k, ← h_L, ← h_R] at h_1;
    try rw [← h_H, ← h_h, ← h_k, ← h_L, ← h_R] at h_2;
    )
  · -- case where coverage interval [L, R) is completely included in query interval [p, q)
    rw [Nat.max_eq_left h_1.left]
    rw [Nat.min_eq_left h_1.right]
    rw [st.h_coverage_interval n j h_j0 h_j]

  · -- case where coverage interval [L, R) and query interval [p, q) are disjoint
    --simp at h_1
    cases h_2 <;> expose_names
    · rw [Nat.min_eq_right (by {grw[h_2]; omega})]
      suffices h_ineq : q ≤ max L p by
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
      trans L <;> omega
    · sorry
  · -- all other cases: the intersection of the two intervals is non-empty and different from [L, R)
    -- (and we are surely not in a leaf node)
    sorry

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
  rw [show 2 ^ Nat.log2 1 = 1 by simp [Nat.log2_eq_log_two]]
  rw [show 1 - 1 = 0 from rfl]
  rw [Nat.mul_zero (2 ^ (st.h_n_pow2.choose - Nat.log2 1))]
  rw [Nat.zero_max p]
  rw [Nat.zero_add (2 ^ (st.h_n_pow2.choose - Nat.log2 1))]
  rw [show Nat.log2 1 = 0 by simp [Nat.log2_eq_log_two]]
  rw [Nat.sub_zero st.h_n_pow2.choose]
  have htmp := st.h_n_pow2.choose_spec
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
  proof (i : ℕ) (h_i_lb : i ≥ j) (h_i0 : i > 0) (h_i_ub : i < m) :
    a.get ⟨i, by omega⟩ = a.get ⟨2*i, by omega⟩ * a.get ⟨2*i+1, by omega⟩

noncomputable def update (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : Nat) : SegmentTree α n :=
  let b := update_aux 1 (by omega) (by have := st.h_m; omega) ⟨st.a, by {
    intro i _ h_i h_i_ub
    exact st.h_children i h_i h_i_ub
  }⟩
  ⟨
    st.n,
    st.m,
    b.a,
    st.h_m,
    st.h_n_pow2,
    by {
      intro j h_j hjm
      exact b.proof j (by omega) h_j hjm
    }
  ⟩

  where update_aux (j : ℕ) (h_j0 : j > 0) (h_j : j < 2*st.m) (b : UpdateHelperStruct α st.m j) : UpdateHelperStruct α st.m j :=
    let l := Nat.log2 j
    let k := j - 2^l
    let H := st.h_n_pow2.choose
    let h := H - l
    let L := 2^h * k
    let R := L + 2^h
    if h_sub : p = L ∧ p = R-1 then
      ⟨
        b.a.set j x h_j,
        by {
          -- just proving that we are in a leaf...
          intro i h_ij h_i0 h_i_ub
          suffices ¬(i < st.m) by contradiction
          obtain ⟨h_pL, h_pR⟩ := h_sub
          rw [h_pL] at h_pR
          subst R
          subst L
          rw [eq_tsub_iff_add_eq_of_le (by exact NeZero.one_le)] at h_pR
          rw [Nat.add_right_inj] at h_pR
          have h_pR := h_pR.symm
          rw [Nat.pow_eq_one] at h_pR
          rw [or_iff_right (by trivial)] at h_pR
          subst h
          rw [Nat.sub_eq_zero_iff_le] at h_pR
          have h_pR : 2^H ≤ 2^l := by refine Nat.pow_le_pow_right (by omega) h_pR
          subst l
          subst H
          rw [← st.h_n_pow2.choose_spec] at h_pR
          rw [Nat.log2_eq_log_two] at h_pR
          simp
          grw [h_ij]
          trans 2 ^ Nat.log 2 j
          · assumption
          · rw [Nat.pow_le_iff_le_log (by omega) (by omega)]
        }
      ⟩
    else if h_empty : p < L ∨ p ≥ R then
      b
    else
      have h_jm : j < st.m := by    -- if we got to this case, j is not a leaf
        by_contra h_jm
        simp_all
        have h_leaf := h_jm
        apply leaf_interval n j st h_j0 h_j at h_leaf
        have h_l : l = Nat.log2 j := by rfl
        have h_k : k = j - 2^l := by rfl
        have h_H : H = st.h_n_pow2.choose := by rfl
        have h_h : h = H - l := by rfl
        have h_L : L = 2^h * k := by rfl
        have h_R : R = L + 2^h := by rfl
        rw [← h_h, ← h_k, ← h_L, ← h_R] at h_leaf
        rw[h_leaf.left] at h_sub
        rw[h_leaf.left] at h_empty
        obtain ⟨he1, he2⟩ := h_empty
        rw [Nat.lt_add_one_iff] at he2
        have h_Pl : p = L := by omega
        simp_all

      let b := update_aux (2*j) (by omega) (by omega) ⟨b.a, by {
        intro i h_ij h_i h_i_ub
        exact b.proof i (by omega) h_i (by omega)
      }⟩
      let b := update_aux (2*j + 1) (by omega) (by omega) ⟨b.a, by {
        intro i h_ij h_i h_i_ub
        exact b.proof i (by omega) h_i (by omega)
      }⟩
      ⟨
        b.a.set j (b.a.get ⟨2*j, by omega⟩ * b.a.get ⟨2*j + 1, by omega⟩) h_j,
        by {

        }
      ⟩
