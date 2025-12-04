import Mathlib.Tactic

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


-- helper lemma
lemma foldl_combine {α : Type*} [Monoid α] (n l mid r : ℕ) (a : Vector α n) (h_bounds: 0 ≤ l ∧ l ≤ mid ∧ mid ≤ r ∧ r < n):
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
    rw [Nat.min_eq_left h_bounds.right.left]
    rw [Nat.max_eq_right h_bounds.right.right.left]
  · --rw [show Mul.mul = inst.toMulOneClass.toMul.1 from rfl]
    refine { assoc := ?_ }
    exact inst.mul_assoc



-- fundamental property of segment tree
lemma SegmentTree.h_coverage_interval (α : Type*) [Monoid α] (n j : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
      let l := Nat.log2 j
      let k := j - 2^l
      let H := st.h_n_pow2.choose
      let h := H - l
      let L := 2^h * k
      let R := L + 2^h - 1
      st.a.get ⟨j, by omega⟩ = (st.a.toArray.extract (st.m+L) (st.m+R+1)).foldl (fun a b => a * b) 1
    := by
  set l := Nat.log2 j with h_l
  set k := j - 2^l with h_k
  set H := st.h_n_pow2.choose with h_H
  set h := H - l with h_h
  set L := 2^h * k with h_L
  set R := L + 2^h - 1 with h_R
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
    have pow2_0 : 2^ h = 1 := by
      subst h
      rw [Nat.sub_eq_zero_of_le exp0]
      omega
    have h_LeqR : L = R := by
      subst R
      rw [pow2_0]
      simp
    have h_leqm : st.m = 2^l := by
      subst l
      rw [Nat.le_antisymm_iff]
      constructor
      · rw [H_spec] at hjm
        rw [← Nat.le_log2 ?_] at hjm
        rw [H_spec]
        exact Nat.pow_le_pow_right (n:=2) (by omega) (i:=st.h_n_pow2.choose) (j:=j.log2) hjm
        omega
      · rw [H_spec]
        rw [Nat.pow_le_pow_iff_right (by omega)]
        rw [Nat.le_iff_lt_add_one]
        rw [Nat.log2_lt]
        rw [Nat.pow_add_one 2 st.h_n_pow2.choose]
        rw [← H_spec]
        rw [Nat.mul_comm st.m 2]
        assumption
        omega

    rw [← h_h, ← h_k, ← h_L, ← h_R, ← h_LeqR]
    rw [foldl_single2 (h:=?_)] -- without (h:=?_) it says "don't know how to synthesize placeholder"
    · rw [Array.getElem_extract]
      simp [Vector.get]
      apply getElem_congr_idx
      --subst R
      subst L
      rw [pow2_0]
      --subst h
      --rw [Nat.sub_eq_zero_of_le exp0]
      simp
      subst k
      rw [h_leqm]
      omega
    · simp
      rw [Nat.min_eq_left ?_]
      · omega
      ·-- subst R
        subst L
        rw [pow2_0]
        --subst h
        --rw [Nat.sub_eq_zero_of_le exp0]
        omega

  · rw [st.h_children j h0j (by omega)]   -- in this case a[j] is an internal node of the tree
    rw [st.h_coverage_interval]
    rw [st.h_coverage_interval]

    rw [Array.foldl]
    sorry
    omega
    omega
    -- have a := foldl_combine α (2 * st.m) st.a
    --   (st.m + 2 ^ (st.H - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2))
    --   (st.m + (2 ^ (st.H - (2 * j).log2) * (2 * j - 2 ^ (2 * j).log2) + 2 ^ (st.H - (2 * j).log2) - 1))
    --   (st.m + 2 ^ (st.H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2))
    --   (st.m + (2 ^ (st.H - (2 * j + 1).log2) * (2 * j + 1 - 2 ^ (2 * j + 1).log2) + 2 ^ (st.H - (2 * j + 1).log2) - 1))
    --   --(by sorry)
    -- subst l
    -- rw [a]
    -- omega
    -- omega


def build (α : Type u) [Monoid α] (n : ℕ) (h_n_pow2 : ∃ k, n = 2^k)
    (xs : Vector α n) : SegmentTree α n := by
  sorry
