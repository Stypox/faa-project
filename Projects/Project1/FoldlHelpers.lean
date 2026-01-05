import Mathlib.Tactic

set_option autoImplicit false


-- helper lemma
lemma foldl_single_list {α : Type*} (a : List α) (op : α → α → α) (init : α) (h : a.length = 1) :
    a.foldl op init = op init (a[0]) := by
  cases a with
  | nil => trivial
  | cons x xs =>
    simp
    cases xs with
    | nil => simp
    | cons y ts => simp_all

-- helper lemma
lemma foldl_single_array {α : Type*} (a : Array α) (op : α → α → α) (init : α) (h : a.size = 1) :
    a.foldl op init = op init (a[0]) := by
  have h_list := foldl_single_list a.toList op init (by simp_all)
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
