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


def build (α : Type) (inst: Monoid α) (n : ℕ) (xs : Vector α n) : TimeM (SegmentTree α n) := do
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

theorem build_time (α : Type) (inst: Monoid α) (n : ℕ) (xs : Vector α n) :
  (build α inst n xs).time ≤ 8 + 10*n      -- 9n + log2 (n-1) - 7 (= log2(n-1)+2 + n-2 + 2x(2n-1)+1 + 2x(2n-1))
:= by
  unfold build
  simp
  have h_compute_m_H_time := compute_m_H_time n
  have h_build_helper_time := fun (xs : Vector α (compute_m_H n).ret.m) ↦ (build_helper_time ((compute_m_H n).ret.m) 0 xs)
  have h_m : (compute_m_H n).ret.m ≤ 2 * n + 1 := by {
    cases ((compute_m_H n).ret.proofnm) <;> omega
  }
  have h_2m : 2 * (compute_m_H n).ret.m ≤ 4 * n + 2 := by {
    rw[show 4 = 2*2 from rfl]
    rw [Nat.mul_assoc 2 2 n]
    rw [← Nat.mul_add_one 2 (2 * n)]
    rw [Nat.mul_le_mul_left_iff (by omega)]
    assumption
  }
  grw [h_compute_m_H_time, h_build_helper_time, h_2m, h_m]
  ring_nf
  rw [Nat.add_sub_assoc (by omega) 1]
  rw [← Nat.mul_sub_one n 2]
  simp
  ring_nf
  rw [Nat.Simproc.add_le_le (8 + Nat.log 2 (n - 1)) (by omega)]
  rw [Nat.add_sub_assoc (by omega) 8]
  rw [← Nat.mul_sub n 10 9]
  simp
  exact log_sublinear n
