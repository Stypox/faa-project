import Mathlib.Tactic

set_option autoImplicit false


lemma odd_log2' (i : ℕ) : Nat.log 2 (2*i + 1) = Nat.log 2 (2*i) := by
  if h_pos : 1 ≤ i then {
    rw [Nat.log_of_one_lt_of_le (by omega) (by omega)]
    rw [Nat.succ_div_of_not_dvd (by omega)]
    rw [← Nat.log_of_one_lt_of_le (by omega) (by omega)]
  } else {
    rw [show i = 0 from by omega]
    simp
  }

lemma odd_log2 (i : ℕ) : (2*i + 1).log2 = (2*i).log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact odd_log2' i

lemma log_sublinear (n : ℕ) : Nat.log 2 (n - 1) ≤ n := by
  if hn : n > 1 then {
    have a := Nat.log_lt_self 2 (x:=(n - 1)) (by omega)
    grw [a]
    simp
  } else {
    simp_all
  }

lemma succ_div_even_eq_div_even (a b: ℕ) :  (2 * a + 1) / (2 * b) = (2 * a) / (2 * b) := by
  rw [Nat.succ_div_of_not_dvd ?_]
  by_contra h_contra
  have h22b : 2 ∣ 2*b := by omega
  grw[← h22b] at h_contra
  rw [Nat.dvd_add_right (by omega)] at h_contra
  contradiction


lemma succ_div_even_eq_div_even_pow2 (j: ℕ) :  ∀ g > 0, (2 * j + 1) / 2 ^ g = (2 * j) / 2 ^ g := by
  intro g g0
  rw [← Nat.two_pow_pred_mul_two (by omega)]
  rw [Nat.mul_comm (2 ^ (g - 1)) 2]
  exact succ_div_even_eq_div_even j (2^(g-1))
