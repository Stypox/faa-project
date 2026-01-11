import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.CoverageIntervalDefs
import Projects.Project1.SegmentTree
import Projects.Project1.FoldlHelpers

set_option autoImplicit false




-- def query_old (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) : α :=
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









--structure UpdateHelperStruct (α : Type*) [Monoid α] (m j : ℕ) where
--  a : Vector α (2*m)
--  proof (i : ℕ) (h_i0 : i > 0) (h_i_neq_j2 : ∀ g > 0, i ≠ j/(2^g)) (h_i_ub : i < m) :
--    a.get ⟨i, by omega⟩ = a.get ⟨2*i, by omega⟩ * a.get ⟨2*i+1, by omega⟩
--
--def update_old (α : Type*) (inst: Monoid α) (n : ℕ) (st : SegmentTree α n) (x : α) (p : Nat) : SegmentTree α n :=
--  let b := update_aux 1 (by omega) (by have := st.h_m0; omega) ⟨st.a, by {
--    intro i _ _ h_i_ub
--    exact st.h_children i (by omega) h_i_ub
--  }⟩
--  ⟨
--    st.m,
--    st.H,
--    b.a,
--    st.h_m0,
--    st.h_mn,
--    st.h_m2n,
--    st.h_m_pow2H,
--    by {
--      intro j h_j hjm
--      exact b.proof j (by omega) (by {
--        -- don't know why omega isn't working for something this trivial
--        intro g h_g0
--        rw [Nat.div_eq_of_lt (by {rw [Nat.one_lt_two_pow_iff]; omega})]
--        omega
--      }) hjm
--    }
--  ⟩
--
--  where update_aux (j : ℕ) (h_j0 : j > 0) (h_j : j < 2*st.m) (b : UpdateHelperStruct α st.m j) : UpdateHelperStruct α st.m j :=
--    let d := CoverageIntervalDefs.from_st n j st h_j0 h_j
--    if h_sub : p = d.L ∧ p+1 = d.R then
--      have h_leaf : st.m ≤ j := by    -- if we got to this case, j is a leaf
--        obtain ⟨h_pL, h_pR⟩ := h_sub
--        rw [h_pL] at h_pR
--        rw [st.h_m_pow2H]
--        exact d.leaf_interval_R.mpr (by omega)
--
--      ⟨
--        b.a.set j x h_j,
--        by {
--          intro i h_i0 h_i_neq_j2 h_i_ub
--          simp [Vector.set, Vector.get, Array.set, List.getElem_set]
--          split_ifs with h1 h2 h3 h3 <;> try omega
--          · specialize h_i_neq_j2 1 (by omega)
--            omega
--          · specialize h_i_neq_j2 1 (by omega)
--            omega
--          · exact b.proof i h_i0 h_i_neq_j2 h_i_ub
--        }
--      ⟩
--    else if h_empty : p < d.L ∨ p ≥ d.R then
--      b
--    else
--      have h_internal : j < 2^st.H := d.not_in_leaf p (p+1) (by grind) (by grind)
--
--      let b := update_aux (2*j) (by omega) (by rw [st.h_m_pow2H]; omega) ⟨b.a, by {
--        intro i h_i0 h_i_neq_j2 h_i_ub
--        exact b.proof i h_i0 (by {
--          intro g _
--          specialize h_i_neq_j2 (g+1) (by omega)
--          rw [Nat.pow_add_one 2 g] at h_i_neq_j2
--          rw [pow_mul_comm' 2 g] at h_i_neq_j2
--          rw [Nat.mul_div_mul_left j (2 ^ g) (by omega)] at h_i_neq_j2
--          assumption
--        }) (by omega)
--      }⟩
--      let b := update_aux (2*j + 1) (by omega) (by rw [st.h_m_pow2H]; omega) ⟨b.a, by {
--        intro i h_i0 h_i_neq_j2 h_i_ub
--        exact b.proof i (by omega) (by {
--          intro g h_g0
--          specialize h_i_neq_j2 g (by omega)
--          rw [show 2 * j / 2 ^ g = (2 * j + 1) / 2 ^ g by {
--            rcases g with _ | g <;> try contradiction
--            rw [Nat.pow_add_one']
--            rw [← Nat.div_div_eq_div_mul (2 * j + 1) 2 (2 ^ g)]
--            rw [Nat.mul_div_mul_left j (2 ^ g) (by omega)]
--            nth_rw 1 [show j = (2 * j + 1) / 2 by omega]
--          }]
--          assumption
--        }) (by omega)
--      }⟩
--      ⟨
--        b.a.set j (b.a.get ⟨2*j, by rw [st.h_m_pow2H]; omega⟩ * b.a.get ⟨2*j + 1, by rw [st.h_m_pow2H]; omega⟩) h_j,
--        by {
--          intro i h_i0 h_i_neq_j2 h_i_ub
--          simp [Vector.set, Vector.get, Array.set, List.getElem_set]
--          split_ifs with h1 h2 h3 h3 <;> try omega
--          · simp_all
--          · specialize h_i_neq_j2 1 (by omega)
--            omega
--          · specialize h_i_neq_j2 1 (by omega)
--            omega
--          · exact b.proof i h_i0 (by {
--              intro g h_g0
--              if h_g1 : g = 1 then {
--                rw [h_g1]
--                omega
--              } else {
--                specialize h_i_neq_j2 (g-1) (by omega)
--                rw [← Nat.two_pow_pred_mul_two (by omega)]
--                rw [Nat.mul_comm (2 ^ (g - 1)) 2]
--                rw [← Nat.div_div_eq_div_mul (2 * j + 1) 2 (2 ^ (g - 1))]
--                rw [show (2 * j + 1) / 2 = j by omega]
--                assumption
--              }
--            }) h_i_ub
--        }
--      ⟩




-- EXAMPLES
