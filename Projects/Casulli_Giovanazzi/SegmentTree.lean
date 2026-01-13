import Mathlib.Tactic

set_option autoImplicit false


structure SegmentTree (α : Type*) [Monoid α] (n : ℕ) where
  m : ℕ
  H : ℕ
  -- TODO maybe store original vector
  a : Vector α (2*m)

  -- assumptions that must hold for any SegmentTree
  h_m0 : m > 0
  h_mn : m ≥ n
  h_m2n : m = 1 ∨ m < n * 2 - 1
  h_m_pow2H : m = 2^H
  h_children (j : ℕ) (h0j : 0 < j) (hjm: j < m) :
    (a.get ⟨j, by omega⟩) = (a.get ⟨2*j, by omega⟩) * (a.get ⟨2*j+1, by omega⟩)
