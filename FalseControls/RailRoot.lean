import WTK.Field
-- Deliberately false: the nontrivial limiting roots multiply to 1, not 2.
example : (17 + 12 * Real.sqrt 2) * (17 - 12 * Real.sqrt 2) = 2 := by
  rw [WTK.Field.rail_roots_product]
  norm_num
