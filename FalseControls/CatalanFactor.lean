import WTK.Catalan
-- Deliberately false: the cancellation gives 450 (G, 1), not 45 (G, 1).
example : WTK.Catalan.A *ᵥ WTK.Catalan.v 1 0 = ![45, 45] := by
  rw [WTK.Catalan.A_v]
  norm_num
