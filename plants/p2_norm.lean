-- PLANT (must fail): |xy| = |x||y|, the division-algebra habit
theorem plant_norm {α : Type} [Lean.Grind.CommRing α] (x y : B3 α) :
    B3.norm2 (B3.mul x y) = B3.norm2 x * B3.norm2 y := by
  cases x; cases y; simp only [B3.mul, B3.norm2]; grind
