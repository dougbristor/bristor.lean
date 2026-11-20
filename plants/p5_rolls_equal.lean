-- PLANT (must fail): the two rolls are the same product WITHOUT the reversal
theorem plant_rolls {α : Type} [Lean.Grind.CommRing α] (x y : B3 α) : B3.jmul x y = B3.mul x y := by
  cases x; cases y; simp only [B3.jmul, B3.mul, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
