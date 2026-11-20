-- PLANT (must fail): associativity, the quaternion habit
theorem plant_assoc {α : Type} [Lean.Grind.CommRing α] (x y z : B3 α) :
    B3.mul (B3.mul x y) z = B3.mul x (B3.mul y z) := by
  cases x; cases y; cases z; simp only [B3.mul, B3.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
