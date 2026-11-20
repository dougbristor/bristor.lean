-- PLANT (must fail): a sorry. Lean only WARNS on sorry and exits 0; check.sh must still refuse it.
theorem plant_sorry {α : Type} [Lean.Grind.CommRing α] (x y z : B3 α) :
    B3.mul (B3.mul x y) z = B3.mul x (B3.mul y z) := by sorry
