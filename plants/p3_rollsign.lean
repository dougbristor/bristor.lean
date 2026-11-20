-- PLANT (must fail): the legacy (j-roll) commutator sign stated against the canon product
theorem plant_rollsign : B3.sub (B3.mul (B3.e 1) (B3.e 2)) (B3.mul (B3.e 2) (B3.e 1)) =
    B3.smul (-1) (B3.add (B3.e 1) (B3.e 2)) := by decide
