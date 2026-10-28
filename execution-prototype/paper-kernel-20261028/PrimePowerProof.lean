import PrimePowerCRT
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Kernel-checked actual nilpotent-ring CRT/Hermite on a connected 3SAT. -/
theorem primepower_order1 : ((PrimePowerCRT.run 6 1).1.take 6).map ZMod.val =
    [18,22,20,0,0,0] := by decide
theorem primepower_order2 : ((PrimePowerCRT.run 3 2).1.take 6).map ZMod.val =
    [18,22,20,0,0,0] := by decide
theorem primepower_order3 : ((PrimePowerCRT.run 2 3).1.take 6).map ZMod.val =
    [18,22,20,0,0,0] := by decide

/-- Explicitly attest the scalar callback costs in the non-field Z/49 example. -/
theorem primepower_costs :
    (PrimePowerCRT.run 6 1).2 = 1997 ∧
    (PrimePowerCRT.run 3 2).2 = 965 ∧
    (PrimePowerCRT.run 2 3).2 = 731 := by decide
