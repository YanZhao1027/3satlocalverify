import MeasureHashArithmetic

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 50000
  IndependentNativeCost.runArithmetic fuel
