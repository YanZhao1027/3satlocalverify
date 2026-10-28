import MeasureHashABI

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 20000
  IndependentNativeCost.measureABI fuel
