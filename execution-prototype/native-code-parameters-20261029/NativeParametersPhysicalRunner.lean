import NativeParametersPhysical

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 50000
  let _ ← IndependentNativeParameters.Physical.runFive fuel
  pure ()
