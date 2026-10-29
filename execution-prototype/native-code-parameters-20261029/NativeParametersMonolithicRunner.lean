import NativeParametersMonolithic

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 40000
  IndependentNativeParameters.Monolithic.run fuel
