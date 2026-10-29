import NativeGraphSearchPhysical

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 150000
  IndependentNativeParameters.Graph.runGraph fuel
