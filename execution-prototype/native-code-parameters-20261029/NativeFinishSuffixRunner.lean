import NativeFinishSuffixProbe

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 100000
  IndependentNativeParameters.Finish.run fuel
