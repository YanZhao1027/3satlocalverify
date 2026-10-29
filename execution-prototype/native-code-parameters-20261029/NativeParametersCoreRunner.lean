import NativeParametersCore

def main (args : List String) : IO Unit := do
  let m := (args[0]?.bind String.toNat?).getD 1
  let B := (args[1]?.bind String.toNat?).getD 8
  let fuel := (args[2]?.bind String.toNat?).getD 150000
  IndependentNativeParameters.runCore m B fuel
