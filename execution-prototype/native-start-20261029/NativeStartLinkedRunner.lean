import NativeStartLinked

def main (args : List String) : IO Unit := do
  let fuel := (args[0]?.bind String.toNat?).getD 40000
  IndependentNativeStart.Linked.runLinked fuel
