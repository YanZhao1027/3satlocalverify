import NativeCanonicalLinked

def main (args : List String) : IO Unit := do
  let fuel := (args[0]?.bind String.toNat?).getD 60000
  IndependentNativeStart.CanonicalLinked.runMonolithic fuel
