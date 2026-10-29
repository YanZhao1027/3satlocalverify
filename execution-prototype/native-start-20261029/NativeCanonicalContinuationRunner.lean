import NativeCanonicalContinuation

def main (args : List String) : IO Unit := do
  let fuel := (args[0]?.bind String.toNat?).getD 90000
  IndependentNativeStart.Canonical.runCanonical fuel
