import NativeSourceFastMeter

def main (args : List String) : IO Unit := do
  let size := (args[0]?.bind String.toNat?).getD 1000000
  let chunks := (args[1]?.bind String.toNat?).getD 8
  let audit := (args[2]?.bind String.toNat?).getD 8
  IndependentNativeFastMeter.run size chunks audit
