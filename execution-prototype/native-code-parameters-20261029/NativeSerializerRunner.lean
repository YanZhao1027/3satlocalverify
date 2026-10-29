import NativeSerializerPhysical

def main (args : List String) : IO Unit := do
  let fuel := (args.head?.bind String.toNat?).getD 180000
  let _ ← IndependentNativeParameters.Serializer.runSerializer fuel
  pure ()
