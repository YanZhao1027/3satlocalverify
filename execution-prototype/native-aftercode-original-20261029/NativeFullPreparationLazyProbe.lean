import NativeFullPreparationDirectCertificate

/-! Runtime fetch of a few ORIGINAL 12539-label source program instructions.
This intentionally never materializes the entire instruction array.
No claim that this is an exhaustive global linker audit or that the full
command has run to HALT. -/

open IndependentFullPreparationDirectCertificate
open OAI.Algorithms.SubexponentialSAT.BitProgram

def main : IO Unit := do
  let begin ← IO.monoMsNow
  let p := Original
  let labels := Total
  IO.println s!"FULL_NATIVE_SOURCE_LABELS={labels} entry={p.entry.val}"
  (← IO.getStdout).flush
  unless labels == 12539 && p.entry.val == 3 do
    throw <| IO.userError "Unexpected original full preparation size or entry"
  for i in [0,3,4,5,3160,3161,9000,12421,12538] do
    let t ← IO.monoMsNow
    let pc : Fin Total := Fin.ofNat _ i
    let opcode := p.code pc
    let category : String := match opcode with
      | .halt => "halt"
      | .goto _ => "goto"
      | .branch _ _ _ => "branch"
      | _ => "other"
    IO.println s!"FULL_NATIVE_LAZY_SOURCE_OPCODE index={i} category={category} fetchMs={(← IO.monoMsNow)-t} elapsedMs={(← IO.monoMsNow)-begin}"
    (← IO.getStdout).flush
  IO.println "FULL_NATIVE_LAZY_SAMPLE_PASS originalSourceLabels=12539 entry=3 sites=9 noWholeTable=true"
