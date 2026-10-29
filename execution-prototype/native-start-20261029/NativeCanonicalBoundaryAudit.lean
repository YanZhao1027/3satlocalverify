import NativeCanonicalLinked

/-! Exhaustive source-versus-single-PC physical-state audit: at the first
complete `start` -> `saveCanonical` transition and final global HALT, compare
ALL original 40 registers and ALL 896 stacks. Independently scan ALL 896
stacks at EVERY one of the 7085 source bit instructions for peak occupancy.
This supports exact empirical code runtime but not full source compiler
extensional equality for every possible program state. -/
namespace IndependentNativeStart.CanonicalAudit
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open IndependentNativeCost
open IndependentNativeStart
open IndependentNativeStart.Linked
open IndependentNativeStart.CanonicalLinked

private def used (a : Array (List Bool)) : Nat :=
  a.foldl (fun acc w => acc+w.length) 0
private def longest (a : Array (List Bool)) : Nat :=
  a.foldl (fun acc w => max acc w.length) 0

def audit : IO Unit := do
  let t0 ← IO.monoMsNow
  let (startFinish,startStats) := runInstrumented linked
    (copyConfig (loadedLocalInput.withPC (some (Fin.ofNat Total clEntry)))) 60000
  let (canonicalFinish,saveStats) := runInstrumented sourceSave
    (startCfg (takeFrame startFinish) (Fin.ofNat Additional additionalEntry)) 60000
  unless startFinish.pc.isNone && canonicalFinish.pc.isNone &&
      startStats.executed == 6135 && saveStats.executed == 951 do
    throw <| IO.userError "Independent original start/saveCanonical source stages failed"
  let table := monolithic
  let init := copyConfig (loadedLocalInput.withPC (some (Fin.ofNat Full clEntry)))
  let mut c := init
  let mut peak := used c.words
  let mut long := longest c.words
  let mut step := 0
  let mut boundaries := 0
  for _ in [:10000] do
    let some pc := c.pc | break
    let some op := table[pc.val]? | throw <| IO.userError "Unknown opcode label"
    c := runOne op c
    step := step + 1
    peak := max peak (used c.words)
    long := max long (longest c.words)
    if step == 6134 then
      let ok := c.pc == some (Fin.ofNat Full (afterStartBase+additionalEntry)) &&
        c.registers == startFinish.registers && c.words == startFinish.words
      IO.println s!"CANONICAL_SOURCE_BOUNDARY startToSave atStep={step} exact40Regs896StacksAndPC={ok} dataBits={used c.words}"
      unless ok do throw <| IO.userError "Native original start/saveCanonical physical boundary differs"
      boundaries := boundaries + 1
    if step == 7085 then
      let ok := c.pc.isNone && c.registers == canonicalFinish.registers &&
        c.words == canonicalFinish.words
      IO.println s!"CANONICAL_SOURCE_BOUNDARY finalHalt atStep={step} exact40Regs896StacksAndPC={ok} dataBits={used c.words}"
      unless ok do throw <| IO.userError "Native canonical final state diverges from source"
      boundaries := boundaries + 1
  let (fast,stat) := runInstrumented table init 10000
  let ok := c.pc.isNone && step==7085 && boundaries==2 &&
    c.registers == fast.registers && c.words == fast.words &&
    c.pc == fast.pc && stat.executed == step &&
    peak==stat.peakTotalBits && long==stat.peakSingleBits &&
    stat.finalTotalBits==used c.words && peak==125 &&
    BinaryArithmetic.toNat (c.words[780]!)==3 &&
    BinaryArithmetic.toNat (c.words[817]!)==1280000
  IO.println s!"CANONICAL_MONOLITHIC_PER_STEP_AUDIT success={ok} allSteps={step} checkpoints={boundaries} peakDataBits={peak} longestSingleStack={long} finalDataBits={used c.words} originalSourceProgramPositions={table.size} auditMs={(← IO.monoMsNow)-t0}"
  unless ok do throw <| IO.userError "Native canonical monolithic trace audit failed"

end IndependentNativeStart.CanonicalAudit

def main : IO Unit := IndependentNativeStart.CanonicalAudit.audit
