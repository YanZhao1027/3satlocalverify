import NativeParametersMonolithic

/-! Independent comparison of SINGLE-PC `canonicalStart; parameters` link
against five separately compiled ORIGINAL OAI source components. At each
logical handoff, compare ALL 40 register bits and ALL 896 stacks and the
expected next program counter. Recount ALL 896 stacks at EVERY source
instruction to independently verify peak data bits; fail on discrepancy.

This is a strong finite experiment, not a universal compiler theorem.
-/
namespace IndependentNativeParameters.PhysicalAudit
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeStart
open IndependentNativeStart.CanonicalLinked
open IndependentNativeParameters
open IndependentNativeParameters.Physical
open IndependentNativeParameters.Monolithic

set_option maxRecDepth 23000

private def countBits (a : Array (List Bool)) : Nat :=
  a.foldl (fun acc w => acc+w.length) 0
private def maxStack (a : Array (List Bool)) : Nat :=
  a.foldl (fun acc w => max acc w.length) 0

def run : IO Unit := do
  let started ← IO.monoMsNow
  let (c0,s0) := runInstrumented codeCanonical
    (copyConfig (loadedLocalInput.withPC (some (Fin.ofNat CanonicalSource 3)))) 50000
  let inE : Fin InSource := Fin.ofNat _ inputEntry
  let (c1,s1) := runInstrumented codeInputs (inject (bank c0) inE) 50000
  let coreE : Fin CoreSource := Fin.ofNat _ coreEntry
  let coreMapped := codeCore.map
    (fun op => ProgramLinking.relocateInstr regs8 stacks77 id none op)
  let (c2,s2) := runInstrumented coreMapped (inject (bank c1) coreE) 50000
  let outE : Fin OutSource := Fin.ofNat _ outputEntry
  let (c3,s3) := runInstrumented codeOutputs (inject (bank c2) outE) 50000
  let clearE : Fin ClearSource := Fin.ofNat _ cleanupEntry
  let (c4,s4) := runInstrumented codeCleanup (inject (bank c3) clearE) 50000
  unless c0.pc.isNone && c1.pc.isNone && c2.pc.isNone &&
      c3.pc.isNone && c4.pc.isNone &&
      s0.executed==7085 && s1.executed==55 && s2.executed==9130 &&
      s3.executed==278 && s4.executed==2636 do
        throw <| IO.userError "Independent original 5-stage source replay failed"
  let originalStates := #[bank c0,bank c1,bank c2,bank c3,bank c4]
  let boundaries : Array (Nat × Nat × String) :=
    #[(7084,bInputs+inputEntry,"canonical_to_inputs"),
      (7138,bCore+coreEntry,"inputs_to_core"),
      (16268,bOutputs+outputEntry,"core_to_outputs"),
      (16545,bCleanup+cleanupEntry,"outputs_to_cleanup"),
      (19182,0,"final_halt")]
  let table := code
  let mut c := copyConfig (loadedLocalInput.withPC (some (Fin.ofNat Total 3)))
  let mut totalMax := countBits c.words
  let mut longestMax := maxStack c.words
  let mut passed := 0
  let mut executed := 0
  for _ in [:25000] do
    let some pc := c.pc | break
    let some op := table[pc.val]? | throw <| IO.userError "Source-linked invalid program counter"
    c := runOne op c
    executed := executed+1
    totalMax := max totalMax (countBits c.words)
    longestMax := max longestMax (maxStack c.words)
    if let some k := (boundaries.toList.findIdx? (fun p => p.1==executed)) then
      let (step,target,name) := boundaries[k]!
      let some reference := originalStates[k]? | throw (IO.userError "Missing source phase reference")
      let sameData := c.registers == reference.regs && c.words == reference.words
      let samePC := if k==4 then c.pc.isNone
        else c.pc == some (Fin.ofNat Total target)
      IO.println s!"PARAMETER_MONOLITHIC_BOUNDARY name={name} steps={step} physical40x896FullStateEqual={sameData && samePC} occupiedBits={countBits c.words}"
      (← IO.getStdout).flush
      unless sameData && samePC do
        throw <| IO.userError s!"Source program handoff mismatch at {name}, instruction {executed}"
      passed := passed+1
  let (fast,st) := runInstrumented table
    (copyConfig (loadedLocalInput.withPC (some (Fin.ofNat Total 3)))) 25000
  let ok := c.pc.isNone && executed==19182 && passed==5 &&
    c.pc==fast.pc && c.registers==fast.registers && c.words==fast.words &&
    totalMax==st.peakTotalBits && longestMax==st.peakSingleBits &&
    st.executed==executed && st.finalTotalBits==countBits c.words &&
    totalMax==252 && metadataCorrect 1 8 (bank c)
  IO.println s!"PARAMETER_FULL_TRACE_AUDIT success={ok} sourceBitInstructions={executed} full40x896BoundariesPassed={passed} all896StacksRecountedEveryStep={ok} verifiedPeakOccupiedBits={totalMax} longestStack={longestMax} finalOccupiedBits={countBits c.words} auditMs={(← IO.monoMsNow)-started}"
  (← IO.getStdout).flush
  unless ok do throw <| IO.userError "Failed source-program full-state or 19K-step peak space verification"

end IndependentNativeParameters.PhysicalAudit

def main : IO Unit := IndependentNativeParameters.PhysicalAudit.run
