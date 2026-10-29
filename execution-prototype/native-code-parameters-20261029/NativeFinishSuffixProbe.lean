import NativeSerializerPhysical
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

/-! Run a BOUNDED real source bit-prefix of the original final `afterCode`
selector initialization, after the genuine 40x896 physical CNF/parameters/
TWO searches/row serializer. This stage can require millions of operations
because it explicitly constructs a zero candidate of depth x modulus width.
Fuel is a hard resource cap. Halt false is recorded, not a SAT failure/proof.
-/
namespace IndependentNativeParameters.Finish
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeParameters.Physical

set_option maxRecDepth 23000

def originalSuffix := NativeLeafPreparation.afterCode

def run (fuel : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let prep ← IndependentNativeParameters.Serializer.runSerializer 180000
  IO.println s!"FINISH_REAL_INPUT row777Bits={(prep.words[777]!).length} modulus={(BinaryArithmetic.toNat (prep.words[780]!))} digitWidth={(prep.words[780]!).length} distanceDepth={BinaryArithmetic.toNat (prep.words[817]!)} physicalStackBits={bits prep}"
  (← IO.getStdout).flush
  let cmd := originalSuffix
  let table := IndependentNonterminal.FastLinearize.instructionArray cmd
  let entry : Fin (StructuredCalls.size cmd+1) := Fin.ofNat _
    (IndependentNonterminal.Linearize.callEntry cmd 1 0)
  IO.println s!"FINISH_ORIGINAL_CODE labels={table.size} sourceEntries={StructuredCalls.size cmd} entry={entry.val} fuel={fuel}"
  (← IO.getStdout).flush
  let began ← IO.monoMsNow
  let (out,stat) := runInstrumented table (inject prep entry) fuel
  let ended ← IO.monoMsNow
  let physical := bank out
  IO.println s!"FINISH_ORIGINAL_PREFIX halted={out.pc.isNone} executedSourceSteps={stat.executed} currentOriginalPC={out.pc.map Fin.val} peakOccupiedStackBits={stat.peakTotalBits} longestStackBits={stat.peakSingleBits} visitedLabels={stat.visitedDistinctLabels} zeroCandidate778Bits={(out.words[778]!).length} zeroCandidateDepthWord={(out.words[817]!).length} sourceRow777Unchanged={out.words[777]! == prep.words[777]!} finalOccupiedBits={bits physical} sourceInstructionMs={ended-began} totalInternalMs={ended-start}"
  (← IO.getStdout).flush
  unless stat.executed <= fuel && out.words[777]! == prep.words[777]! do
    throw <| IO.userError "Original finish source instrumentation inconsistent"

end IndependentNativeParameters.Finish
