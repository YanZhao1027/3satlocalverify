import MeasureHashArithmetic

/-! Actual original hash arithmetic on several independent scalar metadata
inputs. All expected values are computed only AFTER the bit-program has run;
no formula count or numeric result is loaded into the input banks. -/
namespace IndependentNativeCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 19000

def metadataInput (n m B : Nat) : StructuredCalls.State 8 22 :=
  SubexpBlockParameterProgram.state (fun _ => false)
    (HashParametersProgram.inputWords n.bits m.bits B.bits)

def runCase (table : Array (Instr 8 22 (StructuredCalls.size realArithmeticCommand + 1)))
    (entry : Fin (StructuredCalls.size realArithmeticCommand + 1))
    (n m B fuel : Nat) : IO Unit := do
  let initial := copyConfig ((metadataInput n m B).withPC (some entry))
  let t0 ← IO.monoMsNow
  let (out,counts) := runInstrumented table initial fuel
  let t1 ← IO.monoMsNow
  let gotAlphabet := BinaryArithmetic.toNat (out.words[14]!)
  let gotDepth := BinaryArithmetic.toNat (out.words[9]!)
  let gotLoops := BinaryArithmetic.toNat (out.words[13]!)
  let expectedAlphabet := 3*m
  let expectedDepth := SparseCode.distanceDenom m B
  let expectedLoops := HashSelect.loopCap n m
  let allOK := counts.executed == counts.set+counts.copy+counts.bitLogic+counts.tests+counts.push+counts.pop+counts.peek+counts.goto+counts.halt &&
    counts.finalTotalBits == out.words.foldl (fun sum w => sum+w.length) 0 &&
    (if out.pc.isNone then gotAlphabet == expectedAlphabet && gotDepth == expectedDepth && gotLoops == expectedLoops else true)
  IO.println s!"HASH_CASE n={n} m={m} B={B} halted={out.pc.isNone} steps={counts.executed} peakBits={counts.peakTotalBits} peakSingleBits={counts.peakSingleBits} initialBits={counts.initialBits} finalBits={counts.finalTotalBits} distinctPC={counts.visitedDistinctLabels} returnedAlphabet={gotAlphabet} returnedDepth={gotDepth} returnedLoops={gotLoops} expectedAlphabet={expectedAlphabet} expectedDepth={expectedDepth} expectedLoops={expectedLoops} instruction_ms={t1-t0} consistent={allOK}"
  unless allOK do throw <| IO.userError "Inconsistent machine bit count or arithmetic answer"

end IndependentNativeCost
