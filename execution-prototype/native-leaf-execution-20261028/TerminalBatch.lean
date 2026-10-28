import ReadyTerminalTrace
open IndependentNativeExec

/-- Machine-readable row fields are listed in the accompanying parser.
The observer uses only original BitProgram.execInstr for each instruction. -/
def csvRow (r : Record) : String :=
  String.intercalate "," [
    toString r.dimension, r.kind, toString r.halted,
    toString r.instructions, toString r.sets, toString r.copies,
    toString r.nots, toString r.ands, toString r.ors, toString r.xors,
    toString r.tests, toString r.pushes, toString r.pops,
    toString r.peeks, toString r.gotos, toString r.halts,
    toString r.initialStackBits, toString r.peakStackBits,
    toString r.peakSingleStackBits, toString r.finalStackBits,
    toString r.resultCount ]

#eval ([0,1,2,3,5,8,16,32] : List Nat).map (fun n => csvRow (readyEmptyTrial n))
#eval ([0,3,8,16] : List Nat).map (fun n => csvRow (readyEmptyClauseTrial n))
