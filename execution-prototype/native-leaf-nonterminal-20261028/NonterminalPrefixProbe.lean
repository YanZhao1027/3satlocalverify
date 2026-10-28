import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram
import ReadyTerminalTrace

namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
open OAI.Algorithms.SubexponentialSAT.BitProgram

set_option maxRecDepth 18000
set_option maxHeartbeats 1300000

/-- The actual source clause: positive variable zero in ambient dimension 3. -/
def F : RawCNF 3 := [[⟨0, true⟩]]

def physical := IndependentNativeExec.readyPhysicalState 3 2 2
  (NativeTerminal.clauseRecords F)

/-- Faithfully uses the actual original nonterminal classifier and original
    leaf-state loader. The yet-unexecuted high-query suffix is STOPPED after
    loading, never counted as computed. -/
def commonPrefix : StructuredCalls.Cmd 80 1220 :=
  .seq NativeTerminal.readyCommand
    (.ite 0 (.base .skip)
      (.ite 7 (.seq Native.loadLeaf (.base .skip)) (.base .skip)))

def program := StructuredCalls.compiled commonPrefix 265 263

#eval NativeTerminal.clauseRecords F
#eval (NativeTerminal.clauseRecords F).length
#eval (physical.stacks 265).length
#eval StructuredCalls.size Native.loadLeaf
#eval StructuredCalls.size commonPrefix
#eval program.entry.val

end IndependentNonterminal
