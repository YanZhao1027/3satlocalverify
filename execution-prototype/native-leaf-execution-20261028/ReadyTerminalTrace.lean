import TerminalTrace
import OriginalTerminalTraceProof
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

/-! The same tested terminal commands with physical persistent headers
restored, so they satisfy the real LeafReady predicate on explicit examples. -/
namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
open OAI.Algorithms.SubexponentialSAT.BitProgram

/-- Ambient and occurrence words are little-endian. Unlike the earlier
minimal test state, every named persistent field of DFSVisit.LeafReady is
present in these source inputs. -/
def readyPhysicalState (n k M : Nat) (records : List (List Bool)) :
    StructuredCalls.State 80 1220 :=
  ⟨fun _ => false, fun i =>
    if i = (258 : Fin 1220) then Encoding.encodeNat n
    else if i = 259 then M.bits
    else if i = 264 then (4 * M ^ (k - 1)).bits
    else if i = 265 then Encoding.encodeList id records
    else if i = 267 then n.bits
    else []⟩

def readyCfg (n k M : Nat) (records : List (List Bool)) :
    Cfg 80 1220 (StructuredCalls.size terminalCmd + 1) :=
  (readyPhysicalState n k M records).withPC (some terminalProg.entry)

/-- Executed via exact original instruction executor, not the mathematical
count function. Compile and check the physical result for n=3. -/
def readyEmptyTrial (n : Nat) : Record :=
  snapshot n "empty_formula" (observeFuel 1000 (readyCfg n 2 2 []))

def readyEmptyClauseTrial (n : Nat) : Record :=
  snapshot n "empty_clause" (observeFuel 1000 (readyCfg n 2 2 [[false]]))

#eval readyEmptyTrial 0
#eval readyEmptyTrial 3
#eval readyEmptyTrial 5
#eval readyEmptyClauseTrial 3

/-- The complete physical state meets every field in the actual OpenAI
LeafReady predicate for the empty-CNF test input. -/
theorem full_ready_empty3 :
    DFSVisit.LeafReady 2 ((2:Nat).bits) 10
      ([] : DisjointReuse.RawCNF 3)
      (readyPhysicalState 3 2 2 []) := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro i hi
    have h258 : i ≠ (258 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h259 : i ≠ (259 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h264 : i ≠ (264 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h265 : i ≠ (265 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    have h267 : i ≠ (267 : Fin 1220) := by
      intro he; have := congrArg Fin.val he; omega
    simp [readyPhysicalState, h258, h259, h264, h265, h267]

end IndependentNativeExec
