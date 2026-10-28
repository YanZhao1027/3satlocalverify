import CompiledTerminalEquivalence
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract

/-! Per-prefix SOURCE stack-space certificate for the actual original
NativeLeafProgram.command on a full LeafReady physical input. No high-query
algorithm is run; this is the mathematically genuine terminal branch. -/
namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- The original full program (including unused high-query code) obeys the
original BoundedEval *all-prefix per-stack* semantics, on this actual physical
empty-CNF input, under a fully concrete explicit stack bound of 204 bits per
stack and time bound 1490 source instruction steps. The measured execution
was only 106 before the compiled trailing HALT, and 4 max bits per stack. -/
theorem bounded_original_native_terminal3 :
    ∃ steps : Nat, ∃ finish : State 80 1220,
      steps ≤ 1490 ∧
      BoundedEval (NativeLeafProgram.command 2) steps
        (readyPhysicalState 3 2 2 []) finish 204 ∧
      LeafDone ([] : RawCNF 3)
        (readyPhysicalState 3 2 2 []) finish := by
  let a := readyPhysicalState 3 2 2 []
  have hframe : ∀ i : Fin 1220, (a.stacks i).length ≤ 204 := by
    intro i
    simp only [a, readyPhysicalState]
    split_ifs <;> decide
  have hclass : 101 * (a.stacks 265).length + 103 ≤ 204 := by
    decide
  have hpower : 5 * 3 + 6 ≤ 204 := by decide
  obtain ⟨steps, hs, finish, hbounded, hdone⟩ :=
    NativeLeafDispatch.command_execution
      (NativeLeafExecution.command (NativeLeafProgram.localCommand 2))
      0 204 full_ready_empty3 hframe hclass hpower
      (by
        intro _ hz _ _
        exact False.elim (hz rfl))
  refine ⟨steps, finish, ?_, hbounded, hdone⟩
  have hbody : (a.stacks 265).length = 1 := by decide
  rw [hbody] at hs
  norm_num at hs
  exact hs

end IndependentNativeExec
