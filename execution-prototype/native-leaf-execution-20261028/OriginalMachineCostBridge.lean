import CompiledTerminalEquivalence
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

/-! Trace-preserving connection from the full original leaf's terminal path
to the original source BitProgram step count, original TM2 instruction blocks,
original primitive block compiler bound, and the exact source stackBits
resource definition. This does NOT execute the noncomputable primitive tape
machine; the multiplier is symbolic as in the upstream theorem. -/

namespace IndependentNativeExec
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.BitProgram

/-- On the actually LeafReady 3-variable empty-CNF state, one actual original
BitProgram trace length `steps` induces the same number of TM2 block steps;
the original primitive simulator has an upstream-certified upper bound
`primitiveOverhead * steps`, and the final active source data bits are
bounded by initial data bits + steps. This is NOT the measured primitive
microstep count or peak tape visitation. -/
theorem full_native_terminal_TM2_primitive_and_dataBits :
    ∃ steps : Nat, ∃ b : StructuredCalls.State 80 1220,
      let p := NativeLeafProgram.program 2
      let initial := (readyPhysicalState 3 2 2 []).withPC (some p.entry)
      let final : BitProgram.Cfg 80 1220 (StructuredCalls.size (NativeLeafProgram.command 2) + 1) := b.withPC none
      BitProgram.Trace p steps initial final ∧
      Computation.Trace (BitProgram.tm p).step steps
        (BitProgram.tmCfg p initial) (BitProgram.tmCfg p final) ∧
      Computation.RunsIn (BitProgram.primitive p).step
        (BitProgram.primitiveOverhead p * steps)
        (BitProgram.primitiveCfg p initial) (BitProgram.primitiveCfg p final) ∧
      BitProgram.dataBits final ≤ BitProgram.dataBits initial + steps ∧
      b.stacks 263 = countWord 8 := by
  obtain ⟨t, b, hsource, _, hcount⟩ := full_native_and_proxy_same_trace_empty3
  let p := NativeLeafProgram.program 2
  let initial := (readyPhysicalState 3 2 2 []).withPC (some p.entry)
  let final : BitProgram.Cfg 80 1220 (StructuredCalls.size (NativeLeafProgram.command 2) + 1) := b.withPC none
  have ht : BitProgram.Trace p (t+1) initial final := hsource
  refine ⟨t+1, b, ?_, ?_, ?_, ?_, hcount⟩
  · exact ht
  · exact BitProgram.tm_trace p ht
  · exact BitProgram.primitive_execution p ⟨t+1, le_rfl, ht⟩
  · exact BitProgram.trace_dataBits p ht

end IndependentNativeExec
