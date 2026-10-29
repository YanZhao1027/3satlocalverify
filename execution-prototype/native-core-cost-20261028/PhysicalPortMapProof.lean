import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHashParameters

/-! Constant-time primitive numeric index maps for the ORIGINAL paper's
40-register, 896-stack relocation. The closed source's `![...]` vector map
is costly to interpret in Lean at runtime; these equalities are proved in
the kernel for ALL 16 registers and ALL 44 stacks, not sampled. -/
namespace IndependentNativeCost.PhysicalPort
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Equivalent to LeafProgram.HashParameters.registers : Fin 16 -> Fin 40. -/
def register (i : Fin 16) : Nat := i.val

/-- Equivalent to LeafProgram.HashParameters.stackMap : Fin 44 -> Fin 896. -/
def stack (i : Fin 44) : Nat :=
  if i.val < 14 then 768 + i.val
  else if i.val == 14 then 785
  else if i.val == 15 then 782
  else if i.val == 16 then 786
  else i.val - 17

theorem register_exact (i : Fin 16) :
    register i = (LeafProgram.HashParameters.registers i).val := by
  rfl

theorem stack_exact (i : Fin 44) :
    stack i = (LeafProgram.HashParameters.stackMap i).val := by
  fin_cases i <;> decide

end IndependentNativeCost.PhysicalPort
