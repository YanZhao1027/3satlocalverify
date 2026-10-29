import NativeDirectTraceProof
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

/-! Kernel-checked symbolic semantics of the original *full* native preparation.
No concrete 12539-element instruction array is forced. No complete HALT
execution or universal independent-linker equivalence is asserted here. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 1500000

namespace IndependentFullPreparationDirectCertificate

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open IndependentNativeTraceProof
open IndependentNativeCost

abbrev Command := NativeLeafPreparation.command
abbrev Total : Nat := StructuredCalls.size Command + 1
def Original : Program 40 896 Total :=
  StructuredCalls.compiled Command 784 788

theorem original_full_code_table_is_source :
    ((List.finRange Total).map (fun pc => Original.code pc)).toArray =
      Array.ofFn Original.code := by
  exact sourceArray_is_ofFn Original

theorem every_finite_full_preparation_prefix_exact
    (n : Nat) (state : Cfg 40 896 Total) :
    directTableFuel Original n (copyConfig state) =
      copyConfig (sourceFuel Original n state) := by
  exact direct_table_fuel_exact Original n state

theorem every_full_preparation_step_exact
    (state : Cfg 40 896 Total) :
    (OAI.Algorithms.SubexponentialSAT.BitProgram.step Original state).map copyConfig =
      if state.pc.isSome then
        some (compactStep Original (copyConfig state))
      else none := by
  exact bitStep_exact Original state

theorem original_full_program_entry : Original.entry.val = 3 := by
  decide

end IndependentFullPreparationDirectCertificate

#print axioms IndependentFullPreparationDirectCertificate.original_full_code_table_is_source
#print axioms IndependentFullPreparationDirectCertificate.every_finite_full_preparation_prefix_exact
#print axioms IndependentFullPreparationDirectCertificate.every_full_preparation_step_exact
#print axioms IndependentFullPreparationDirectCertificate.original_full_program_entry
