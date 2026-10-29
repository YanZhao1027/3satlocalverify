import NativeDirectTraceProof
import NativeFinishOriginalDirect

/-!
Formal specialization of the generic direct-source finite-fuel execution
theorem to the actual OpenAI upstream NativeLeafPreparation.afterCode command.
This is a universal equality about the certified directTableFuel engine.
It does not claim that the older statistics-recording runInstrumented routine
has yet been proved to implement directTableFuel.
-/

namespace IndependentNativeAfterCodeCertificate

open OAI.Algorithms.SubexponentialSAT.BitProgram
open IndependentNativeCost
open IndependentNativeTraceProof

abbrev Original := NativeFinishOriginalDirect.source
abbrev Total := NativeFinishOriginalDirect.Total

/-- All static labels are copied from the original compiler, without an
independent linker or synthesizing an alternative algorithm. -/
theorem original_array_exact :
    NativeFinishOriginalDirect.originalCode = Array.ofFn Original.code := by
  exact sourceArray_is_ofFn Original

/-- For all n and every legal physical 40-reg/896-stack source configuration,
the interpreter reading the upstream source table follows the same n-step
configuration as the upstream BitProgram primitive source semantics. -/
theorem afterCode_direct_fuel_exact (n : Nat) (c : Cfg 40 896 Total) :
    directTableFuel Original n (copyConfig c) =
      copyConfig (sourceFuel Original n c) := by
  exact direct_table_fuel_exact Original n c

theorem afterCode_one_step_exact (c : Cfg 40 896 Total) :
    (OAI.Algorithms.SubexponentialSAT.BitProgram.step Original c).map copyConfig =
      if c.pc.isSome then
        some (compactStep Original (copyConfig c))
      else none := by
  exact bitStep_exact Original c

end IndependentNativeAfterCodeCertificate

#print axioms IndependentNativeAfterCodeCertificate.original_array_exact
#print axioms IndependentNativeAfterCodeCertificate.afterCode_direct_fuel_exact
#print axioms IndependentNativeAfterCodeCertificate.afterCode_one_step_exact
