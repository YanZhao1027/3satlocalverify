import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

/-! Read-only size check for the NEXT ORIGINAL stage; it is NOT execution.
Full linked code may have much higher materialization/evaluation overhead. -/

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

#eval ("original_native_leaf_preparation_static_sites",
  StructuredCalls.size NativeLeafPreparation.command)
