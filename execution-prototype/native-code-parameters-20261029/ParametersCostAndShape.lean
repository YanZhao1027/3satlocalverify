import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramParameters

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram

#check CodeParametersProgram.program
#check CodeParametersProgram.fullCommand
#check parameters
#eval ("fullCommand static", StructuredCalls.size CodeParametersProgram.fullCommand)
#eval ("original parameters static", StructuredCalls.size parameters)
#eval ("parameters budget m1 B8", CodeParametersProgram.fullBudget 1 8 1 4)
#eval ("gapDenom", SparseCode.gapDenom 1 8)
#eval ("original register index ports", ((regs8 (0 : Fin 8)).val, (regs8 (7 : Fin 8)).val))
#eval ("original stack index ports", ((stacks77 (0 : Fin 77)).val, (stacks77 (76 : Fin 77)).val))
#eval (List.finRange 7).map (CodeParametersProgram.parameterValues 1 8)
