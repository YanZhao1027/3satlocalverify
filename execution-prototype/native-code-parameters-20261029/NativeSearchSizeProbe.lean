import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

#check SparseCodeSearch.graphSearch
#check SparseCodeSearch.localSearch
#eval ("graph search (16x48) source labels", StructuredCalls.size SparseCodeSearch.graphSearch + 1)
#eval ("local search (16x48) source labels", StructuredCalls.size SparseCodeSearch.localSearch + 1)
#eval ("graph stage (40x896) source labels", StructuredCalls.size NativeCode.graphStage + 1)
#eval ("local stage (40x896) source labels", StructuredCalls.size NativeCode.localStage + 1)
#eval ("all searches original source labels", StructuredCalls.size NativeCode.searches + 1)
#eval ("native code assembly full labels", StructuredCalls.size NativeCodeAssembly.command + 1)
