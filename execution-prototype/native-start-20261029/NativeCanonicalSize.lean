import NativeStartLinked
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafStartup

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

#eval ("actual_original_saveCanonical_sites", StructuredCalls.size NativeLeafSetup.saveCanonical)
#eval ("actual_original_canonicalStart_sites", StructuredCalls.size NativeLeafSetup.canonicalStart)
#eval ("actual_original_initializer_sites", StructuredCalls.size HashGreedyProgram.Initialize.command)
#eval ("actual_original_canonicalRowWidth_sites", StructuredCalls.size NativeLeaf.canonicalRowWidth)
