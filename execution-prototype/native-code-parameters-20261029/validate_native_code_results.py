#!/usr/bin/env python3
"""Offline archive checks; not a claim of global source compiler equivalence."""
import json,pathlib
r=json.loads((pathlib.Path(__file__).resolve().parent/'native-code-assembly-results.json').read_text())
assert r['paramCore']=={'steps':9130,'staticLabels':1499,'gapDenom':1600,'sevenValues':[1,1,1,1,0,0,1]}
assert r['onePCParameters']['staticLabels']==7201 and r['onePCParameters']['steps']==19182
assert r['onePCParameters']['maxOccupiedStackBits']==252
assert r['onePCParameters']['sourceBoundaryFullStatesCompared']==5
assert r['onePCParameters']['full896StackScanEveryStep']
assert r['graphSearch']['steps']==2680 and r['graphSearch']['matchedOriginal16x48']
assert r['localSearch']['steps']==5598 and r['localSearch']['matchedOriginal16x48']
assert r['bothSearches']['coreSteps']==8278 and r['bothSearches']['allEightStageStepsWithIndividualHalts']==8870
assert r['serializer']['coreSteps']==715 and r['serializer']['rowSaved777Bits']==13
assert r['lastSelectorSuffixPrefix']['2000000StepsHalted'] is False
assert r['lastSelectorSuffixPrefix']['encodedTargetZeroBits']==5120003
assert r['lastSelectorSuffixPrefix']['zeroBitsAfter2mInstructions']==35238
for f in ('wholeOriginalNativeCodeAssemblySingleProgramVerified','fullOriginalAfterCodeExecuted',
          'fullHighQuerySATExecuted','general2oNAdvantageProved'):
 assert r[f] is False,f
print('ORIGINAL_CODE_ASSEMBLY_OFFLINE_ARCHIVE_PASS; no completed high-query SAT, no ETH speedup')
