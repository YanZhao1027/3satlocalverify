#!/usr/bin/env python3
"""Fail-closed measured-source-data builder. Never infers #SAT or ETH claims."""
import json,pathlib,re,sys
root=pathlib.Path(__file__).resolve().parent
logs=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else root

def read(s):
 p=logs/s; assert p.is_file(),p
 return p.read_text()

def field(s,p):
 rows=[v for v in read(s).splitlines() if v.startswith(p)]
 assert len(rows)==1,(s,p,rows)
 d={}
 for item in rows[0].split()[1:]:
  if '=' not in item:continue
  k,v=item.split('=',1)
  d[k]=v=='true' if v in ('true','false') else int(v) if re.fullmatch('[0-9]+',v) else v
 return d

core=field('core-run-1-8.log','ORIGINAL_PARAMETERS_CORE_RESULT ')
para=field('physical-run.log','PHYSICAL_PARAMS_FIVE_STAGES_PASS ')
linked=field('linked-run.log','PARAM_MONOLITHIC_RUN ')
linkedCode=field('linked-run.log','PARAM_MONOLITHIC_CODE ')
audit=field('parameter-boundary-audit.log','PARAMETER_FULL_TRACE_AUDIT ')
search=field('two-search-run.log','TWO_SEARCH_BOTH_COMPLETE ')
row=field('serializer-run.log','SERIALIZER_REAL_ROW_CORE ')
ser=field('serializer-run.log','SERIALIZER_FOUR_ORIGINAL_STAGES_PASS ')
finite=field('finish-prefix-120k.log','FINISH_ORIGINAL_PREFIX ')
chunk=field('finish-chunk-trial.log','CHUNKED_ORIGINAL_FINISH_RESULT ')
graph=field('graph-run.log','GRAPH_ORIGINAL_SEARCH_RESULT ')
check=[
 (core['halted'] and core['steps']==9130 and core['gapDenom']==1600 and core['allMetadataCorrect']),
 (para['sourceStepsIncludingFiveHalts']==19184 and para['peakStackBits']==252),
 (linkedCode['actualLabels']==7201 and linkedCode['originalParametersSites']==4040),
 (linked['halted'] and linked['steps']==19182 and linked['peakStackBits']==252 and linked['original14MetadataCorrect']),
 (audit['success'] and audit['full40x896BoundariesPassed']==5 and audit['sourceBitInstructions']==19182),
 (search['bothCandidatesPersisted'] and search['bothSourceSearchSteps']==8278 and search['allEightSubstagesStepsIncludingHalts']==8870),
 (graph['halted'] and graph['executedSteps']==2680),
 (row['halted'] and row['executedSteps']==715 and row['outputRowBits']==13 and row['original16x64StateEqualsPhysical']),
 (ser['sourceBitInstructionsWithIndividualHalts']==3374),
 (not finite['halted'] and finite['executedSourceSteps']==120000 and finite['zeroCandidate778Bits']==2110),
 (not chunk['halted'] and chunk['actualInstructions']==2000000 and chunk['zeroWordLen']==35238 and chunk['theoreticalZeroWordLen']==5120003 and chunk['peakDataBits']==35368),
]
assert all(check),check
bounds=[v for v in read('parameter-boundary-audit.log').splitlines() if v.startswith('PARAMETER_MONOLITHIC_BOUNDARY ')]
assert len(bounds)==5 and all('physical40x896FullStateEqual=true' in x for x in bounds)
for v in ['TWO_SEARCH_SOURCE_MAPPING_AUDIT name=graph_search all16RegistersAnd48StacksEqual=true','TWO_SEARCH_SOURCE_MAPPING_AUDIT name=local_search all16RegistersAnd48StacksEqual=true']:
 assert v in read('two-search-run.log')
result={
 'date':'2026-10-29','originalMathCommit':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',
 'input':'real 3-variable nonempty 1-clause CNF; n=3, B=8, m=1 computed by original ClauseCount',
 'paramCore':{'steps':9130,'staticLabels':1499,'gapDenom':1600,'sevenValues':[1,1,1,1,0,0,1]},
 'physicalParametersFiveStages':{'stepsWithFiveHalts':19184,'maxOccupiedStackBits':252},
 'onePCParameters':{'staticLabels':7201,'steps':19182,'maxOccupiedStackBits':252,'sourceBoundaryFullStatesCompared':5,'full896StackScanEveryStep':True},
 'graphSearch':{'steps':2680,'staticLabels':928,'matchedOriginal16x48':True},
 'localSearch':{'steps':5598,'staticLabels':668,'matchedOriginal16x48':True},
 'bothSearches':{'coreSteps':8278,'allEightStageStepsWithIndividualHalts':8870,'graphMatrixSaved816Bits':0,'localMatrixSaved815Bits':5},
 'serializer':{'coreSteps':715,'staticLabels':739,'rowSaved777Bits':13,'allFourStageStepsWithIndividualHalts':3374,'local16x64Matched':True},
 'lastSelectorSuffixPrefix':{'sourceLabels':119,'120000StepsHalted':False,'2000000StepsHalted':False,'zeroBitsAfter2mInstructions':35238,'encodedTargetZeroBits':5120003,'occupiedDataPeakAt2mSteps':35368},
 'wholeOriginalNativeCodeAssemblySingleProgramVerified':False,'fullOriginalAfterCodeExecuted':False,
 'fullHighQuerySATExecuted':False,'general2oNAdvantageProved':False,
 'limitations':['source-derived staged programs and independent 7201-label parameters link; no full original assembly compiler equality theorem',
 'search examples have graph dimension r=0 and only one local row',
 'suffix was only run for two million actual instructions, without halting',
 'source occupied data bits exclude physical tape representation and code storage',
 'no executable general subexponential SAT solver or ETH advantage established']}
(root/'native-code-assembly-results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print('ORIGINAL_SOURCE_CODE_PARAMETERS_BOTH_SEARCHES_SERIALIZER_PASS; suffix bounded and uncompleted')
