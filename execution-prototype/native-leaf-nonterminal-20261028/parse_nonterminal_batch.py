#!/usr/bin/env python3
"""Fail-closed parser for actual Lean #eval outputs of four original-prefix cases.
SAT.count in each case is an INDEPENDENT oracle, not the prefix output.
"""
import json,pathlib,re,sys
root=pathlib.Path(__file__).resolve().parent
source=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else root/'nonterminal-batch.log'
text=source.read_text()
rows=re.findall(r'^"(case=[^"\n]+)"$',text,re.M)
assert len(rows)==4,f'Expected 4 separate Lean outputs, got {len(rows)}; tail={text[-400:]!r}'
expected={
 'unit_positive':{'clauses':1,'oracleCount':4,'sourceSteps':3166,'peakTotalBits':52,'peakSingleStackBits':17},
 'two_units':{'clauses':2,'oracleCount':2,'sourceSteps':3552,'peakTotalBits':92,'peakSingleStackBits':37},
 'contradiction':{'clauses':2,'oracleCount':0,'sourceSteps':3408,'peakTotalBits':76,'peakSingleStackBits':29},
 'two_binary_clauses':{'clauses':2,'oracleCount':4,'sourceSteps':4272,'peakTotalBits':172,'peakSingleStackBits':77},
}
records=[]
for s in rows:
    pairs=s.split(';')
    d=dict(x.split('=',1) for x in pairs)
    for k,v in list(d.items()):
        if k in ('halted','guard0','guard7','copied'):d[k]=v=='true'
        elif k!='case':d[k]=int(v)
    case=d.get('case');assert case in expected,(case,d)
    assert len(d)==11,d
    assert all(d[k]==v for k,v in expected[case].items()),d
    assert d['halted'] and not d['guard0'] and d['guard7'] and d['copied'],d
    assert d['codeLookups']==2836 and d['peakSingleStackBits']<=d['peakTotalBits'],d
    records.append(d)
assert [r['case'] for r in records]==list(expected)
result={
 'date':'2026-10-28',
 'source':'NonterminalBatch.lean run against pinned OpenAI/math + Lean 4.34.1',
 'experiment':'Actual original NativeTerminal.readyCommand and Native.loadLeaf, compiled through new linear source layout with high-query suffix explicitly NOT executed',
 'original_program':'commonPrefix = .seq NativeTerminal.readyCommand (.ite 0 skip (.ite 7 (Native.loadLeaf ; skip) skip))',
 'executed_high_query':False,
 'full_original_NativeLeafProgram_command_executed':False,
 'independently_proven_original_prefix_trace_for_positive_unit':True,
 'original_vs_compact_entire_state_matched_first_100_steps':True,
 'original_vs_flat_first_60_labels_matched':True,
 'full_2856_label_diff':'TIMEOUT at 420 sec; not proven; cannot claim equivalence of arbitrary instructions',
 'source_instruction_measure':'Real BitProgram.Instr variants on independently linearized prefix; includes final halt',
 'space_measure':'Maximum occupied data bits among all 1220 stacks, separately maximum single stack width; no primitive-machine tape allocation',
 'oracle_measure':'Separate Lean SAT.count on same small input, NOT a result of the executed prefix',
 'cases':records,
 'all_four_prefixes_halted_and_loaded':True,
 'limitation':'Not the full SAT solver; no paper algorithm speed advantage established'
}
out=root/'nonterminal-prefix-results.json';out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(f'NONTERMINAL_PREFIX_SAT_INPUT_CASES={len(records)} PASS; archive={out.name}')
for x in records:print(x['case'],x['sourceSteps'],x['peakTotalBits'],x['peakSingleStackBits'],x['oracleCount'])
