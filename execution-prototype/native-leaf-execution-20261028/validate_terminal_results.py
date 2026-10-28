#!/usr/bin/env python3
"""Offline consistency checks for the committed Lean-measured table.
Does NOT substitute for actual Lean execution or kernel proof checking.
"""
import json,pathlib
p=pathlib.Path(__file__).resolve().parent/'terminal-batch-results.json'
d=json.loads(p.read_text());a=d['cases'];assert len(a)==12
assert len([r for r in a if r['kind']=='empty_formula'])==8
assert len([r for r in a if r['kind']=='empty_clause'])==4
for r in a:
 n=r['n'];s=r['source_instructions_including_halt'];kind=r['kind']
 assert r['halted'] and r['halt']==1
 assert r['output_count']==(2**n if kind=='empty_formula' else 0)
 assert s==(74+11*n if kind=='empty_formula' else 132)
 assert s<=r['source_terminal_proof_bound_including_halt']
 assert s==sum(r[k] for k in ['set','copy','bnot','band','bor','bxor','branch','push','pop','peek','goto','halt'])
 assert r['initial_stack_bits']<=r['peak_stack_bits']
 assert r['final_stack_bits']<=r['peak_stack_bits']
 assert r['peak_stack_bits']<=r['initial_stack_bits']+s
 assert r['observed_source_eval_steps']==s-1
print('TERMINAL_RESULTS_VALID',len(a),'rows')
