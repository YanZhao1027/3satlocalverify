#!/usr/bin/env python3
"""Offline CI data-integrity checks only. Full Lean QA must run on Ubuntu."""
from pathlib import Path
import json
r=json.loads((Path(__file__).resolve().parent/'native-core-cost-results.json').read_text())
assert r['not_a_SAT_speedup'] is True
assert r['original_hash_opcode_full_check']=={'checked':426,'mismatches':0}
assert r['original_vs_array_full_step_state_check']=={'steps':3006,'pc_registers_all_stacks_equal':True}
assert r['original_clause_stage']['source_bit_instructions_including_halt']==180
assert r['original_clause_stage']['peak_total_data_bits']==40
assert len(r['hash_cases'])==6 and r['all_six_every_prefix_stack_space_recounts_passed']
exp=[(3,1,2,2324,79),(3,1,4,2665,90),(3,1,8,3006,101),(3,2,8,3405,113),(3,3,8,3460,113),(8,5,8,3778,121)]
for d,(n,m,B,steps,peak) in zip(r['hash_cases'],exp):
 assert (d['n'],d['m'],d['B'],d['steps'],d['peakBits'])==(n,m,B,steps,peak)
 assert d['halted'] and d['consistent']
 for a,b in [('returnedAlphabet','expectedAlphabet'),('returnedDepth','expectedDepth'),('returnedLoops','expectedLoops')]:
  assert d[a]==d[b]
assert set(r['lean_formal_axioms'])=={'propext','Classical.choice','Quot.sound'}
a=r['authentic_hash_abi_16x44']
assert a['static_sites']==636 and a['static_labels_including_halt']==637
assert a['source_instructions_including_halt']==3585
assert a['peak_total_stack_data_bits']==108 and a['peak_single_stack_bits']==22
assert a['original_source_opcode_check']=={'checked':637,'mismatches':0}
assert a['original_source_full_trace_replay']=={'steps':3585,'all_pc_registers_stacks_equal':True}
assert a['real_output']=={'alphabet':3,'distance_denom':1280000,'rounds':10}
assert a['measured_but_not_40x896_direct_execution'] is True
assert 'Timed out' in r['attempted_full_40x896_physical_stage']
assert 'Timed out' in r['original_start_materialization']
assert r['original_start_static_sites']==3035
print('NATIVE_CORE_COST_OFFLINE_VALIDATION_PASS 6/6 cases; 426/426 raw arithmetic and 637/637 physical ABI opcodes; no full SAT solver')
