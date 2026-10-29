#!/usr/bin/env python3
"""Offline archive integrity only, NOT a substitute for full Lean proof QA."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
p=root/'native-physical-40x896-results.json';a=json.loads(p.read_text())
source=(root/a['source_opcode_table']).read_bytes()
assert hashlib.sha256(source).hexdigest()==a['source_opcode_sha256']
ops=[x for x in source.decode().splitlines() if x.startswith('OP|')]
assert len(ops)==637 and ops[0]=='OP|0|halt'
assert a['abi_static_opcode_count']==637
assert a['physical_port_mapping_proven_for_all_16_registers_and_44_stacks'] is True
assert a['physical_numeric_opcode_general_refinement_theorem_checked'] is True
assert a['all_3585_executed_steps_full_state_agree'] is True
assert a['all_3585_step_stack_store_full_896_stack_recount_agrees'] is True
assert set(a['kernel_axioms_only'])=={'propext','Classical.choice','Quot.sound'}
c=a['stages']['physical_hash_abi']
assert c['source_steps_including_halt']==3585 and c['peak_occupied_stack_bits']==125 and c['output_3m']==3
assert a['stages']['reported_separately_staged_instruction_total']==3766
assert len(a['limitations'])>=5 and 'NOT run' in a['status']
print('PHYSICAL_40X896_OFFLINE_ARCHIVE_PASS 637/637 original source opcode positions; 3585-step lockstep; 125-bit peak; SAT solver not executed')
