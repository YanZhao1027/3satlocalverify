#!/usr/bin/env python3
"""Offline evidence-integrity checks only, not a substitute for Lean runtime QA."""
import pathlib,json
r=json.loads((pathlib.Path(__file__).resolve().parent/'native-canonical-start-results.json').read_text())
s=r['source_leaf_outer_start'];c=r['source_native_canonical_start']
assert (s['original_command_sites'],s['connected_program_labels'],s['actual_bit_instructions_including_one_halt'],s['peak_occupied_stack_data_bits'])==(3035,3036,6135,125)
assert (c['original_command_sites'],c['connected_program_labels'],c['actual_bit_instructions_including_one_halt'],c['peak_occupied_stack_data_bits'],c['final_occupied_data_bits'])==(3160,3161,7085,125,86)
assert s['full_machine_state_matches_independent_origins_at_four_boundaries'] and s['all_6135_steps_recount_all_896_stacks']
assert c['full_machine_state_matches_independent_sources_at_both_boundaries'] and c['all_7085_steps_recount_all_896_stacks']
assert r['source_canonical_stage']['staged_original_source_instructions']==951
assert r['stage_refinement']['staged_instructions_including_four_terminal_halts']==6136
assert r['high_query_counting_executed'] is False and r['end_to_end_SAT_speedup_established'] is False
assert r['original_compiler_full_3036_or_3161_label_equivalence_proved'] is False
samples=r['original_upstream_compiled_start_source_code_samples']
assert [a['label'] for a in samples]==[3,41,677,678,3025]
assert [a['status'] for a in samples]==['PASS','TIMEOUT','PASS','TIMEOUT','PASS']
print('ORIGINAL_NATIVE_CANONICAL_START_OFFLINE_PASS 7085 linked source steps; 125-bit peak; 3/5 original direct opcode probes passed, 2 timed out')
