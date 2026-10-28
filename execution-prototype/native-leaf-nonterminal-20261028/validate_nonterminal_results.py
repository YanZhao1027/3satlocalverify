#!/usr/bin/env python3
"""Independent offline sanity checks on committed real Lean source outputs.
This does not replace source compiler equivalence or kernel proof checking.
"""
from pathlib import Path
import json
p=Path(__file__).resolve().parent/'nonterminal-prefix-results.json'
d=json.loads(p.read_text());rows=d['cases']
assert len(rows)==4
expect={'unit_positive':(3166,52,17,4),'two_units':(3552,92,37,2),'contradiction':(3408,76,29,0),'two_binary_clauses':(4272,172,77,4)}
assert [x['case'] for x in rows]==list(expect)
for x in rows:
 assert (x['sourceSteps'],x['peakTotalBits'],x['peakSingleStackBits'],x['oracleCount'])==expect[x['case']]
 assert x['halted'] and x['copied'] and not x['guard0'] and x['guard7']
 assert x['codeLookups']==2836 and x['peakSingleStackBits']<=x['peakTotalBits']
assert d['executed_high_query'] is False
assert d['full_original_NativeLeafProgram_command_executed'] is False
assert d['all_four_prefixes_halted_and_loaded'] is True
assert 'TIMEOUT' in d['full_2856_label_diff']
print('NONTERMINAL_PREFIX_RESULTS_OFFLINE_CHECK PASS 4/4')
