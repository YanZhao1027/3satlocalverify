#!/usr/bin/env python3
"""Build a fail-closed archive from REAL Ubuntu Lean execution logs.
The source program computes its outputs; this script cannot make a failed
or timed-out execution pass. Kernel proofs and source bit executor audits
are checked separately by the accompanying shell runner.
"""
import json,pathlib,re,sys
R=pathlib.Path(__file__).resolve().parent
logs=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else R

def read(name):
 p=logs/name
 assert p.is_file(),f'Missing real execution log {p}'
 return p.read_text()

def exact_line(text,prefix):
 rows=[s for s in text.splitlines() if s.startswith(prefix)]
 assert len(rows)==1,(prefix,rows)
 return rows[0]

def fields(line):
 parts=line.split()[1:]
 return {k:(v=='true' if v in ('true','false') else int(v) if re.fullmatch(r'\d+',v) else v) for k,v in (p.split('=',1) for p in parts if '=' in p)}

clause=read('measure-clause.log')
setup=fields(exact_line(clause,'STAGE_SETUP name=clauseCount'))
cr=fields(exact_line(clause,'STAGE_RESULT name=clauseCount'))
cn=fields(exact_line(clause,'STAGE_REGISTERS name=clauseCount'))
assert setup['codeSize']==40 and setup['initialBits']==23 and cr['halted'] is True
assert cr['steps']==180 and cr['peakStackBits']==40 and cr['peakSingle']==17
assert cn['countPort782']==1 and cn['input785']==3 and cn['input786']==8
assert 'ORIGINAL_CLAUSE_CODE_40_INSTRUCTIONS_AND_180_STEPS_FULL_STATE_EQUAL true' in read('clause-count-audit.log')

sizes=read('start-component-sizes.log')
for s in ['ORIGINAL_CLAUSE_COUNT_SITES 39','ORIGINAL_PREPARE_HASH_SITES 2985','ORIGINAL_SAVE_WIDTH_SITES 11','ORIGINAL_START_SITES 3035']:
 assert s in sizes,s

v=read('hash-arith-variants.log')
assert 'HASH_VARIANTS_SETUP staticSites=426 entry=1 fuel=100000' in v
rows=[fields(x) for x in v.splitlines() if x.startswith('HASH_CASE ')]
expect=[(3,1,2,2324,79,18,3,80000,10),(3,1,4,2665,90,20,3,320000,10),
        (3,1,8,3006,101,22,3,1280000,10),(3,2,8,3405,113,24,6,5120000,12),
        (3,3,8,3460,113,24,9,5120000,12),(8,5,8,3778,121,25,15,11520000,24)]
assert len(rows)==len(expect),(len(rows),len(expect))
for d,e in zip(rows,expect):
 actual=tuple(d[k] for k in ('n','m','B','steps','peakBits','peakSingleBits','returnedAlphabet','returnedDepth','returnedLoops'))
 assert actual==e,(actual,e)
 assert d['halted'] is True and d['consistent'] is True,d
 for x,y in [('returnedAlphabet','expectedAlphabet'),('returnedDepth','expectedDepth'),('returnedLoops','expectedLoops')]:
  assert d[x]==d[y],d
 assert d['steps']<100000 and d['peakSingleBits']<=d['peakBits']

op=read('hash-arith-original-fulltrace.log')
assert 'ORIGINAL_HASH_OPCODE_AUDIT checked=426 tableSize=426 mismatches=0' in op
assert 'ORIGINAL_HASH_STEP_AUDIT firstSteps=3006 fullStateEqual=true' in op
source=read('hash-arith-space-audit.log')
checks=[fields(s) for s in source.splitlines() if s.startswith('HASH_PREFIX_PHYSICAL_AUDIT ')]
assert len(checks)==6 and all(x['equal'] is True for x in checks)
assert [(x['n'],x['m'],x['B']) for x in checks]==[(x[0],x[1],x[2]) for x in expect]

axioms=read('hash-arith-axioms.log')
found=re.findall(r'depends on axioms: \[(.*?)\]',axioms,re.S)
allowed={'propext','Classical.choice','Quot.sound'}
assert len(found)==2,found
for f in found:
 a={s.strip() for s in f.split(',') if s.strip()}
 assert a<=allowed,a


# The next, physically wired ORIGINAL 16-register/44-stack ABI command.
abi_text=read('measure-hash-abi.log')
abi_pre=fields(exact_line(abi_text,'ABI_PREPARE '))
abi_table=fields(exact_line(abi_text,'ABI_TABLE '))
abi_run=fields(exact_line(abi_text,'ABI_RUNTIME '))
abi_out=fields(exact_line(abi_text,'ABI_OUTPUT '))
assert abi_pre['staticSites']==636 and abi_pre['n']==3 and abi_pre['m']==1 and abi_pre['B']==8
assert abi_table['size']==637 and abi_table['entry']==1
assert abi_run['halted'] is True and abi_run['steps']==3585 and abi_run['peakStackBits']==108
assert abi_run['peakSingleBits']==22 and abi_run['finalBits']==abi_run['recheckedFinalBits']==34
assert abi_run['distinctSites']==616 and abi_run['halts']==1
assert (abi_out['alpha'],abi_out['depthDenom'],abi_out['rounds'])==(3,1280000,10)
assert (abi_out['inputN'],abi_out['inputM'],abi_out['inputB'])==(3,1,8)
assert sum(abi_run[k] for k in ['sets','copies','logic','branches','pushes','pops','peeks','gotos','halts'])==abi_run['steps']
original_abi_log=read('abi-original-fulltrace.log')
assert 'HASH_ABI_ORIGINAL_OPCODE checked=637 mismatches=0' in original_abi_log
assert 'HASH_ABI_ORIGINAL_TRACE steps=3585 fullMachineStateEqual=true' in original_abi_log
abi={'program':'HashParametersProgram.ABI.command (original, 16 regs, 44 stacks)',
  'input':{'n':3,'m':1,'B':8},
  'static_sites':abi_pre['staticSites'],
  'static_labels_including_halt':abi_table['size'],
  'source_instructions_including_halt':abi_run['steps'],
  'peak_total_stack_data_bits':abi_run['peakStackBits'],
  'peak_single_stack_bits':abi_run['peakSingleBits'],
  'final_stack_data_bits':abi_run['finalBits'],
  'real_output':{'alphabet':abi_out['alpha'],'distance_denom':abi_out['depthDenom'],'rounds':abi_out['rounds']},
  'original_source_opcode_check':{'checked':637,'mismatches':0},
  'original_source_full_trace_replay':{'steps':3585,'all_pc_registers_stacks_equal':True},
  'vm_materialize_ms_approx':abi_table['build_ms'],
  'vm_execute_ms_approx':abi_run['run_ms'],
  'measured_but_not_40x896_direct_execution':True}

result={
 'as_of':'2026-10-28',
 'source_repository':'OpenAI/math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',
 'lean':'4.34.1',
 'status':'SUCCESS: original finite arithmetic and clause counting; full native SAT leaf NOT executed',
 'source_program':'OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.command',
 'what_executed':'Original 8-register 22-stack Boolean arithmetic (n,m,B -> 3m,distance denominator,round cap), plus actual clause-count stage on a one-clause CNF',
 'what_did_not_execute':'Entire NativeLeafSetup.start, HighQueryProgram, reconstruction, complete #SAT solving, TM2 physical tape operations',
 'original_start_static_sites':3035,
 'authentic_hash_abi_16x44':abi,
 'original_start_materialization':'Timed out at 62 seconds in Lean interpreter experiment: no start execution count',
 'attempted_full_40x896_physical_stage':'Timed out at 66 seconds before benchmark output; not a completed source program run',
 'original_hash_opcode_slots':426,
 'original_hash_opcode_full_check':{'checked':426,'mismatches':0},
 'original_vs_array_full_step_state_check':{'steps':3006,'pc_registers_all_stacks_equal':True},
 'original_clause_stage':{'source_bit_instructions_including_halt':180,
      'source_opcode_slots':40,'initial_stack_data_bits':23,'peak_total_data_bits':40,
      'peak_single_stack_bits':17,'output_clause_count':1,
      'all_40_opcode_and_180_step_state_equal':True},
 'hash_cases':rows,
 'all_six_every_prefix_stack_space_recounts_passed':True,
 'formal_arithmetic_source_eval_upper_bound_n3_m1_B8':6400000000,
 'measured_3006_includes_final_halt':True,
 'lean_formal_axioms':sorted(allowed),
 'machine_time_note':'instruction_ms is IO.monoMsNow within compiled Lean evaluator, coarse millisecond values; process wall includes Lean startup, mathlib imports; not physical Turing-machine bit-time',
 'memory_note':'peakBits counts occupied data bits in 22 virtual Boolean stacks, not Linux RSS or peak tape cells',
 'not_a_SAT_speedup':True,
 }
output=R/'native-core-cost-results.json'
output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print('NATIVE_CORE_COST_EVIDENCE_VALIDATED',len(rows),'independent cases; 426/426 opcodes; all 3006 exact original steps; 637/637 ABI opcodes and 3585 source steps; 6/6 peak-space audits')
print('RESULT_FILE',output)
