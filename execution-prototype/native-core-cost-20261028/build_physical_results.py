#!/usr/bin/env python3
"""Fail-closed archive builder for ORIGINAL Lean 40x896 physical SAT-leaf prep.
Reads real source/lockstep/proof logs. This is not a complete SAT solver.
"""
from pathlib import Path
import hashlib,json,re,sys
root=Path(__file__).resolve().parent
logs=Path(sys.argv[1]) if len(sys.argv)>1 else root

def read(name):
 p=logs/name
 assert p.is_file(),f'Missing experiment evidence {p}'
 return p.read_text()

def one(text,pre):
 lines=[x for x in text.splitlines() if x.startswith(pre)]
 assert len(lines)==1,(pre,len(lines),lines[-5:])
 return lines[0]

def kv(text):
 result={}
 for token in text.split(' ')[1:]:
  if '=' not in token:continue
  key,v=token.split('=',1)
  result[key]=True if v=='true' else False if v=='false' else int(v) if re.fullmatch('[0-9]+',v) else v
 return result

src=read('physical-numeric-verified.log')
clause=kv(one(src,'REAL_PHYSICAL_NUMERIC_CLAUSE '))
table=kv(one(src,'ORIGINAL_NUMERIC_ABI_SOURCE_TABLE '))
core=kv(one(src,'REAL_PHYSICAL_NUMERIC_HASH '))
out=kv(one(src,'REAL_PHYSICAL_NUMERIC_OUTPUT '))
audit=kv(one(src,'REAL_PHYSICAL_NUMERIC_AUDIT '))
assert 'REAL_PHYSICAL_NUMERIC_EVERY_STEP_SPACE_CHECK equal=true' in src
assert (clause['halted'],clause['steps'],clause['count'],clause['peakDataBits'])==(True,180,1,40)
assert table['size']==637 and table['expected']==637
assert (core['halted'],core['stepsABI'],core['stepsWithOuterHalt'],core['peakTotalStackBits'],core['peakSingleStackBits'],core['initialDataBits'],core['finalDataBits'],core['recountedFinalBits'],core['sourceLabelsVisited'])==(True,3585,3586,125,22,24,51,51,616),core
assert (out['m'],out['alpha'],out['distanceDenom'],out['loopCap'],out['n'],out['B'])==(1,3,1280000,10,3,8)
assert audit['ABI_steps']==3585 and audit['ABI_original_state_match'] is True and audit['unmapped40x896_frame_preserved'] is True and audit['raw_total_steps']==3766
lock=kv(one(read('physical-lockstep-audit.log'),'PHYSICAL_LOCKSTEP_AUDIT '))
assert (lock['everyStepMatched'],lock['steps'],lock['sourceLabels'],lock['physicalRegs'],lock['physicalStacks'],lock['occupiedStackPeak'],lock['maxSingleStack'],lock['output3m'],lock['outputDenom'],lock['outputLoopCap'])==(True,3585,637,40,896,125,22,3,1280000,10),lock
axioms=read('physical-axioms.log')
assert 'does not depend on any axioms' in axioms
matches=re.findall(r'depends on axioms: \[(.*?)\]',axioms,re.S)
assert len(matches)==2,matches
allowed={'propext','Classical.choice','Quot.sound'}
for x in matches:
 assert {s.strip() for s in x.split(',') if s.strip()}<=allowed

auditSrc=read('fast-abi-audit.log')
assert 'FAST_LINEARIZER_ABI_STATIC_OPCODES_637_MATCH=true' in auditSrc
assert 'FAST_LINEARIZER_ABI_FULL_STATE_3585_EQUAL=true' in auditSrc
export=(root/'physical-original-opcodes.txt').read_text()
lines=export.splitlines()
assert lines[-1]=='COMPLETE|original-lean-opcodes-and-physical-state',lines[-8:]
ops=[line for line in lines if line.startswith('OP|')]
assert len(ops)==637
assert [int(x.split('|')[1]) for x in ops]==list(range(637))
assert ops[0]=='OP|0|halt'
regs=[x for x in lines if x.startswith('RMAP|')]
stacks=[x for x in lines if x.startswith('SMAP|')]
assert len(regs)==16 and len(stacks)==44
assert [int(x.split('|')[1]) for x in regs]==list(range(16))
assert [int(x.split('|')[1]) for x in stacks]==list(range(44))
assert [int(x.split('|')[2]) for x in regs]==list(range(16))
expectedStack=[768+i for i in range(14)]+[785,782,786]+list(range(27))
assert [int(x.split('|')[2]) for x in stacks]==expectedStack
assert len(set(expectedStack))==44
assert 'TABLE|637|1' in lines
assert any(x.startswith('META|original-clauseCount-then-original-ABI|n3-m1-B8') for x in lines)
expectedArgs={'halt':0,'goto':1,'set':3,'copy':3,'bnot':3,'band':4,'bor':4,'bxor':4,'branch':3,'push':3,'peek':4,'pop':4}
for ln in ops:
 _,label,kind,*args=ln.split('|')
 assert kind in expectedArgs and len(args)==expectedArgs[kind],ln
 assert all(v.isdecimal() for v in args),ln
 assert all(int(a)<=636 for a in args),ln
result={
 'date':'2026-10-29',
 'source':'OpenAI/math pinned commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (Lean 4.34.1)',
 'status':'original physical 40x896 hash preparation (lifted ABI) run PASSED; full high-query SAT solver NOT run',
 'inputs':'real nonempty 3-variable one-clause CNF x0, actual original clause counter output m=1; n=3 B=8',
 'machine_model':'source-level Boolean instructions, 40 registers, 896 stacks, original ports by kernel-proven formula',
 'source_opcode_table':'physical-original-opcodes.txt',
 'source_opcode_sha256':hashlib.sha256(export.encode()).hexdigest(),
 'abi_static_opcode_count':637,
 'abi_direct_original_bit_program_full_trace_check':True,
 'physical_port_mapping_proven_for_all_16_registers_and_44_stacks':True,
 'physical_numeric_opcode_general_refinement_theorem_checked':True,
 'kernel_axioms_only':sorted(allowed),
 'stages':{
  'original_clause_count':{'steps_including_halt':180,'peak_occupied_stack_bits':40,'output_m':1},
  'physical_hash_abi':{'source_steps_including_halt':3585,'outer_call_final_halt_budget':1,'peak_occupied_stack_bits':125,'peak_one_stack_bits':22,'initial_occupied_bits':24,'final_occupied_bits':51,'visited_labels':616,
    'observed_instruction_ms':core['instruction_ms'],'output_3m':3,'distance_denom':1280000,'loop_cap':10},
  'reported_separately_staged_instruction_total':3766,
 },
 'all_3585_executed_steps_full_state_agree':True,
 'all_3585_step_stack_store_full_896_stack_recount_agrees':True,
 'all_40_registers_896_stacks_unmapped_frame_preserved':True,
 'limitations':[
  'This is the actual hash-parameter preparation ABI mapped to the full leaf bank, not NativeLeafPreparation.command or the complete SAT solver.',
  'The two stages are executed as independently compiled and re-initialized source programs; 3766 is a staged total, not a monolithic original start trace.',
  'The extra one instruction for caller HALT is wrapper accounting, not a directly executed monolithic 40x896 program trace.',
  'Peak occupied virtual stack data bits are not a physical Turing tape-space bound, and Lean/host wall times are not source-bit time.',
  'No asymptotic or empirical subexponential #SAT runtime advantage is established.'
 ]
}
p=root/'native-physical-40x896-results.json';p.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print('FULL_PHYSICAL_SOURCE_RESULTS_PASS 637 source opcodes 3585 lockstep states 896-stack-every-step 125-bit peak')
print('OUTPUT',p)
