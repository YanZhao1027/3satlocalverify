#!/usr/bin/env python3
"""Parse only actual Lean #eval reports from TerminalBatch.lean; fail closed.
We intentionally do NOT benchmark the original noncomputable nonterminal leaf,
the TM2 interpreter, or the primitive tape-machine step in this script.
"""
from __future__ import annotations
import ast,json,pathlib,re,sys

root=pathlib.Path(__file__).resolve().parent
source=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else root/'terminal-batch.log'
raw=source.read_text()
text_lists=re.findall(r'\[(?:"[^"\n]*"(?:,\s*\n?\s*"[^"\n]*")*)\]',raw,re.S)
assert len(text_lists)==2,f'Expected precisely 2 Lean lists, got {len(text_lists)}'
lines=[]
for literal in text_lists:
    strings=ast.literal_eval(literal)
    assert isinstance(strings,list)
    lines.extend(strings)
columns=['n','kind','halted','source_instructions_including_halt','set','copy','bnot','band','bor','bxor','branch','push','pop','peek','goto','halt','initial_stack_bits','peak_stack_bits','peak_single_stack_bits','final_stack_bits','output_count']
assert len(lines)==12,len(lines)
records=[]
for row in lines:
    cols=row.split(',')
    assert len(cols)==len(columns),(row,len(cols))
    data={k:(v if k=='kind' else v=='true' if k=='halted' else int(v)) for k,v in zip(columns,cols)}
    n=data['n'];kind=data['kind'];assert kind in ('empty_formula','empty_clause')
    assert data['halted'] is True
    assert data['output_count']==(2**n if kind=='empty_formula' else 0),data
    assert sum(data[k] for k in ('set','copy','bnot','band','bor','bxor','branch','push','pop','peek','goto','halt')) == data['source_instructions_including_halt']
    assert data['halt']==1
    assert data['peak_stack_bits']>=data['initial_stack_bits']
    assert data['peak_stack_bits']>=data['final_stack_bits']
    assert data['peak_stack_bits'] <= data['initial_stack_bits']+data['source_instructions_including_halt']
    if kind=='empty_formula':
        assert data['source_instructions_including_halt']==74+11*n
        # original NativeTerminal.readyCommand_eval, 2 guards, 1 compiled halt
        upper=100*(1+1)+11*n+31+2+1
    else:
        assert data['source_instructions_including_halt']==132
        # original encoded [[false]] body has length=5; one guard and final halt
        upper=100*(5+1)+11*n+31+1+1
    assert data['source_instructions_including_halt'] <= upper
    data['source_terminal_proof_bound_including_halt']=upper
    data['observed_source_eval_steps']=data['source_instructions_including_halt']-1
    records.append(data)
assert [r['n'] for r in records if r['kind']=='empty_formula']==[0,1,2,3,5,8,16,32]
assert [r['n'] for r in records if r['kind']=='empty_clause']==[0,3,8,16]
result={'source_lean_file':'TerminalBatch.lean','source_output_file':source.name,
    'program':'StructuredCalls.compiled (NativeLeafDispatch.command (.base .skip)) 265 263',
    'relationship':'Lean proves same source-Eval length/final state for original noncomputable NativeLeafProgram.command on terminal inputs; NOT execution of nonterminal code',
    'count_basis':'source BitProgram.execInstr variants, one per source step incl final HALT',
    'space_basis':'BitProgram.dataBits total occupied stack bits, plus longest individual stack at any prefix; static control and primitive tape cells excluded',
    'same_source_steps_as_TM2':'formally proved via original BitProgram.tm_step and tm_trace',
    'primitive_microstep_count':'NOT MEASURED; original primitiveOverhead*sourceSteps is a symbolic certified bound',
    'cases':records,'all_checks_passed':True}
out=root/'terminal-batch-results.json';out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print('SUCCESS_VALIDATED_ROWS',len(records));print('RESULTS',out)
for x in records:
 print(x['kind'],x['n'],'source_steps',x['source_instructions_including_halt'],'peak_stackbits',x['peak_stack_bits'],'peak_single',x['peak_single_stack_bits'],'count',x['output_count'],'source_time_upper',x['source_terminal_proof_bound_including_halt'])
