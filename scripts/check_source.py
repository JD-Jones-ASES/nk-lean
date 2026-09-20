#!/usr/bin/env python3
"""Supplementary source guard; kernel and axiom checks remain separate gates."""
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
BANNED=re.compile(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|extern|ofReduceBool|skipKernelTC|skipKernelTCCheck)\b')

def code_only(s):
    out=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\':i+=2
            elif s[i]=='"':string=False;i+=1
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':string=True;i+=1
        else:out.append(s[i]);i+=1
    if depth or string:raise ValueError('Unterminated comment/string')
    return ''.join(out)

def main():
    paths=sorted((ROOT/'NK').rglob('*.lean'))+[ROOT/'NK.lean',ROOT/'Solution.lean',ROOT/'Audit.lean']
    errors=[]
    for p in paths:
        s=code_only(p.read_text())
        if m:=BANNED.search(s):errors.append(f'{p.relative_to(ROOT)}: forbidden proof token {m[0]}')
        if re.search(r'^import\s+Challenge\b',s,re.M):errors.append(f'{p}: proof imports Challenge')
    challenge=ROOT/'Challenge.lean';s=challenge.read_text();code=code_only(s)
    if len(s.encode())>100*1024 or len(s.splitlines())>1000:errors.append('Challenge exceeds size limit')
    if re.findall(r'^import\s+(.+)$',code,re.M)!=['Mathlib']:errors.append('Challenge import policy changed')
    cfg=json.loads((ROOT/'comparator.json').read_text())
    if cfg.get('definition_names')!=[]:errors.append('No definition holes are permitted')
    if cfg.get('enable_nanoda') is not True:errors.append('NanoDa must remain enabled')
    if set(cfg['permitted_axioms'])!={'propext','Quot.sound','Classical.choice'}:errors.append('Axiom allowlist changed')
    if errors:raise SystemExit('\n'.join(errors))
    print(f'Source guard: {len(paths)} proof files; {len(cfg["theorem_names"])} compared statements; no definition holes.')
if __name__=='__main__':main()
