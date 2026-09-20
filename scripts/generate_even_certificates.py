#!/usr/bin/env python3
"""Regenerate exact finite input; every generated certificate is kernel checked.

This Python recurrence is a convenience, not part of the proof boundary.
NK.RationalPowerBounds and NK.RationalMomentCertificate prove soundness.
"""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
S=10**24

def ceildiv(a,b):return (a+b-1)//b
def add(x,y):return x[0]+y[0],x[1]+y[1]
def scale(x,a,b):return x[0]*a//b,ceildiv(x[1]*a,b)
def pad(x,a,b):return x[0],x[1]+ceildiv(a*S,b)
def logbounds(a,b):
    x,y=a-b,a+b
    term=(x*S//y,ceildiv(x*S,y));total=(0,0)
    for n in range(40):
        total=add(total,scale(term,1,2*n+1))
        term=scale(term,x*x,y*y)
    return pad(scale(total,2,1),1,10**38)
def logpos(a,b,s):return add(scale(logbounds(2,1),s,1),logbounds(a,b*2**s))
def expbounds(a,b):
    term=(S,S);total=(0,0)
    for n in range(31):
        total=add(total,term)
        term=scale(term,a,b*(n+1))
    return pad(total,1,10**60)
def expos(a,b,m):
    x=expbounds(a,b*2**m)
    for _ in range(m):x=x[0]*x[0]//S,ceildiv(x[1]*x[1],S)
    return x
def powerdata(a,b,fn,fd,unit=False):
    assert a>=b>0 and fd>0
    s=0
    while b*2**(s+1)<=a:s+=1
    v=scale(logpos(a,b,s),fn,fd)
    m=0
    while 8*v[1]>S*2**m:m+=1
    r=expos(v[0],S,m)[0],expos(v[1],S,m)[1]
    if unit:
        assert r[0]>0
        r=S*S//r[1],ceildiv(S*S,r[0])
    return s,m,*r

def lean(c):return '⟨'+', '.join(map(str,c))+'⟩'
def frac(a,b):return f'({a} / {b} : ℝ)'

def main():
    data=json.loads((ROOT/'certificates/even.json').read_text())
    lines=['import NK.Certificates.EvenGeometry','import NK.RationalMomentCertificate','',
      '/-! Exact numerical moments for the P0177 seeds. Generated certificate',
      'input is proved by ordinary kernel reduction; no native evaluator is trusted. -/',
      'set_option maxRecDepth 32768','set_option maxHeartbeats 0',
      'namespace NK.Certificates','open RationalMomentCertificate','']
    apps=['import NK.Certificates.EvenMoments','import NK.ClosureProducts','','/-! Unconditional every-N numerical applications of the full interval criterion. -/',
      'namespace NK.Certificates','']
    for case in data['cases']:
        k=case['k'];an=case['alpha_numerator'];ad=case['alpha_denominator'];alpha=frac(an,ad)
        names=[]
        for b in case['blocks']:
            m=b['m'];name=f'k{k}_m{m}';names.append(name)
            B=b['base'];mult=b['multiplicity'];D=b['denominator'];fn=b['f_numerator'];fd=b['f_denominator'];f=frac(fn,fd)
            top=powerdata(B,1,an,ad)
            ws={w:powerdata(D,w,fn,fd,True) for w in sorted(set(b['widths']))}
            assert top[3] <= mult*sum(ws[w][2] for w in b['widths'])
            lines+=[f'def {name}_power : ℕ → PowerData']
            for w,c in ws.items():lines+=[f'  | {w} => {lean(c)}']
            lines+=['  | _ => ⟨0, 0, 0, 0⟩','',
              f'theorem {name}_moment : ({B}:ℝ)^{alpha} ≤ ({mult}:ℝ) *',
              f'    ∑ x∈{name}.support, (({name}.width x:ℝ)/{name}.denominator)^{f} := by',
              f'  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound {name} {S} {B} {mult} {an} {ad} {fn} {fd}',
              f'    {lean(top)} (fun x => {name}_power ({name}.width x))',
              '    (by decide) (by decide) (by decide) (by decide))','']
            apps += [f'theorem {name}_closure : perfectPowerClosure {k} {m} = {B} := by']
            if m==51:
                apps += [f'  have h := perfectPowerClosure_mul {k} 3 17 (by decide) (by decide) (by decide) (by decide)',
                  '  norm_num [perfectPowerClosure, perfectPowerRoot] at h', '  exact h', '']
            else:
                p=next(i for i in range(2,m+1) if m%i==0);e=0;r=m
                while r%p==0:e+=1;r//=p
                assert r==1
                apps += [f'  have h := perfectPowerClosure_prime_pow {k} {p} {e} (by decide) (by decide)',
                  '  norm_num at h', '  exact h', '']
            apps+=[f'noncomputable def {name}_component : MomentComponent {k} {alpha} :=',
              f'  {name}.toComponent {k} {m} {alpha} {f}',
              f'    (by decide) (by decide) {name}_valid (by norm_num) (by',
              f'      rw [{name}_closure]',f'      simpa using {name}_moment)','']
        title='fourth_power_bound' if k==4 else 'sixth_power_bound'
        apps+=[f'theorem {title} : PowerLowerBound {k} {alpha} := by',
          f'  let cs : List (MomentComponent {k} {alpha}) :=',
          '    ['+', '.join(n+'_component' for n in names)+']',
          f'  apply powerLowerBound_of_intervalMoments {k} {alpha} (by decide) (by norm_num) cs',
          '  · simp [cs]',
          '  · change ['+', '.join(f'perfectPowerClosure {k} {b["m"]}' for b in case['blocks'])+'].Pairwise Nat.Coprime',
          '    rw ['+', '.join(n+'_closure' for n in names)+']', '    decide',
          f'  · change {alpha} < ['+', '.join(frac(b['f_numerator'],b['f_denominator']) for b in case['blocks'])+'].sum',
          '    norm_num','']
    lines+=['end NK.Certificates',''];apps+=['end NK.Certificates','']
    (ROOT/'NK/Certificates/EvenMoments.lean').write_text('\n'.join(lines))
    (ROOT/'NK/Certificates/EvenApplications.lean').write_text('\n'.join(apps))
if __name__=='__main__':main()
