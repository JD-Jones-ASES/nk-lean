#!/usr/bin/env python3
"""Exact finite input for the proved rational-power evaluator and binary rows."""
from fractions import Fraction as F
import json
from generate_even_certificates import ROOT,S,powerdata,lean,frac

def rat(x):
    x=F(x);return frac(x.numerator,x.denominator)

def main():
    d=json.loads((ROOT/'certificates/square/data/binary_policy.json').read_text())
    f=F(d['moment_power']);growth=F(d['growth_lower']);vs=[F(s['positive_weight']) for s in d['states']]
    fn,fd=f.numerator,f.denominator
    lines=['import NK.Certificates.BinaryGeometry','import NK.RationalMomentCertificate','',
      '/-! Exact weighted-row certificate at the P0180 square allocation. -/',
      'set_option maxHeartbeats 0','set_option maxRecDepth 32768',
      'namespace NK.Certificates','open NK.BinaryPolicy NK.RationalMomentCertificate','',
      'noncomputable def binaryWeights (i : Fin 25) : ℝ :=', '  match i.val with', *[f'  | {i} => {rat(v)}' for i,v in enumerate(vs)], '  | _ => 0','',
      'theorem binaryWeights_bounds (i : Fin 25) : 0 < binaryWeights i ∧ binaryWeights i ≤ 1 := by',
      '  fin_cases i <;> norm_num [binaryWeights]','']
    for i,state in enumerate(d['states']):
        coeffs=[];lower={};upper={};proof={}
        lines += [f'theorem binaryRow{i}_growth : {rat(growth)} * binaryWeights {i} ≤',
          f'    rowMoment binaryRow{i} {rat(f)} binaryWeights := by']
        for j,t in enumerate(state['transitions']):
            branch,child,swap,ref,u,_=t;u=F(u);c=powerdata(u.denominator,u.numerator,fn,fd,True)
            coeffs.append(F(c[2],S)*vs[child])
            lines += [f'  have h{j} : ({c[2]} / {S} : ℝ) ≤ {rat(u)}^{rat(f)} := by',
              f'    simpa only [Nat.cast_ofNat, Nat.cast_one] using (PowerData.unit_sound {lean(c)} {S} {u.denominator} {u.numerator} {fn} {fd}',
              '      (by decide +kernel) (by decide +kernel)).1',
              f'  have hw{j} := mul_le_mul_of_nonneg_right h{j} (by norm_num : (0:ℝ) ≤ {rat(vs[child])})']
            lower[branch]=f'(({c[2]} / {S} : ℝ) * {rat(vs[child])})'
            upper[branch]=f'({rat(u)}^{rat(f)} * {rat(vs[child])})'
            proof[branch]=f'hw{j}'
        assert sum(coeffs)>=growth*vs[i],(i,sum(coeffs)-growth*vs[i])
        def summation(d):return '('+d.get(0,'0')+' + ('+d.get(1,'0')+' + ('+d.get(2,'0')+' + '+d.get(3,'0')+')))'
        lowerExpr=summation(lower);upperExpr=summation(upper)
        def pr(b):return proof.get(b,'(le_refl (0:ℝ))')
        lines += [f'  have hn : {rat(growth)} * {rat(vs[i])} ≤ {lowerExpr} := by norm_num',
          f'  have hs : {lowerExpr} ≤ {upperExpr} :=',
          f'    add_le_add {pr(0)} (add_le_add {pr(1)} (add_le_add {pr(2)} {pr(3)}))',
          f'  simpa [rowMoment, Fin.sum_univ_succ, binaryRow{i}, binaryWeights] using hn.trans hs','']
    lines += [f'theorem binaryRows_growth (i : Fin 25) : {rat(growth)} * binaryWeights i ≤',
      f'    rowMoment (binaryRows i) {rat(f)} binaryWeights := by',
      '  fin_cases i']
    for i in range(25):lines += [f'  · exact binaryRow{i}_growth']
    lines += ['', 'end NK.Certificates','']
    (ROOT/'NK/Certificates/BinaryMoments.lean').write_text('\n'.join(lines))
if __name__=='__main__':main()
