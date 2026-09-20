#!/usr/bin/env python3
"""Generate small square-chain certificates, verified entirely in Lean."""
from fractions import Fraction
import json
from generate_even_certificates import ROOT,S,powerdata,lean,frac

def main():
    data=json.loads((ROOT/'certificates/square/certificate.json').read_text())
    alpha=Fraction(data['alpha']);an,ad=alpha.numerator,alpha.denominator;a=frac(an,ad)
    lines=['import NK.RationalMomentCertificate','','/-! Exact square-chain components; all arithmetic is kernel checked. -/',
      'set_option maxHeartbeats 0','set_option maxRecDepth 32768','namespace NK.Certificates',
      'open RationalMomentCertificate','']
    for row in data['chains']:
        p=row['prime'];name=f'square_chain{p}';vs=row['ordered_residues'];t=len(vs);f=Fraction(row['f']);fn,fd=f.numerator,f.denominator;fs=frac(fn,fd)
        low=powerdata(t,1,fn,fd,True);top=powerdata(p*p,1,an,ad)
        assert top[3] <= p*t*low[2]
        lines += [f'def {name} : RationalAlphabetData :=',f'  .ofRows {t} ['+', '.join(f'({v}, {i}, 1)' for i,v in enumerate(vs))+']',
          f'theorem {name}_valid : {name}.Valid 2 {p} := by decide','',
          f'theorem {name}_moment : ({p*p}:ℝ)^{a} ≤ ({p}:ℝ) *',
          f'    ∑ x∈{name}.support, (({name}.width x:ℝ)/{name}.denominator)^{fs} := by',
          f'  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound {name} {S} {p*p} {p} {an} {ad} {fn} {fd}',
          f'    {lean(top)} (fun _ => {lean(low)})',
          '    (by decide) (by decide) (by decide) (by decide))','',
          f'theorem {name}_closure : perfectPowerClosure 2 {p} = {p*p} := by',
          f'  have h := perfectPowerClosure_prime_pow 2 {p} 1 (by decide) (by decide)',
          '  norm_num at h','  exact h','',
          f'noncomputable def {name}_component : MomentComponent 2 {a} :=',
          f'  {name}.toComponent 2 {p} {a} {fs}',
          f'    (by decide) (by decide) {name}_valid (by norm_num) (by',
          f'      rw [{name}_closure]',f'      simpa using {name}_moment)','',
          f'theorem {name}_base : {name}_component.base = {p*p} := {name}_closure','']
    lines+=['end NK.Certificates','']
    (ROOT/'NK/Certificates/SquareChains.lean').write_text('\n'.join(lines))
if __name__=='__main__':main()
