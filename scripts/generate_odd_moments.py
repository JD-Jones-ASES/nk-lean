#!/usr/bin/env python3
"""Generate exact application wrappers; all numerical work is checked in Lean."""
from fractions import Fraction as F
import json
import subprocess
import sys
import shutil
from generate_even_certificates import ROOT,S,powerdata,lean,frac

def main():
    d=json.loads((ROOT/'certificates/square/certificate.json').read_text());a=F(d['alpha']);an,ad=a.numerator,a.denominator;alpha=frac(an,ad)
    for block in d['odd']:
        q=block['q'];f=F(block['f']);fn,fd=f.numerator,f.denominator;fs=frac(fn,fd)
        head=list(map(int,(ROOT/'certificates/square'/block['file']).read_text().splitlines()[0].split()));p,r,n,D=head
        top=powerdata(q**6,1,an,ad);t=f'odd{q}Tree';lo=f'odd{q}Low'
        lines=[f'import NK.Certificates.Odd{q}Geometry','import NK.PairMomentCertificate','',
          '/-! The exact low-word moment and its full retained-digit CRT component. -/',
          'set_option maxHeartbeats 0','set_option maxRecDepth 32768','namespace NK.Certificates','',
          f'theorem odd{q}_moment : ({q**6}:ℝ)^{alpha} ≤ ({q**3}:ℝ) *',
          f'    ({t}.rows.map (fun r => ((r.width:ℝ)/{D})^{fs})).sum := by',
          f'  simpa only [Nat.cast_ofNat] using (PairMomentCertificate.moment_bound {S} {D} {fn} {fd} {q**6} {q**3} {an} {ad}',
          f'    {t} {lean(top)} (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))','',
          f'noncomputable def {lo} : RetainedPairAlphabet 2 {p} {r} 3 :=',
          f'  {t}.toAlphabet 2 {p} {r} 3 {D} (by decide +kernel) odd{q}_tree_valid odd{q}_tree_geometry','',
          f'noncomputable def odd{q}_component : MomentComponent 2 {alpha} where',
          f'  base := {q**6}',f'  root := {q**3}','  base_ge_two := by decide','  base_eq_power := by decide',
          f'  alphabet := {lo}.toIntervalAlphabet (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)',
          f'  f := {fs}','  f_nonneg := by norm_num',
          '  width_lt_one x hx := by',
          f'    exact {t}.toAlphabet_width_lt_one 2 {p} {r} 3 {D} (by decide +kernel)',
          f'      odd{q}_tree_valid odd{q}_tree_geometry _ (Finset.mem_filter.mp hx).2',
          '  moment_bound := by','    rw [RetainedPairAlphabet.toIntervalAlphabet_moment]',
          f'    rw [{lo}, PairCertificateTree.toAlphabet_moment _ _ _ _ _ _ _ _ _ odd{q}Key odd{q}_tree_sorted]',
          f'    simpa using odd{q}_moment','',
          'end NK.Certificates','']
        text='\n'.join(lines);i=text.index(f'noncomputable def odd{q}Low')
        (ROOT/f'NK/Certificates/Odd{q}Numeric.lean').write_text(text[:i].replace(f'import NK.Certificates.Odd{q}Geometry',f'import NK.Certificates.Odd{q}Data')+'\nend NK.Certificates\n')
        (ROOT/f'NK/Certificates/Odd{q}Moments.lean').write_text(f'import NK.Certificates.Odd{q}Geometry\nimport NK.Certificates.Odd{q}Numeric\n\nnamespace NK.Certificates\n\n'+text[i:])
    out = ROOT/'scratch/chunked-odd'
    subprocess.run([sys.executable, str(ROOT/'scripts/generate_chunked_odd_moments.py'),
                    '--q', '437', '--out', str(out)], check=True)
    shutil.copyfile(out/'Odd437NumericChunked.lean', ROOT/'NK/Certificates/Odd437Numeric.lean')
if __name__=='__main__':main()
