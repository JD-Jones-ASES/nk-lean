#!/usr/bin/env python3
"""Generate the finite-depth logarithmic certificate at the P0180 allocation."""
from fractions import Fraction as F
import json
from generate_even_certificates import ROOT,S,logpos,frac

def main():
    d=json.loads((ROOT/'certificates/square/certificate.json').read_text());a=F(d['alpha']);f=F(d['binary']['f']);g=F(d['binary']['growth_lower']);m=d['binary']['depth']
    ar,fr,gr=[frac(z.numerator,z.denominator) for z in (a,f,g)]
    ga=logpos(g.numerator,g.denominator,1)[0];l4=logpos(4,1,2)[1];l2=logpos(2,1,1)[1]
    assert (m-1)*ga-(1+a*m)*l4-f*l2>0
    lines=['import NK.BinaryDepth','','/-! Finite depth10^15, certified without expanding4^(10^15). -/',
      'namespace NK.Certificates','open NK.RationalPowerBounds','',
      f'theorem binary_depth_moment : (((4 ^ {m} : ℕ):ℝ)^{ar}) ≤',
      f'    (1/2:ℝ)^{fr} * (1/4:ℝ) * {gr}^({m}-1 : ℕ) := by',
      f'  apply binary_depth_moment_of_logs {m} {ar} {fr} {gr} (by decide) (by norm_num)']
    for label,x,y,shift,which,val in [('a',g.numerator,g.denominator,1,'lo',ga),('b',4,1,2,'hi',l4),('c',2,1,1,'hi',l2)]:
      proj='1' if which=='lo' else '2'
      lines += [f'  have h{label} := (logPosBounds_sound {S} {x} {y} {shift} (by decide) (by decide) (by decide) (by decide)).{proj}',
        f'  have h{label}v : (logPosBounds {S} {x} {y} {shift}).{which} = {val} := by decide',
        f'  rw [h{label}v] at h{label}']
    lines += [f'  have haW := mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ) ≤ ({m}:ℝ)-1)',
      f'  have hbW := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1+{ar}*{m})',
      f'  have hcW := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ {fr})',
      '  norm_num at haW hbW hcW ⊢','  linarith','',
      'end NK.Certificates','']
    (ROOT/'NK/Certificates/BinaryDepth.lean').write_text('\n'.join(lines))
if __name__=='__main__':main()
