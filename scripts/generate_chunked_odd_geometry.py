#!/usr/bin/env python3
"""Untrusted chunked geometry checks; all root queries remain exact Lean checks."""
import argparse
from pathlib import Path
import re
from generate_odd_geometry import ROOT,load,build

def generate(q):
    (p,r,n,D),rows=load(q);nodes=build(rows,(0,3,1,4,5,2));sizes=[]
    for node in nodes:sizes.append(1 if node[3]<0 else sizes[node[3]]+sizes[node[4]])
    named=[]
    def visit(i):
        if sizes[i]>128:visit(nodes[i][3]);visit(nodes[i][4])
        named.append(i)
    visit(len(nodes)-1)
    tree=lambda i:f'odd{q}Tree_{i}'
    word=lambda a:'['+', '.join(map(str,a))+']'
    def inline(i):
        node=nodes[i]
        if node[3]<0:
            row=rows[node[5]]
            return f'.leaf ⟨({word(row[:3])}, {word(row[3:6])}), {row[6]}, {row[7]}⟩'
        return f'.branch {word(node[0])} {word(node[1])} {node[2]} ({inline(node[3])}) ({inline(node[4])})'
    expected={}
    for i in named:
        node=nodes[i]
        expected[tree(i)]=inline(i) if sizes[i]<=128 else (
            f'.branch {word(node[0])} {word(node[1])} {node[2]} {tree(node[3])} {tree(node[4])}')
    data=(ROOT/f'NK/Certificates/Odd{q}Data.lean').read_text()
    declarations=re.findall(r'^def (odd\d+Tree_\d+) : PairCertificateTree',data,re.M)
    bodies=re.findall(rf'^def (odd{q}Tree_\d+) : PairCertificateTree :=\n  ([^\n]+)\n',data,re.M)
    if (len(declarations)!=len(expected) or set(declarations)!=set(expected) or
            len(bodies)!=len(expected) or dict(bodies)!=expected):
        raise ValueError('Data tree names or literal bodies differ; regenerate data first')
    aliases=re.findall(rf'^def odd{q}Tree : PairCertificateTree := (\w+)$',data,re.M)
    if aliases!=[tree(len(nodes)-1)]:
        raise ValueError('Data root alias differs; regenerate data first')
    masks=[sum(1<<d for d in {pow(x,2,m) for x in range(m)} if d) for m in [p,r]]
    pm,qm=masks;test=f'(fun source => odd{q}Tree.FastQuery 2 {p} {r} {pm} {qm} source)'
    lines=[f'import NK.Certificates.Odd{q}Data','import NK.PairCertificateComposition','',
      '/-! Literal rows are checked in bounded chunks against the full target tree.',
      'Generic proved assembly combines summaries, uniqueness and every source query. -/',
      'set_option maxRecDepth 32768','set_option maxHeartbeats 0','set_option Elab.async false','namespace NK.Certificates','',
      f'theorem odd{q}_pMask : PowerMaskValid 2 {p} {pm} := by decide +kernel',
      f'theorem odd{q}_qMask : PowerMaskValid 2 {r} {qm} := by decide +kernel','']
    for i in named:
        node=nodes[i];chunk=sizes[i]<=128;tn=tree(i)
        lines.append(f'-- {sizes[i]} source leaves.')
        lines.append(f'theorem odd{q}_valid_{i} : {tn}.Valid {p} {r} 3 {D} := by')
        if chunk:lines.append('  decide +kernel')
        else:
            l,rr=node[3:5];args=f'{tn} {word(node[0])} {word(node[1])} {node[2]} {tree(l)} {tree(rr)}'
            lines += [f'  exact PairCertificateTree.valid_of_branch_eq {p} {r} 3 {D} {args}',
              '    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)',
              '    (by decide +kernel) (by decide +kernel) (by decide +kernel)',
              f'    odd{q}_valid_{l} odd{q}_valid_{rr}']
        lines += ['',f'theorem odd{q}_sorted_{i} : {tn}.Sorted odd{q}Key = true := by']
        if chunk:lines.append('  decide +kernel')
        else:lines += [f'  exact PairCertificateTree.sorted_of_branch_eq odd{q}Key {args}',
                      f'    rfl (by decide +kernel) odd{q}_sorted_{l} odd{q}_sorted_{rr}']
        lines += ['',f'theorem odd{q}_queries_{i} : {tn}.rows.all {test} = true := by']
        if chunk:lines.append('  decide +kernel')
        else:lines += [f'  exact PairCertificateTree.rows_all_of_branch_eq {test} {args}',
                      f'    rfl odd{q}_queries_{l} odd{q}_queries_{rr}']
        lines.append('')
    last=named[-1]
    for label,pred,target in [('valid',f'(fun t : PairCertificateTree => t.Valid {p} {r} 3 {D})',f'odd{q}Tree.Valid {p} {r} 3 {D}'),
                              ('sorted',f'(fun t : PairCertificateTree => t.Sorted odd{q}Key = true)',f'odd{q}Tree.Sorted odd{q}Key = true'),
                              ('queries',f'(fun t : PairCertificateTree => t.rows.all {test} = true)',f'odd{q}Tree.rows.all {test} = true')]:
        lines += [f'theorem odd{q}_tree_{label} : {target} :=',
          f'  Eq.mpr (congrArg {pred} (show odd{q}Tree = {tree(last)} from rfl)) odd{q}_{label}_{last}','']
    lines += [f'theorem odd{q}_tree_geometry : odd{q}Tree.GeometryValid 2 {p} {r} = true :=',
       f'  PairCertificateTree.fastGeometryValid_sound 2 {p} {r} {pm} {qm} (by decide) (by decide)',
       f'    odd{q}_pMask odd{q}_qMask odd{q}Tree',
       f'    (PairCertificateTree.fastGeometry_of_rows_all 2 {p} {r} {pm} {qm} odd{q}Tree odd{q}_tree_queries)',
       '', 'end NK.Certificates','']
    text='\n'.join(lines)
    (ROOT/f'NK/Certificates/Odd{q}Geometry.lean').write_text(text)
    return text

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--q',type=int,choices=[215,437],required=True);args=ap.parse_args()
    text=generate(args.q);print(f'Generated odd{args.q} chunked geometry: {len(text)} characters')
if __name__=='__main__':main()
