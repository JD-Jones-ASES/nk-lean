#!/usr/bin/env python3
"""Untrusted geometry-tree generation; soundness belongs to Lean checker."""
from pathlib import Path
from itertools import combinations
import json
import argparse
ROOT=Path(__file__).resolve().parents[1]

def common(a,b):
    j=0
    while j<min(len(a),len(b)) and a[j]==b[j]:j+=1
    return a[:j]
def load(q):
    rs=[list(map(int,line.split())) for line in (ROOT/f'certificates/square/data/odd{q}.txt').read_text().splitlines()]
    return rs[0],rs[1:]
def build(rows,order):
    ids=sorted(range(len(rows)),key=lambda i:tuple(rows[i][j] for j in order))
    nodes=[]
    def rec(a,b):
        if b==a+1:
            i=ids[a];r=rows[i];node=(tuple(r[:3]),tuple(r[3:6]),r[6],-1,-1,i)
        else:
            mid=(a+b)//2;l=rec(a,mid);r=rec(mid,b);ln=nodes[l];rn=nodes[r]
            node=(common(ln[0],rn[0]),common(ln[1],rn[1]),min(ln[2],rn[2]),l,r,-1)
        nodes.append(node);return len(nodes)-1
    rec(0,len(ids));return nodes

def measure(rows,nodes,p,q,sources):
    sqp={x*x%p for x in range(p)};sqq={x*x%q for x in range(q)}
    def bad(word,prefix,p,squares):
        for x,y in zip(word,prefix):
            if x!=y:return (y-x)%p not in squares
        return False
    count=0
    for i in sources:
        r=rows[i];end=r[6]+r[7];todo=[len(nodes)-1]
        while todo:
            ix=todo.pop();count+=1;node=nodes[ix]
            if end<=node[2] or bad(r[:3],node[0],p,sqp) or bad(r[3:6],node[1],q,sqq):continue
            if node[3]<0:
                assert node[5]==i,(i,node[5])
            else:todo.extend((node[3],node[4]))
    return count

def emit(q,order=(0,3,1,4,5,2)):
    head,rows=load(q);nodes=build(rows,order);p,r,n,D=head
    visits=measure(rows,nodes,p,r,range(n))
    print(f'odd{q}: {n} leaves; {visits} query node visits',flush=True)
    sizes=[]
    for node in nodes:sizes.append(1 if node[3]<0 else sizes[node[3]]+sizes[node[4]])
    decls=[]
    def word(w):return '['+', '.join(map(str,w))+']'
    def inline(i):
        node=nodes[i]
        if node[3]<0:
            row=rows[node[5]]
            return f'.leaf ⟨({word(row[:3])}, {word(row[3:6])}), {row[6]}, {row[7]}⟩'
        return f'.branch {word(node[0])} {word(node[1])} {node[2]} ({inline(node[3])}) ({inline(node[4])})'
    def rec(i):
        node=nodes[i]
        if sizes[i]<=128:body=inline(i)
        else:
            l=rec(node[3]);r=rec(node[4]);body=f'.branch {word(node[0])} {word(node[1])} {node[2]} {l} {r}'
        name=f'odd{q}Tree_{i}'
        decls.append(f'def {name} : PairCertificateTree :=\n  {body}\n')
        return name
    root=rec(len(nodes)-1)
    text='\n'.join(['import NK.RetainedPairCertificate','',
      '/-! Exact P0180 data in a verified prefix/minimum-start pruning tree.',
      'The generator is untrusted. All summaries, uniqueness and queries are checked. -/',
      'set_option maxRecDepth 32768','set_option maxHeartbeats 0',
      'namespace NK.Certificates','',*decls,
      f'def odd{q}Tree : PairCertificateTree := {root}',
      f'def odd{q}Key (w : RetainedPair) : ℕ :=',
      '  (((((w.1.getD 0 0 * 64 + w.2.getD 0 0) * 64 + w.1.getD 1 0) * 64 + w.2.getD 1 0) * 64 + w.2.getD 2 0) * 64 + w.1.getD 2 0)',
      f'theorem odd{q}_tree_valid : odd{q}Tree.Valid {p} {r} 3 {D} := by decide +kernel',
      f'theorem odd{q}_tree_sorted : odd{q}Tree.Sorted odd{q}Key = true := by decide +kernel',
      f'theorem odd{q}_pMask : PowerMaskValid 2 {p} {sum(1 << d for d in {x*x%p for x in range(p)} if d)} := by decide +kernel',
      f'theorem odd{q}_qMask : PowerMaskValid 2 {r} {sum(1 << d for d in {x*x%r for x in range(r)} if d)} := by decide +kernel',
      f'theorem odd{q}_tree_geometry : odd{q}Tree.GeometryValid 2 {p} {r} = true :=',
      f'  PairCertificateTree.fastGeometryValid_sound 2 {p} {r} _ _ (by decide) (by decide)',
      f'    odd{q}_pMask odd{q}_qMask odd{q}Tree (by decide +kernel)',
      '', 'end NK.Certificates',''])
    i=text.index(f'theorem odd{q}_tree_valid')
    (ROOT/f'NK/Certificates/Odd{q}Data.lean').write_text(text[:i]+'\nend NK.Certificates\n')
    (ROOT/f'scratch/odd{q}-tree-replay.json').write_text(json.dumps(dict(vertices=n,tree_nodes=len(nodes),query_node_visits=visits,order=order),indent=2)+'\n')
    from generate_chunked_odd_geometry import generate
    generate(q)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--q',type=int,default=437);ap.add_argument('--samples',type=int,default=20);ap.add_argument('--all',action='store_true');ap.add_argument('--emit',action='store_true');args=ap.parse_args()
    if args.emit:emit(args.q);return
    head,rows=load(args.q);n=len(rows);sources=range(n) if args.all else sorted({(i*7919+17)%n for i in range(args.samples)})
    results=[]
    for pslots in combinations(range(6),3):
        pi=iter(range(3));qi=iter(range(3,6));order=tuple(next(pi) if j in pslots else next(qi) for j in range(6))
        nodes=build(rows,order);visits=measure(rows,nodes,*head[:2],sources)
        results.append((visits,order));print(visits,order,flush=True)
    print('best',min(results),flush=True)
if __name__=='__main__':main()
