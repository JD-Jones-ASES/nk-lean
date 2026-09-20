#!/usr/bin/env python3
"""Untrusted chunked retained-pair moments; outputs require Lean kernel replay.

No Lean process is launched. Existing named geometry trees are matched literally.
Every generated numerical claim still requires ordinary Lean kernel checking.
"""
import argparse
import hashlib
import importlib.util
import json
from fractions import Fraction
from pathlib import Path
import re
import sys
import time

sys.dont_write_bytecode = True
ORDER = (0, 3, 1, 4, 5, 2)
THRESHOLD = 128
DEPTH = 3


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[1] / 'scratch/chunked-odd')
    ap.add_argument('--q', type=int, choices=(215, 437), default=437)
    ap.add_argument('--chunk-limit', type=int, choices=(16, 32, 64, 128), default=128,
                    help='Maximum leaves per numerical obligation; existing data chunks use128')
    ap.add_argument('--checker', choices=('OneSidedPairMoment', 'PairMomentCertificate'),
                    default='OneSidedPairMoment')
    args = ap.parse_args()
    start = time.perf_counter()
    root, out, q = args.root.resolve(), args.out.resolve(), args.q
    gp = root / 'scripts/generate_odd_geometry.py'
    mp = root / 'scripts/generate_even_certificates.py'
    geom = load_module('nk_chunk_geometry', gp)
    mirror = load_module('nk_chunk_mirror', mp)
    require(mirror.S == 10**24, 'Unexpected numerical scale')
    S = mirror.S
    certificate_path = root / 'certificates/square/certificate.json'
    cert = json.loads(certificate_path.read_text())
    block = next(b for b in cert['odd'] if b['q'] == q)
    alpha, f = Fraction(cert['alpha']), Fraction(block['f'])
    an, ad, fn, fd = alpha.numerator, alpha.denominator, f.numerator, f.denominator
    data_path = root / 'certificates/square' / block['file']
    records = [list(map(int, line.split())) for line in data_path.read_text().splitlines()]
    p, r, count, D = records[0]
    rows = records[1:]
    require(count == len(rows) and p*r == q and all(len(x) == 8 for x in rows), 'Bad flat data shape')
    require(fd > 0 and all(0 < x[7] <= D for x in rows), 'Invalid width/domain')
    nodes = geom.build(rows, ORDER)
    sizes = []
    for node in nodes:
        sizes.append(1 if node[3] < 0 else sizes[node[3]] + sizes[node[4]])

    def word(w):
        return '[' + ', '.join(map(str, w)) + ']'

    def inline(i):
        node = nodes[i]
        if node[3] < 0:
            row = rows[node[5]]
            return f'.leaf ⟨({word(row[:3])}, {word(row[3:6])}), {row[6]}, {row[7]}⟩'
        return f'.branch {word(node[0])} {word(node[1])} {node[2]} ({inline(node[3])}) ({inline(node[4])})'

    def tree(i):
        return f'odd{q}Tree_{i}'

    named, expected = [], {}

    def declarations(i):
        node = nodes[i]
        if sizes[i] <= THRESHOLD:
            body = inline(i)
        else:
            declarations(node[3])
            declarations(node[4])
            body = f'.branch {word(node[0])} {word(node[1])} {node[2]} {tree(node[3])} {tree(node[4])}'
        named.append(i)
        expected[tree(i)] = body

    root_index = len(nodes)-1
    declarations(root_index)
    lean_data_path = root / f'NK/Certificates/Odd{q}Data.lean'
    lean_data = lean_data_path.read_text()
    actual = dict(re.findall(rf'^def (odd{q}Tree_\d+) : PairCertificateTree :=\n  ([^\n]+)\n', lean_data, re.M))
    require(actual == expected, 'Named Lean tree definitions differ from reconstructed literal data')
    aliases = re.findall(rf'^def odd{q}Tree : PairCertificateTree := (\w+)$', lean_data, re.M)
    require(aliases == [tree(root_index)], 'Wrong root alias')
    data_named = set(named)
    named = []
    def proof_nodes(i):
        if sizes[i] > args.chunk_limit:
            proof_nodes(nodes[i][3])
            proof_nodes(nodes[i][4])
        named.append(i)
    proof_nodes(root_index)
    def tree(i):
        return f'odd{q}Tree_{i}' if i in data_named else f'odd{q}MomentTree_{i}'
    frontier = [i for i in named if sizes[i] <= args.chunk_limit]
    require(sum(sizes[i] for i in frontier) == count, 'Frontier does not partition the leaves')

    cache, maximum_log_hi, minimum_rpow_lo = {}, 0, None
    for width in sorted({row[7] for row in rows}):
        shift = (D // width).bit_length()-1
        powerlog = mirror.scale(mirror.logpos(D, width, shift), fn, fd)
        require(width * 2**shift <= D <= 2*width*2**shift, 'Bad dyadic shift')
        require(8*powerlog[1] <= S*2**DEPTH, 'Depth3 range reduction failed')
        # Fixed depth3 is essential: mirror.powerdata chooses an adaptive depth.
        raw_lo = mirror.expos(powerlog[0], S, DEPTH)[0]
        raw_hi = mirror.expos(powerlog[1], S, DEPTH)[1]
        require(0 < raw_lo <= raw_hi, 'Original reciprocal enclosure invalid')
        cache[width] = S*S // raw_hi
        maximum_log_hi = max(maximum_log_hi, powerlog[1])
        minimum_rpow_lo = raw_lo if minimum_rpow_lo is None else min(minimum_rpow_lo, raw_lo)

    sums = []
    for node in nodes:
        sums.append(cache[rows[node[5]][7]] if node[3] < 0 else sums[node[3]] + sums[node[4]])
    require(sums[root_index] == sum(cache[row[7]] for row in rows), 'Tree/flat lower-sum disagreement')
    B, mult = q**6, q**3
    top = mirror.powerdata(B, 1, an, ad)
    top_literal = mirror.lean(top)
    gap = mult*sums[root_index] - top[3]
    require(gap >= 0, 'Exact final natural-number comparison failed')

    checker = args.checker
    params = f'{S} {D} {fn} {fd}'
    valid = lambda i: f'odd{q}_numeric_valid_{i}'
    sum_name = lambda i: f'odd{q}_lower_sum_{i}'
    header = [f'import NK.Certificates.Odd{q}Data', f'import NK.{checker}', '',
              '/-! Untrusted generator output; all numerical claims require Lean kernel replay.',
              'No numerical theorem here is accepted merely because Python emitted it. -/',
              'set_option maxHeartbeats 0','set_option Elab.async false', 'set_option maxRecDepth 32768',
              'namespace NK.Certificates', '']

    def helper_definition(i):
        if i in data_named:
            return []
        node = nodes[i]
        if sizes[i] <= args.chunk_limit:
            body = inline(i)
        else:
            body = f'.branch {word(node[0])} {word(node[1])} {node[2]} {tree(node[3])} {tree(node[4])}'
        return [f'def {tree(i)} : PairCertificateTree :=', f'  {body}', '']

    valid_branch = f'odd{q}_valid_branch'
    sum_branch = f'odd{q}_lowerSum_branch_values'
    header += [
        f'private theorem {valid_branch} (S D fn fd : ℕ) (p q : List ℕ) (a : ℕ)',
        '    (l r : PairCertificateTree)',
        f'    (hl : {checker}.Valid S D fn fd l) (hr : {checker}.Valid S D fn fd r) :',
        f'    {checker}.Valid S D fn fd (.branch p q a l r) := ⟨hl, hr⟩', '',
        f'private theorem {sum_branch} (S D fn fd : ℕ) (p q : List ℕ) (a : ℕ)',
        '    (l r : PairCertificateTree) (L R : ℕ)',
        '    (hl : PairMomentCertificate.lowerSum S D fn fd l = L)',
        '    (hr : PairMomentCertificate.lowerSum S D fn fd r = R) :',
        '    PairMomentCertificate.lowerSum S D fn fd (.branch p q a l r) = L + R :=',
        '  congrArg₂ Nat.add hl hr', '']

    def node_proofs(i):
        node = nodes[i]
        is_chunk = sizes[i] <= args.chunk_limit
        lines = [f'-- {sizes[i]} leaves; literal tree {tree(i)}.']
        if not is_chunk:
            left, right = node[3:5]
            shape = f'odd{q}_numeric_shape_{i}'
            branch = f'.branch {word(node[0])} {word(node[1])} {node[2]} {tree(left)} {tree(right)}'
            branch_args = f'{params} {word(node[0])} {word(node[1])} {node[2]} {tree(left)} {tree(right)}'
            lines += [f'private theorem {shape} : {tree(i)} = {branch} := rfl', '']
        lines += [f'theorem {valid(i)} : {checker}.Valid {params} {tree(i)} := by']
        if is_chunk:
            lines += ['  decide +kernel']
        else:
            lines += [f'  exact Eq.mpr (congrArg ({checker}.Valid {params}) {shape})',
                      f'    ({valid_branch} {branch_args} {valid(left)} {valid(right)})']
        lines += ['', f'theorem {sum_name(i)} :',
                  f'    PairMomentCertificate.lowerSum {params} {tree(i)} = {sums[i]} := by']
        if is_chunk:
            lines += ['  decide +kernel']
        else:
            lines += [f'  exact (congrArg (PairMomentCertificate.lowerSum {params}) {shape}).trans',
                      f'    (({sum_branch} {branch_args} {sums[left]} {sums[right]}',
                      f'      {sum_name(left)} {sum_name(right)}).trans (by decide +kernel))']
        return lines + ['']

    full = header.copy()
    for i in named:
        full += helper_definition(i) + node_proofs(i)
    full += [f'private theorem odd{q}_numeric_root_shape : odd{q}Tree = {tree(root_index)} := rfl', '',
             f'theorem odd{q}_numeric_valid : {checker}.Valid {params} odd{q}Tree :=',
             f'  Eq.mpr (congrArg ({checker}.Valid {params}) odd{q}_numeric_root_shape) {valid(root_index)}', '',
             f'theorem odd{q}_lower_sum :',
             f'    PairMomentCertificate.lowerSum {params} odd{q}Tree = {sums[root_index]} :=',
             f'  (congrArg (PairMomentCertificate.lowerSum {params}) odd{q}_numeric_root_shape).trans {sum_name(root_index)}', '',
             f'theorem odd{q}_numeric_top_valid :',
             f'    ({top_literal} : RationalMomentCertificate.PowerData).Valid {S} {B} 1 {an} {ad} := by',
             '  decide +kernel', '',
             f'theorem odd{q}_numeric_compare : {top[3]} ≤',
             f'    {mult} * PairMomentCertificate.lowerSum {params} odd{q}Tree := by',
             f'  exact Eq.mpr (congrArg (fun n : ℕ => {top[3]} ≤ {mult} * n) odd{q}_lower_sum)',
             '    (by decide +kernel)', '',
             f'theorem odd{q}_moment : ({B}:ℝ)^{mirror.frac(an,ad)} ≤ ({mult}:ℝ) *',
             f'    (odd{q}Tree.rows.map (fun r => ((r.width:ℝ)/{D})^{mirror.frac(fn,fd)})).sum := by',
             f'  simpa only [Nat.cast_ofNat] using ({checker}.moment_bound {params} {B} {mult} {an} {ad}',
             f'    odd{q}Tree {top_literal} (by decide +kernel) odd{q}_numeric_valid',
             f'    odd{q}_numeric_top_valid odd{q}_numeric_compare)', '', 'end NK.Certificates', '']
    sample = header + helper_definition(frontier[0]) + node_proofs(frontier[0]) + ['end NK.Certificates', '']
    out.mkdir(parents=True, exist_ok=True)
    full_path = out / f'Odd{q}NumericChunked.lean'
    sample_path = out / f'Odd{q}NumericFirstChunk.lean'
    full_path.write_text('\n'.join(full))
    sample_path.write_text('\n'.join(sample))
    report = {
        'status': 'UNTRUSTED_GENERATOR_OUTPUT_NOT_LEAN_CHECKED', 'lean_builds_run': 0,
        'q': q, 'vertices': count, 'named_nodes': len(named), 'frontier_chunks': len(frontier),
        'existing_data_nodes': len(data_named), 'new_helper_definitions': len(set(named)-data_named),
        'chunk_limit': args.chunk_limit,
        'chunk_leaf_counts': sorted(set(sizes[i] for i in frontier)), 'upper_branch_nodes': len(named)-len(frontier),
        'scale': S, 'reduction_depth': DEPTH, 'denominator': D,
        'f': str(f), 'alpha': str(alpha), 'checker': checker,
        'root_name': tree(root_index), 'root_lower_sum': sums[root_index],
        'top_upper': top[3], 'multiplicity': mult, 'integer_comparison_surplus': gap,
        'maximum_powerlog_hi': maximum_log_hi, 'minimum_original_rpow_lo': minimum_rpow_lo,
        'distinct_widths': len(cache), 'all_named_tree_bodies_matched': True,
        'source_sha256': {str(p): digest(p) for p in [data_path, lean_data_path, certificate_path, gp, mp, Path(__file__).resolve(),
            root/'NK/PairMomentCertificate.lean', root/'NK/RationalPowerBounds.lean',
            root/'NK/FixedPointSeries.lean', root/f'NK/{checker}.lean']},
        'output_sha256': {str(p): digest(p) for p in [full_path, sample_path]},
        'chunks': [{'name': tree(i), 'leaves': sizes[i], 'lower_sum': sums[i]} for i in frontier],
        'elapsed_seconds': time.perf_counter()-start,
    }
    (out / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    (out / 'README.md').write_text(f'''# Chunked odd{q} numerical replay

This directory is generated by `scripts/generate_chunked_odd_moments.py`.
The generator writes only its output artifacts into the selected `--out`
directory and launches no Lean process. Its default output is under the
repository's scratch directory. Source geometry and numerical parameters
remain unchanged. Python is an untrusted mirror; all emitted equalities and
validity conditions require kernel checking.

The {count} leaves are partitioned into {len(frontier)} named
frontier definitions, each with {sorted(set(sizes[i] for i in frontier))} leaves.
All {len(data_named)} original named tree bodies were compared literally against Odd{q}Data.
The selected limit is {args.chunk_limit}; {len(set(named)-data_named)} additional local
helper definitions split original chunks without altering the imported data. Their
relationship to the original trees is checked by Lean definitional equality when
assembling parent facts; Python's comparison is not part of the proof boundary.
Each frontier gets its own validity and exact lowerSum proof. The {len(named)-len(frontier)}
upper branches assemble already proved child facts through generic opaque
congruence lemmas and data-only tree-shape equalities. They do not decide the
entire descendant tree again, and do not use parent-level change/rw on a closed
lowerSum. Equality junctions are syntactically identical; only the final
literal child-sum addition is decided. The final comparison uses a literal sum.

`Odd{q}NumericFirstChunk.lean` is a small benchmark candidate.
`Odd{q}NumericChunked.lean` is the complete replacement candidate for the
numerical wrapper only. They intentionally define overlapping names and
should be checked separately. Neither imports the old Odd{q}Numeric module.
No geometry certificate or application wrapper is changed.

Checker API: import NK.{checker}; use its Valid and moment_bound.
The sum remains NK.PairMomentCertificate.lowerSum. Its literal mirror uses
scale 10^24 and fixed reduction depth 3, not powerdata's adaptive depth.
OneSidedPairMoment drops the old lower reciprocal-endpoint positivity test;
the generated lowerSum endpoints remain exactly unchanged.

To check a generated sample in the prepared Lean project:
`lake env lean -DautoImplicit=false {sample_path}`.
After that succeeds, the full candidate can be checked by the same command.
The generator does not perform either check. Consult the repository's current
proof-status and verification notes for actual replay outcomes. Chunking reduces
individual numerical obligations but does not itself prove a memory bound.
''')
    print(json.dumps({k: report[k] for k in ['q','vertices','frontier_chunks','chunk_leaf_counts',
                     'named_nodes','root_lower_sum','integer_comparison_surplus','elapsed_seconds']}, indent=2))
    print(f'Generated {full_path} and {sample_path}; NO Lean builds run.')


if __name__ == '__main__':
    main()
