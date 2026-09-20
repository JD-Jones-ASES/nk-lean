#!/usr/bin/env python3
"""Transcribe the supplied finite binary geometry; Lean proves every condition."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'certificates/square/data/binary_policy.json'
DEST = ROOT / 'NK/Certificates/BinaryGeometry.lean'


def real(x):
    x = Fraction(x)
    return f'({x.numerator} / {x.denominator} : ℝ)'


def interval(left, width):
    return f'⟨{real(left)}, {real(width)}, by norm_num, by norm_num, by norm_num⟩'


def window(w):
    if w is None:
        return 'none'
    left, right = map(Fraction, w)
    return 'some ' + interval(left, right-left)


def transformed(states, transition, parity):
    _, child, swap, reflect, scale, shift = transition
    w = states[child]['parity_windows'][parity ^ swap]
    if w is None:
        return None
    left, right = map(Fraction, w)
    if reflect:
        left, right = 1-right, 1-left
    scale, shift = Fraction(scale), Fraction(shift)
    return shift + scale*left, shift + scale*right


def main():
    raw = SOURCE.read_bytes()
    states = json.loads(raw)['states']
    if len(states) != 25 or sum(len(s['transitions']) for s in states) != 94:
        raise ValueError('Expected the supplied 25-state, 94-transition policy')
    out = [
        'import NK.BinaryPolicyGrowth', '',
        '/-! Exact binary policy geometry, generated from the supplied mathematical witness.',
        'Source: Naslund, commit e5d693729e23762b063a55015ad79ccaf28a3217.',
        f'Input SHA256: {hashlib.sha256(raw).hexdigest()}.',
        'All containment, cyclic ordering, and seed bounds are proved below in Lean. -/',
        'set_option maxHeartbeats 0', 'set_option maxRecDepth 32768',
        'namespace NK.Certificates', 'open NK.BinaryPolicy', '',
    ]
    for i, state in enumerate(states):
        if len(state['parity_windows']) != 2:
            raise ValueError(f'Expected two parity windows in state {i}')
        out += [f'noncomputable def binaryState{i} : State :=',
                '  ![' + ', '.join(window(w) for w in state['parity_windows']) + ']', '']
    out += ['noncomputable def binaryWindows (i : Fin 25) : State :=', '  match i.val with']
    out += [f'  | {i} => binaryState{i}' for i in range(25)]
    out += ['  | _ => binaryState0', '']
    for i, state in enumerate(states):
        for transition in state['transitions']:
            if len(transition) != 6:
                raise ValueError(f'Malformed transition in state {i}')
            branch, child, swap, reflect, _, _ = transition
            if branch not in range(4) or child not in range(25) or swap not in (0, 1) or reflect not in (0, 1):
                raise ValueError(f'Out-of-domain transition in state {i}')
        branches = {t[0]: t for t in state['transitions']}
        if len(branches) != len(state['transitions']):
            raise ValueError(f'Duplicate branch in state {i}')
        row = []
        classes = []
        for branch in range(4):
            if branch not in branches:
                row.append('none')
            else:
                _, child, swap, reflect, scale, shift = branches[branch]
                row.append(f'some ⟨{child}, {str(bool(swap)).lower()}, {str(bool(reflect)).lower()}, '
                           + interval(shift, scale) + '⟩')
        for c in range(8):
            t = branches.get(c % 4)
            classes.append(window(None if t is None else transformed(states, t, c // 4)))
        has_adjacent = any(classes[c] != 'none' and classes[(c+1) % 8] != 'none' for c in range(8))
        cycle_finish = '    all_goals (cases hI <;> cases hJ' + (' <;> norm_num)' if has_adjacent else ')')
        out += [f'noncomputable def binaryRow{i} : Row (Fin 25) :=', '  ![' + ', '.join(row) + ']', '',
                f'noncomputable def binaryClass{i} : Fin 8 → Option UnitInterval :=',
                '  ![' + ', '.join(classes) + ']', '',
                f'theorem binaryClass{i}_exact (c : Fin 8) :',
                f'    classWindow binaryWindows binaryRow{i} c = binaryClass{i} c := by',
                '  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,',
                f'    binaryRow{i}, binaryClass{i}, binaryWindows, Transition.state, orientState,',
                '    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,',
                '    ' + ', '.join(f'binaryState{j}' for j in sorted({t[1] for t in state['transitions']})) + ']', '',
                f'theorem binaryRow{i}_valid : RowValid binaryWindows binaryState{i} binaryRow{i} where',
                '  inside := by', '    intro c I hI', f'    rw [binaryClass{i}_exact] at hI',
                f'    fin_cases c <;> norm_num [binaryClass{i}] at hI',
                '    all_goals cases hI',
                f'    all_goals norm_num [InWindow, Contains, binaryState{i}, parity]',
                '  cycle := by', '    intro c d I J hI hJ hnext',
                f'    rw [binaryClass{i}_exact] at hI hJ',
                '    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm',
                '    subst d', '    fin_cases c',
                f'    all_goals norm_num [binaryClass{i}] at hI hJ',
                cycle_finish, '']
    out += ['noncomputable def binaryRows (i : Fin 25) : Row (Fin 25) :=', '  match i.val with']
    out += [f'  | {i} => binaryRow{i}' for i in range(25)]
    out += ['  | _ => binaryRow0', '',
            'theorem binaryRows_valid (i : Fin 25) : RowValid binaryWindows (binaryWindows i) (binaryRows i) := by',
            '  fin_cases i']
    for i in range(25):
        out += [f'  · exact binaryRow{i}_valid']
    out += ['', 'theorem binarySeeds_nonempty (i : Fin 25) : Nonempty (Seed (binaryWindows i)) := by', '  fin_cases i']
    for i, state in enumerate(states):
        candidates = [(Fraction(w[1])-Fraction(w[0]), p, w)
                      for p, w in enumerate(state['parity_windows']) if w is not None]
        width, p, w = max(candidates)
        if width < Fraction(1, 4):
            raise ValueError(f'No quarter seed in state {i}')
        out += [f'  · exact ⟨⟨{p}, {interval(w[0], width)},',
                f'      by norm_num [binaryWindows, binaryState{i}], by norm_num⟩⟩']
    out += ['', 'noncomputable def binarySeeds (i : Fin 25) : Seed (binaryWindows i) :=',
            '  Classical.choice (binarySeeds_nonempty i)', '',
            'noncomputable def binaryPolicy : Policy (Fin 25) where',
            '  windows := binaryWindows', '  rows := binaryRows',
            '  valid := binaryRows_valid', '  seed := binarySeeds', '',
            'end NK.Certificates', '']
    DEST.write_text('\n'.join(out))


if __name__ == '__main__':
    main()
