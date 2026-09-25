#!/usr/bin/env python3
"""Independent-style directed oracle for the scratch extra O2a envelopes."""
import importlib.util
from pathlib import Path
import sys

BASE = Path(__file__).resolve().with_name('o2a_compare.py')
spec = importlib.util.spec_from_file_location('o2a_envelope_parser', BASE)
parser = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parser)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    if len(sys.argv) != 4:
        raise SystemExit('usage: compare_extra.py SPARSE_C SPARSE_LEAN SLOW_C')
    sparse_c, sparse_lean, slow_c = map(Path, sys.argv[1:])
    data = sparse_c.read_bytes()
    need(data == sparse_lean.read_bytes(), 'C/Lean full-envelope bytes differ')
    need(data == slow_c.read_bytes(), 'sparse/slow full-envelope bytes differ')
    cases = parser.parse(sparse_c)
    names = [
        'DISJOINT_DEFAULT', 'SAME_FIXED_MERGE', 'DIFFERENT_FIXED_MERGE',
        'INITIAL_FIXED', 'REVERSED_REPEAT', 'SELF_PAIR', 'SET_THEN_READ',
        'READ_THEN_PAIR', 'READ_PAIR_SET', 'DUPLICATE_ADVICE',
        'CONFLICT_ADVICE', 'INVALID_POINTER', 'CHECKER_REJECTED',
        'CHECKER_MISMATCH',
    ]
    need([c['name'] for c in cases] == names, 'extra case sequence')
    by = {c['name']: c for c in cases}
    header_keys = ('status', 'phase', 'tag', 'reason', 'fi', 'fo',
                   'steps', 'pc', 'fp', 'checker')
    headers = {
        'DISJOINT_DEFAULT': (2, 0, 2, 0, 0, 0, 2, 4, 1, (4, 1, 5)),
        'SAME_FIXED_MERGE': (2, 0, 2, 0, 0, 0, 2, 4, 1, (4, 1, 5)),
        'DIFFERENT_FIXED_MERGE': (16, 9, 0, 0, 3, 5, 1, 2, 1, None),
        'INITIAL_FIXED': (2, 0, 2, 0, 0, 0, 1, 2, 1, (2, 1, 5)),
        'REVERSED_REPEAT': (2, 0, 2, 0, 0, 0, 2, 4, 1, (4, 1, 5)),
        'SELF_PAIR': (2, 0, 2, 0, 0, 0, 1, 2, 1, (2, 1, 5)),
        'SET_THEN_READ': (1, 0, 3, 0, 0, 0, 3, 8, 1, (8, 1, 1)),
        'READ_THEN_PAIR': (2, 0, 2, 0, 0, 0, 2, 4, 1, (4, 1, 5)),
        'READ_PAIR_SET': (8, 8, 0, 0, 4, 0, 2, 4, 1, None),
        'DUPLICATE_ADVICE': (1, 0, 3, 0, 0, 0, 1, 2, 1, (2, 1, 1)),
        'CONFLICT_ADVICE': (6, 1, 0, 0, 2, 0, 0, 1, 1, None),
        'INVALID_POINTER': (7, 5, 0, 0, 0, 0, 0, 1, 1, None),
        'CHECKER_REJECTED': (14, 10, 1, 0, 0, 0, 0, 2, 1, (2, 1, 1)),
        'CHECKER_MISMATCH': (15, 10, 1, 0, 0, 0, 0, 1, 1, (2, 1, 1)),
    }
    for name in names:
        need(tuple(by[name][key] for key in header_keys) == headers[name],
             name + ': extra directed header')

    d = by['DISJOINT_DEFAULT']
    need((d['status'], d['tag'], d['pairs']) == (2, 2, [(3, 4), (6, 7)]),
         'disjoint default status and original pair order')
    need([(e[7], e[3], e[11]) for e in d['events'] if e[0] == 12]
         == [(3, 2, 8), (4, 2, 8), (6, 2, 8), (7, 2, 8)],
         'terminal first-encounter default event order and origins')
    for i in (3, 4, 6, 7):
        need(parser.cell(d, i) == (0, 8, 0), f'defaulted cell {i}')

    same = by['SAME_FIXED_MERGE']
    need((same['status'], same['pairs']) == (2, [(3, 4), (4, 5)]),
         'same fixed component merge')
    need(all(parser.cell(same, i)[2] == 9 for i in (3, 4, 5)),
         'same fixed merged image')
    conflict = by['DIFFERENT_FIXED_MERGE']
    need((conflict['status'], conflict['phase'], conflict['tag'],
          conflict['fi'], conflict['fo'], conflict['steps'])
         == (16, 9, 0, 3, 5, 1), 'non-edge conflict witness')
    need(conflict['pairs'] == [(3, 4), (4, 5)], 'conflict retains pair order')
    need(conflict['events'][-1][0] == 10
         and conflict['events'][-1][7:9] == (3, 5),
         'conflict failure-event witness')

    need(parser.cell(by['INITIAL_FIXED'], 4) == (9, 1, 9),
         'supplied origin preserved')
    need(by['REVERSED_REPEAT']['pairs'] == [(3, 4), (4, 3)],
         'reversed pair retained')
    need(by['SELF_PAIR']['pairs'] == [(2, 2)]
         and not [e for e in by['SELF_PAIR']['events'] if e[0] == 12],
         'self pair has no propagation')
    need((by['SET_THEN_READ']['status'], parser.cell(by['SET_THEN_READ'], 3))
         == (1, (5, 7, 5)), 'late SET propagates before observation')
    read = by['READ_THEN_PAIR']
    need(parser.cell(read, 3) == (0, 5, 0)
         and parser.cell(read, 4) == (0, 7, 0),
         'eager zero propagates when pair arrives')
    early = by['READ_PAIR_SET']
    need((early['status'], early['phase'], early['fi'], early['steps'])
         == (8, 8, 4, 2), 'early eager zero beats later SET')
    need([(e[0], e[7], e[13]) for e in early['events'][-2:]]
         == [(7, 4, 8), (10, 4, 8)],
         'assignment conflict event follows eager propagation')

    need(by['DUPLICATE_ADVICE']['status'] == 1
         and by['CONFLICT_ADVICE']['status'] == 6,
         'duplicate advice compatible/conflicting')
    invalid = by['INVALID_POINTER']
    need((invalid['status'], invalid['phase'], invalid['steps'], invalid['pairs'])
         == (7, 5, 0, []), 'invalid pointer rejects before pair')
    for name, status in [('CHECKER_REJECTED', 14), ('CHECKER_MISMATCH', 15)]:
        c = by[name]
        need((c['status'], c['phase'], c['tag'], c['checker'])
             == (status, 10, 1, (2, 1, 1)), name + ' checker gate')
        need(c['events'][-1][0] == 10 and c['events'][-1][13] == status,
             name + ' failure event')
    print(f'{len(cases)} complete extra envelopes parsed; C/Lean/slow bytes equal')


if __name__ == '__main__':
    main()
