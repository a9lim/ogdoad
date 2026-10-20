import json, collections, sys
f = sys.argv[1] if len(sys.argv) > 1 else 'results_ref.jsonl'
d = [json.loads(l) for l in open(f)]
print(len(d), 'rows done; max p', max(x['p'] for x in d), '; sum1/p', round(sum(1/x['p'] for x in d), 4))
print('counterexamples', [x for x in d if x.get('COUNTEREXAMPLE')])
print('not forced_ok', [x['p'] for x in d if not x['forced_ok']])
print(collections.Counter(x['arm'] for x in d))
s = sorted(d, key=lambda x: -x['secs'])[:5]; print('slowest', [(x['p'], x['E'], x['secs']) for x in s])
ps = sorted(x['p'] for x in d); first_gap = next((p for p in ps if p > 727), None)
