import pickle, glob, sys
pat, out = sys.argv[1], sys.argv[2]
res = []
for f in sorted(glob.glob(pat)):
    with open(f, 'rb') as fh:
        while True:
            try: res.extend(pickle.load(fh))
            except EOFError: break
            except Exception: break
pickle.dump(res, open(out, 'wb')); print(len(res))
