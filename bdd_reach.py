#!/usr/bin/env python3
"""EE709 Assignment 1, Part 1: reachable states of the arbiter using ROBDDs.
Self-contained ROBDD package (unique table + ITE + exists + rename), no external library.
Run: python3 bdd_reach.py | tee bdd_run.log

Equations (overbars restored), reset(0)=1 and reset(k>0)=0:
  q0+ = !reset.(r0.!q0 + q0.!g0)   q1+ = !reset.(r1.!q1 + q1.!g1)   p+ = !reset.(p xor (g0+g1))
  g0 = p ? q0.!q1 : q0         g1 = p ? q1 : q1.!q0
"""
import itertools

class BDD:
    def __init__(s):
        s.node = [None, None]          # node id -> (var, lo, hi); ids 0,1 are the constants
        s.uniq, s.memo = {}, {}
    def mk(s, v, lo, hi):
        if lo == hi: return lo         # redundant test removed (reduced)
        k = (v, lo, hi)
        if k not in s.uniq:            # shared nodes (ordered + reduced = canonical)
            s.node.append(k); s.uniq[k] = len(s.node) - 1
        return s.uniq[k]
    def var(s, i): return s.mk(i, 0, 1)
    def lvl(s, u): return 10**9 if u < 2 else s.node[u][0]
    def cof(s, u, v):
        if u < 2 or s.node[u][0] != v: return u, u
        return s.node[u][1], s.node[u][2]
    def ite(s, f, g, h):
        if f == 1: return g
        if f == 0: return h
        if g == h: return g
        if g == 1 and h == 0: return f
        k = ('ite', f, g, h)
        if k in s.memo: return s.memo[k]
        v = min(s.lvl(f), s.lvl(g), s.lvl(h))
        (f0, f1), (g0, g1), (h0, h1) = s.cof(f, v), s.cof(g, v), s.cof(h, v)
        r = s.mk(v, s.ite(f0, g0, h0), s.ite(f1, g1, h1))
        s.memo[k] = r; return r
    def NOT(s, f): return s.ite(f, 0, 1)
    def AND(s, f, g): return s.ite(f, g, 0)
    def OR(s, f, g): return s.ite(f, 1, g)
    def XOR(s, f, g): return s.ite(f, s.NOT(g), g)
    def XNOR(s, f, g): return s.ite(f, g, s.NOT(g))
    def exists(s, f, vs):
        if f < 2: return f
        k = ('ex', f, frozenset(vs))
        if k in s.memo: return s.memo[k]
        v, lo, hi = s.node[f]
        a, b = s.exists(lo, vs), s.exists(hi, vs)
        r = s.OR(a, b) if v in vs else s.mk(v, a, b)
        s.memo[k] = r; return r
    def substitute(s, f, m):           # replace variable i by variable m[i]
        if f < 2: return f
        k = ('sub', f, tuple(sorted(m.items())))
        if k in s.memo: return s.memo[k]
        v, lo, hi = s.node[f]
        r = s.ite(s.var(m.get(v, v)), s.substitute(hi, m), s.substitute(lo, m))
        s.memo[k] = r; return r
    def size(s, f):
        seen, st = set(), [f]
        while st:
            u = st.pop()
            if u > 1 and u not in seen: seen.add(u); st += [s.node[u][1], s.node[u][2]]
        return len(seen)
    def eval(s, f, a):                 # a: var index -> 0/1
        while f > 1: v, lo, hi = s.node[f]; f = hi if a[v] else lo
        return f

B = BDD()
# variable order = creation order: present state, next state, inputs
P, Q0, Q1, Pn, Q0n, Q1n, R0, R1 = range(8)
p, q0, q1, pn, q0n, q1n, r0, r1 = (B.var(i) for i in range(8))

g0 = B.ite(p, B.AND(q0, B.NOT(q1)), q0)
g1 = B.ite(p, q1, B.AND(q1, B.NOT(q0)))
fq0 = B.OR(B.AND(r0, B.NOT(q0)), B.AND(q0, B.NOT(g0)))          # reset = 0
fq1 = B.OR(B.AND(r1, B.NOT(q1)), B.AND(q1, B.NOT(g1)))
fp  = B.XOR(p, B.OR(g0, g1))
T = B.AND(B.AND(B.XNOR(pn, fp), B.XNOR(q0n, fq0)), B.XNOR(q1n, fq1))
print(f"transition relation T: {B.size(T)} BDD nodes")

# reset(0)=1 forces the state after cycle 0 to (p,q0,q1)=(0,0,0)
R = B.AND(B.AND(B.NOT(p), B.NOT(q0)), B.NOT(q1))
quant = {P, Q0, Q1, R0, R1}                   # quantify present state and inputs
back = {Pn: P, Q0n: Q0, Q1n: Q1}              # next-state vars -> present-state vars

def states(f):
    return [(a, b, c) for a, b, c in itertools.product((0, 1), repeat=3)
            if B.eval(f, {P: a, Q0: b, Q1: c})]
it = 0
print(f"R{it}: {len(states(R))} states, {B.size(R)} nodes, {states(R)}")
while True:
    img = B.substitute(B.exists(B.AND(R, T), quant), back)
    Rn = B.OR(R, img); it += 1
    print(f"R{it}: {len(states(Rn))} states, {B.size(Rn)} nodes, {states(Rn)}")
    if Rn == R: break                         # canonical => pointer/id equality test
    R = Rn
print("\nFixpoint reached at iteration", it)
print("R is constant 1 (all 8 states reachable):", R == 1)
print("Reachable (p,q0,q1):", [f"{a}{b}{c}" for a, b, c in states(R)])
