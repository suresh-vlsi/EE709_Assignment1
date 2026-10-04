#!/usr/bin/env python3
"""EE709 Assignment 1, Part 2: bounded SAT checks of the arbiter (PySAT + MiniSat).

Run:  python3 arbiter_sat.py | tee sat_run.log
Also writes DIMACS files (cnf/*.cnf) so you can run `minisat file.cnf` directly.
Assumed equations (overbars restored):
  q0+ = !reset.(r0.!q0 + q0.!g0)    q1+ = !reset.(r1.!q1 + q1.!g1)
  p+  = !reset.(p xor (g0+g1))
  g0  = p ? q0.!q1 : q0         g1  = p ? q1 : q1.!q0
"""
import os, sys
from pysat.formula import IDPool, CNF
from pysat.solvers import Minisat22

N = 8  # window: cycles k = 0..7

class Enc:
    def __init__(self, p_zero=False):
        self.pool, self.cnf = IDPool(), CNF()
        v = self.v = lambda name, k: self.pool.id((name, k))
        self.T = self.pool.id('TRUE'); self.cnf.append([self.T])
        for k in range(N):
            for n in ('r0', 'r1', 'q0', 'q1', 'p'):
                v(n, k)
        self.g = {}
        for k in range(N):
            q0, q1, p, r0, r1 = (v(n, k) for n in ('q0', 'q1', 'p', 'r0', 'r1'))
            # g0 = p ? q0.!q1 : q0 ; g1 = p ? q1 : q1.!q0
            g0 = self.MUX(p, self.AND(q0, -q1), q0)
            g1 = self.MUX(p, q1, self.AND(q1, -q0))
            self.g[k] = (g0, g1)
            if p_zero:
                self.cnf.append([-p])               # modified circuit: p(k)=0 for all k
            if k + 1 < N:
                if k == 0:                           # reset(0)=1 -> next state all 0
                    for n in ('q0', 'q1', 'p'):
                        self.cnf.append([-v(n, 1)])
                else:                                # reset(k)=0
                    self.EQ(v('q0', k+1), self.OR(self.AND(r0, -q0), self.AND(q0, -g0)))
                    self.EQ(v('q1', k+1), self.OR(self.AND(r1, -q1), self.AND(q1, -g1)))
                    if not p_zero:                   # in the modified circuit p is fixed, no update
                        self.EQ(v('p', k+1), self.XOR(p, self.OR(g0, g1)))
    # --- Tseitin gates ---
    def new(self): return self.pool.id(('t', self.pool.top + 1))
    def AND(self, a, b):
        z = self.new(); self.cnf.extend([[-z, a], [-z, b], [z, -a, -b]]); return z
    def OR(self, a, b):
        z = self.new(); self.cnf.extend([[z, -a], [z, -b], [-z, a, b]]); return z
    def XOR(self, a, b):
        z = self.new(); self.cnf.extend([[-z, a, b], [-z, -a, -b], [z, -a, b], [z, a, -b]]); return z
    def MUX(self, s, a, b):                          # s ? a : b
        z = self.new(); self.cnf.extend([[-s, -a, z], [-s, a, -z], [s, -b, z], [s, b, -z]]); return z
    def EQ(self, a, b): self.cnf.extend([[-a, b], [a, -b]])

def run(enc, name, assumptions):
    s = Minisat22(bootstrap_with=enc.cnf.clauses)
    sat = s.solve(assumptions=assumptions)
    m = set(s.get_model()) if sat else None
    s.delete()
    return sat, m

def trace(enc, m):
    b = lambda x: int(x in m)
    print("      k : r0 r1 | p q0 q1 | g0 g1")
    for k in range(N):
        v, g = enc.v, enc.g[k]
        print(f"      {k} :  {b(v('r0',k))}  {b(v('r1',k))} | {b(v('p',k))}  {b(v('q0',k))}  {b(v('q1',k))} |  {b(g[0])}  {b(g[1])}")

def dump(enc, fname):
    os.makedirs('cnf', exist_ok=True); enc.cnf.to_file('cnf/' + fname)

def check_response(enc, c, ks, label, show=True):
    """Violation of r_c(k) => F g_c : r_c(k) & !g_c(j) for all j in k..N-1."""
    print(f"  {label}")
    for k in ks:
        a = [enc.v(f'r{c}', k)] + [-enc.g[j][c] for j in range(k, N)]
        sat, m = run(enc, label, a)
        print(f"    k={k}: {'SAT  (violation found)' if sat else 'UNSAT (no violation)'}")
        if sat and show:
            trace(enc, m); show = False

if __name__ == '__main__':
    E = Enc()
    dump(E, 'base_unrolled.cnf')
    print("=== Property (c): not EF(g0.g1), cycles 0..7 ===")
    for k in range(N):
        sat, m = run(E, 'c', [E.g[k][0], E.g[k][1]])
        print(f"  k={k}: {'SAT (g0.g1 reachable)' if sat else 'UNSAT'}")
    for c, tag in ((0, 'a'), (1, 'b')):
        print(f"\n=== Property ({tag}): AG(r{c} => F g{c}) ===")
        check_response(E, c, [0], f"({tag}) k=0 (reset cycle, request is discarded)")
        check_response(E, c, range(1, 6), f"({tag}) k=1..5 (grant due by k+2 <= 7)")
        check_response(E, c, range(6, 8), f"({tag}) k=6..7 (grant may fall outside window)")
    print("\n=== Part 2: p(k)=0 for all k, AG(r1 => F g1) ===")
    E0 = Enc(p_zero=True); dump(E0, 'p_zero_unrolled.cnf')
    check_response(E0, 1, range(1, 6), "(2) k=1..5")
