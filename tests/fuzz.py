#!/usr/bin/env python3
"""Random well-typed Kubus programs, checked under --selfcheck, plus ill-typed mutants.

Usage: fuzz.py [--cases N] [--seed S] [--case K] [--keep DIR] [--bin PATH] [--timeout SEC]

Case K of seed S is generated from the random seed "S-K", so a failing case can be
regenerated with `--seed S --case K`. Each case is a file of random definitions over the
library (paths, Σ, Π, Glue, Bool, Nat, Int, S1, Susp, Trunc, hcomp/comp/fill with systems)
and `#eval`s of closed instances. It must be accepted with no self-check violation.
Every mutation site of the case (a flipped path boundary, swapped endpoints, a base that
disagrees with its system, a glue element that disagrees with its base, a type error, a
HIT clause that violates the constructor's boundary) gives a mutant that must be rejected
with an ordinary type error.

Terms are generated well-typed by construction: values of a type at a dimension `x` are
written as `(\\(x : I) -> (w : A)) r`, so path endpoints and system faces never require the
generator to compute normal forms.
"""

import argparse
import os
import random
import re
import subprocess
import sys
import tempfile

# ---------------------------------------------------------------------------
# interval expressions


class I:
    pass


class IConst(I):
    def __init__(self, v):
        self.v = v

    def show(self):
        return str(self.v)

    def subst(self, a):
        return self


class IVar(I):
    def __init__(self, n):
        self.n = n

    def show(self):
        return self.n

    def subst(self, a):
        return IConst(a[self.n]) if self.n in a else self


class INeg(I):
    def __init__(self, r):
        self.r = r

    def show(self):
        return "~" + atomic(self.r)

    def subst(self, a):
        r = self.r.subst(a)
        return IConst(1 - r.v) if isinstance(r, IConst) else INeg(r)


class IBin(I):
    def __init__(self, op, r, s):
        self.op, self.r, self.s = op, r, s

    def show(self):
        return f"({self.r.show()} {self.op} {self.s.show()})"

    def subst(self, a):
        r, s = self.r.subst(a), self.s.subst(a)
        absorb = 0 if self.op == "/\\" else 1
        for x, y in ((r, s), (s, r)):
            if isinstance(x, IConst):
                return IConst(absorb) if x.v == absorb else y
        return IBin(self.op, r, s)


def atomic(r):
    s = r.show()
    return s if isinstance(r, (IConst, IVar)) or s.startswith("(") else f"({s})"


# ---------------------------------------------------------------------------
# types


class Ty:
    def show(self):
        raise NotImplementedError

    def __eq__(self, o):
        return isinstance(o, Ty) and self.show() == o.show()

    def __hash__(self):
        return hash(self.show())


class Data(Ty):
    def __init__(self, n):
        self.n = n

    def show(self):
        return self.n


BOOL, NAT, INT, S1 = Data("Bool"), Data("Nat"), Data("Int"), Data("S1")
SUSP, TRUNC = Data("(Susp Bool)"), Data("(Trunc Bool)")
DATAS = [BOOL, NAT, INT, S1, SUSP, TRUNC]


class Pi(Ty):
    def __init__(self, a, b):
        self.a, self.b = a, b

    def show(self):
        return f"({self.a.show()} -> {self.b.show()})"


class Sig(Ty):
    def __init__(self, a, b):
        self.a, self.b = a, b

    def show(self):
        return f"({self.a.show()} × {self.b.show()})"


class PathT(Ty):
    """`Path A (line 0) (line 1)` for a line `line : (x : I) -> A`; or fixed endpoints."""

    def __init__(self, a, line=None, ends=None):
        self.a, self.line, self.ends = a, line, ends

    def endpoints(self):
        if self.ends:
            return self.ends
        return f"({self.line} 0)", f"({self.line} 1)"

    def show(self):
        l, r = self.endpoints()
        return f"(Path {self.a.show()} {l} {r})"


LOOP = PathT(S1, ends=("base", "base"))
MERID_ENDS = ("north", "south")


class GlueT(Ty):
    """`Glue Bool [φ -> (Bool, e)]` with e = notE or idEquiv Bool."""

    def __init__(self, face, equiv):
        self.face, self.equiv = face, equiv

    def show(self):
        return f"(Glue Bool [{self.face} -> (Bool, {self.equiv})])"


# ---------------------------------------------------------------------------
# generator


class Gen:
    def __init__(self, rnd):
        self.rnd = rnd
        self.counter = 0
        self.sites = []  # (good, bad, kind)
        self.globals = []  # (name, dims, param types, result type)

    def fresh(self, base):
        self.counter += 1
        return f"{base}{self.counter}"

    def site(self, good, bad, kind):
        self.sites.append((good, bad, kind))
        return f"§{len(self.sites) - 1}§"

    def chance(self, p):
        return self.rnd.random() < p

    # interval expressions and faces over the dimensions in scope
    def ival(self, dims, d=2):
        r = self.rnd
        if not dims or (d == 0 and r.random() < 0.3):
            return IConst(r.choice([0, 1]))
        k = r.random()
        if d == 0 or k < 0.5:
            return IVar(r.choice(dims))
        if k < 0.65:
            return INeg(self.ival(dims, d - 1))
        return IBin(r.choice(["/\\", "\\/"]), self.ival(dims, d - 1), self.ival(dims, d - 1))

    def face(self, dims):
        """A face: a list of (dim, 0/1), at least one literal."""
        n = 1 if len(dims) == 1 or self.chance(0.6) else 2
        ds = self.rnd.sample(dims, min(n, len(dims)))
        return [(x, self.rnd.choice([0, 1])) for x in ds]

    @staticmethod
    def showFace(f):
        return " /\\ ".join(f"{x} = {v}" for x, v in f)

    def system(self, dims):
        """Keys of a system: faces (possibly with a disjunction, or `1`)."""
        if not dims:
            return [] if self.chance(0.7) else [("1", {})]
        keys = []
        for _ in range(self.rnd.choice([1, 1, 2, 2, 3])):
            f = self.face(dims)
            keys.append((self.showFace(f), dict(f)))
        if self.chance(0.15):
            f, g = self.face(dims), self.face(dims)
            keys.append((f"{self.showFace(f)} \\/ {self.showFace(g)}", None))
        return keys

    # -- types
    def ty(self, d=2, glue_dims=None):
        r = self.rnd.random()
        if d == 0 or r < 0.55:
            return self.rnd.choice(DATAS + [BOOL, INT])
        if r < 0.67:
            return Pi(self.ty(d - 1), self.ty(d - 1))
        if r < 0.79:
            return Sig(self.ty(d - 1), self.ty(d - 1))
        if r < 0.85:
            return LOOP
        if r < 0.9:
            return PathT(SUSP, ends=MERID_ENDS)
        if glue_dims and r < 0.95:
            return GlueT(self.showFace(self.face(glue_dims)), self.rnd.choice(["notE", "idEquiv Bool"]))
        a = self.rnd.choice(DATAS)
        return PathT(a, line=self.line(a, [], [], 1))

    def line(self, a, vars_, dims, d):
        """`(\\(x : I) -> (w : A))`: a line in `a`."""
        x = self.fresh("x")
        w = self.tm(a, vars_, dims + [x], d)
        return f"(\\({x} : I) -> ({w} : {a.show()}))"

    def flip(self, a, t):
        """A term of type `a` that is never convertible to `t`."""
        return {"Bool": f"(not {t})", "Nat": f"(suc {t})", "Int": f"(sucInt {t})"}.get(a.show())

    # -- terms
    def tm(self, a, vars_, dims, d):
        """A term of type `a` in context (vars_: list of (name, type); dims: list of names)."""
        opts = []  # (weight, thunk)
        same = [x for x, t in vars_ if t == a]
        if same:
            opts.append((3, lambda: self.rnd.choice(same)))
        opts += self.intro(a, vars_, dims, d)
        if d > 0:
            opts += self.elim(a, vars_, dims, d)
        total = sum(w for w, _ in opts)
        k = self.rnd.uniform(0, total)
        for w, f in opts:
            k -= w
            if k <= 0:
                return f()
        return opts[-1][1]()

    def intro(self, a, vars_, dims, d):
        g, r = self, self.rnd
        sub = lambda b, vs=vars_, ds=dims: g.tm(b, vs, ds, d - 1)
        o = []
        if isinstance(a, Data):
            n = a.n
            if n == "Bool":
                o.append((2, lambda: r.choice(["true", "false"])))
                if d > 0:
                    o.append((2, lambda: f"(not {sub(BOOL)})"))
                    o.append((1, lambda: g.site(sub(BOOL), "zero", "type error")))
                    if dims:
                        o.append((2, lambda: (lambda gt: f"(unglue ({sub(gt)} : {gt.show()}))")(GlueT(g.showFace(g.face(dims)), r.choice(['notE', 'idEquiv Bool'])))))
            elif n == "Nat":
                o.append((2, lambda: "zero"))
                if d > 0:
                    o.append((2, lambda: f"(suc {sub(NAT)})"))
                    o.append((1, lambda: f"(add {sub(NAT)} {sub(NAT)})"))
            elif n == "Int":
                o.append((2, lambda: f"(pos {sub(NAT) if d > 0 else 'zero'})"))
                o.append((1, lambda: f"(negsuc {sub(NAT) if d > 0 else 'zero'})"))
                if d > 0:
                    o.append((2, lambda: f"({r.choice(['sucInt', 'predInt'])} {sub(INT)})"))
                    o.append((2, lambda: f"(winding {sub(LOOP)})"))
                    o.append((1, lambda: f"(transport Int Int sucPathInt {sub(INT)})"))
            elif n == "S1":
                o.append((2, lambda: "base"))
                if dims:
                    o.append((2, lambda: f"(loop {atomic(g.ival(dims))})"))
                if d > 0 and dims:
                    o.append((2, lambda: f"(({sub(LOOP)} : {LOOP.show()}) {atomic(g.ival(dims))})"))
            elif n == "(Susp Bool)":
                o.append((2, lambda: r.choice(["north", "south"])))
                if dims and d > 0:
                    o.append((2, lambda: f"(merid {sub(BOOL)} {atomic(g.ival(dims))})"))
                if d > 0:
                    o.append((1, lambda: f"(suspMap Bool Bool not {sub(SUSP)})"))
                    o.append((1, lambda: f"(transport (Susp Bool) (Susp Bool) suspNot {sub(SUSP)})"))
            elif n == "(Trunc Bool)":
                o.append((2, lambda: f"(inc {sub(BOOL) if d > 0 else 'true'})"))
                if dims and d > 0:
                    o.append((2, lambda: f"(squash {sub(TRUNC)} {sub(TRUNC)} {atomic(g.ival(dims))})"))
        elif isinstance(a, Pi):
            def lam():
                x = g.fresh("y")
                return f"(\\{x} -> {g.tm(a.b, vars_ + [(x, a.a)], dims, max(d - 1, 0))})"
            o.append((3, lam))
            if a == Pi(BOOL, BOOL):
                o.append((1, lambda: "not"))
        elif isinstance(a, Sig):
            o.append((3, lambda: f"({g.tm(a.a, vars_, dims, max(d - 1, 0))}, {g.tm(a.b, vars_, dims, max(d - 1, 0))})"))
        elif isinstance(a, PathT):
            o += self.pathIntro(a, vars_, dims, max(d, 1))
        elif isinstance(a, GlueT):
            def glue():
                t = g.tm(BOOL, vars_, dims, max(d - 1, 0))
                if a.equiv == "notE":
                    base = g.site(f"(not {t})", t, "glue base")
                else:
                    base = g.site(t, f"(not {t})", "glue base")
                return f"(glue [{a.face} -> {t}] {base})"
            o.append((3, glue))
        return o

    def pathIntro(self, a, vars_, dims, d):
        g, r = self, self.rnd
        o = []
        i = self.fresh("i")
        if a.line:
            L = a.line
            o.append((3, lambda: f"(\\{i} -> {L} {i})"))
            o.append((1, lambda: f"(\\{i} -> (\\{self.fresh('j')} -> {L} {i}) 0)"))
            k = self.fresh("k")
            o.append((2, lambda: f"(\\{i} -> hcomp {k} {a.a.show()} [{i} = 0 -> {L} 0, {i} = 1 -> {L} 1] ({L} {i}))"))
            o.append((1, lambda: f"(\\{i} -> fill {k} {a.a.show()} [{i} = 0 -> {L} 0, {i} = 1 -> {L} 1] ({L} {i}) {atomic(g.ival(dims + [i]))})"))
        elif a.ends == ("base", "base"):
            sub = lambda b: g.tm(b, vars_, dims, d - 1)
            o.append((2, lambda: r.choice(["loopP", "invLoop", f"(\\{i} -> loop {i})", f"(\\{i} -> base)"])))
            if d > 1:
                o.append((2, lambda: f"(compS1 {sub(LOOP)} {sub(LOOP)})"))
                o.append((1, lambda: f"(sym S1 base base {sub(LOOP)})"))
                o.append((1, lambda: f"(intLoop {sub(INT)})"))
                k = self.fresh("k")
                o.append((1, lambda: f"(\\{i} -> hcomp {k} S1 [{i} = 0 -> base, {i} = 1 -> ({sub(LOOP)} : {LOOP.show()}) {k}] (({sub(LOOP)} : {LOOP.show()}) {i}))"))
        elif a.ends == MERID_ENDS:
            o.append((2, lambda: f"(\\{i} -> merid {g.tm(BOOL, vars_, dims, d - 1)} {i})"))
            o.append((1, lambda: f"(meridP Bool {g.tm(BOOL, vars_, dims, d - 1)})"))
        return o

    def elim(self, a, vars_, dims, d):
        """Generic ways to produce a term of any type."""
        g, r = self, self.rnd
        o = []
        A = a.show()

        def let():
            b = g.ty(1)
            x = g.fresh("z")
            return f"(let {x} : {b.show()} := {g.tm(b, vars_, dims, d - 1)} in {g.tm(a, vars_ + [(x, b)], dims, d - 1)})"
        o.append((1, let))

        def beta():
            b = g.ty(1)
            x = g.fresh("z")
            return f"((\\{x} -> {g.tm(a, vars_ + [(x, b)], dims, d - 1)}) : {b.show()} -> {A}) {g.tm(b, vars_, dims, d - 1)}"
        o.append((1, lambda: f"({beta()})"))

        def proj():
            b = g.ty(1)
            if r.random() < 0.5:
                return f"(({g.tm(Sig(a, b), vars_, dims, d - 1)} : {Sig(a, b).show()}).1)"
            return f"(({g.tm(Sig(b, a), vars_, dims, d - 1)} : {Sig(b, a).show()}).2)"
        o.append((1, proj))

        # application of a function variable
        fns = [(x, t) for x, t in vars_ if isinstance(t, Pi) and t.b == a]
        if fns:
            def appv():
                x, t = r.choice(fns)
                return f"({x} {g.tm(t.a, vars_, dims, d - 1)})"
            o.append((2, appv))

        # a line, applied to an interval expression
        def lineApp():
            L = g.line(a, vars_, dims, d - 1)
            return f"({L} {atomic(g.ival(dims))})"
        o.append((2, lineApp))

        # previously generated global definitions
        gl = [x for x in g.globals if x[3] == a]
        if gl:
            def appg():
                name, nd, ps, _ = r.choice(gl)
                args = [atomic(g.ival(dims)) for _ in range(nd)] + [g.tm(p, vars_, dims, d - 1) for p in ps]
                return f"({' '.join([name] + args)})" if args else name
            o.append((2, appg))

        # homogeneous composition with sides from a square `q : (x k : I) -> A`
        if not isinstance(a, GlueT):
            o.append((2, lambda: g.hcomp(a, vars_, dims, d)))
            o.append((2, lambda: g.comp(a, vars_, dims, d)))
        return o

    def square(self, a, vars_, dims, d):
        x, k = self.fresh("x"), self.fresh("k")
        w = self.tm(a, vars_, dims + [x, k], d - 1)
        return f"(\\({x} : I) ({k} : I) -> ({w} : {a.show()}))"

    def sides(self, q, r, keys, k):
        """System `[φ -> q (r|φ) k]`, with the restriction of `r` to `φ` written out or not."""
        out = []
        for key, assign in keys:
            rr = r.subst(assign) if assign is not None and self.chance(0.5) else r
            out.append(f"{key} -> {q} {atomic(rr)} {k}")
        return out

    def hcomp(self, a, vars_, dims, d):
        q = self.square(a, vars_, dims, d)
        r = self.ival(dims)
        k = self.fresh("k")
        keys = self.system(dims)
        base = f"({q} {atomic(r)} 0)"
        if keys and self.flip(a, base):
            base = self.site(base, self.flip(a, base), "hcomp base")
        sys_ = ", ".join(self.sides(q, r, keys, k))
        if self.chance(0.3):
            # fill, applied at a dimension
            return f"(fill {k} {a.show()} [{sys_}] {base} {atomic(self.ival(dims))})"
        return f"(hcomp {k} {a.show()} [{sys_}] {base})"

    def typeLine(self, a, k):
        """A line of types from `a` to `a`, at dimension `k`."""
        lines = {
            "Bool": [f"notPath {k}", f"ua Bool Bool notE {k}", f"ua Bool Bool (idEquiv Bool) {k}"],
            "Int": [f"sucPathInt {k}", f"helix (loop {k})"],
            "(Susp Bool)": [f"Susp (notPath {k})"],
            "(Trunc Bool)": [f"Trunc (notPath {k})"],
        }
        if isinstance(a, Pi):
            return f"({self.typeLine(a.a, k)} -> {self.typeLine(a.b, k)})"
        if isinstance(a, Sig):
            return f"({self.typeLine(a.a, k)} × {self.typeLine(a.b, k)})"
        if isinstance(a, Data) and a.n in lines and self.chance(0.8):
            return f"({self.rnd.choice(lines[a.n])})"
        return a.show()

    def comp(self, a, vars_, dims, d):
        """`comp k (L k) [φ -> fill m (L m) [] (qa r) k] (qa r)` for a line of types `L`."""
        k, m = self.fresh("k"), self.fresh("m")
        Lk = self.typeLine(a, k)
        Lm = Lk.replace(k, m)
        qa = self.line(a, vars_, dims, d - 1)
        r = self.ival(dims)
        keys = self.system(dims)
        base = f"({qa} {atomic(r)})"
        if keys and self.flip(a, base):
            base = self.site(base, self.flip(a, base), "comp base")
        sys_ = []
        for key, assign in keys:
            rr = r.subst(assign) if assign is not None and self.chance(0.5) else r
            sys_.append(f"{key} -> fill {m} {Lm} [] ({qa} {atomic(rr)}) {k}")
        return f"(comp {k} {Lk} [{', '.join(sys_)}] {base})"

    # -- declarations
    def defn(self, idx):
        name = f"fz{idx}"
        nd = self.rnd.choice([0, 1, 1, 2, 2, 3])
        dims = [self.fresh("i") for _ in range(nd)]
        params = []
        for _ in range(self.rnd.choice([0, 0, 1, 2])):
            params.append((self.fresh("p"), self.ty(1, dims)))
        res = self.ty(2, dims)
        body = self.tm(res, params, dims, self.rnd.choice([2, 3, 3, 4]))
        tyS = res.show()
        if isinstance(res, PathT) and res.line and self.flip(res.a, "x"):
            l, r = res.endpoints()
            tyS = self.site(tyS, f"(Path {res.a.show()} {l} {self.flip(res.a, r)})", "path boundary")
        elif isinstance(res, PathT) and res.ends == MERID_ENDS:
            tyS = self.site(tyS, "(Path (Susp Bool) south north)", "swapped endpoints")
        binders = "".join(f" ({x} : I)" for x in dims) + "".join(f" ({x} : {t.show()})" for x, t in params)
        out = [f"def {name}{binders} : {tyS} :=\n  {body}"]
        mentions_params = isinstance(res, (PathT, GlueT))
        if not mentions_params and not any(isinstance(t, GlueT) for _, t in params):
            self.globals.append((name, nd, [t for _, t in params], res))
        # closed instances
        for _ in range(self.rnd.choice([0, 1, 1, 2])):
            if any(isinstance(t, GlueT) for _, t in params):
                break
            args = [self.rnd.choice(["0", "1"]) for _ in dims] + [self.tm(t, [], [], 2) for _, t in params]
            out.append(f"#eval {' '.join([name] + args)}")
        return "\n".join(out)

    def split(self, idx):
        """A pattern-matching definition on a higher inductive type."""
        name = f"fz{idx}"
        r = self.rnd
        kind = r.choice(["S1Bool", "S1S1", "Susp", "Trunc"])
        i = self.fresh("i")
        if kind == "S1Bool":
            b = self.tm(BOOL, [], [], 2)
            loop = self.site(b, f"(not {b})", "HIT clause boundary")
            src = f"def {name} : S1 -> Bool\n  | base => {b}\n  | loop {i} => {loop}"
            res, arg = BOOL, S1
        elif kind == "S1S1":
            p = self.tm(LOOP, [], [], 2)
            src = f"def {name} : S1 -> S1\n  | base => base\n  | loop {i} => ({p} : {LOOP.show()}) {i}"
            res, arg = S1, S1
        elif kind == "Susp":
            a = self.fresh("a")
            b = self.tm(BOOL, [(a, BOOL)], [], 2)
            m = self.site(f"merid {b} {i}", f"merid {b} (~{i})", "HIT clause boundary")
            src = f"def {name} : Susp Bool -> Susp Bool\n  | north => north\n  | south => south\n  | merid {a} {i} => {m}"
            res, arg = SUSP, SUSP
        else:
            a, x, y = self.fresh("a"), self.fresh("x"), self.fresh("y")
            b = self.tm(BOOL, [(a, BOOL)], [], 2)
            sq = self.site(f"squash ({name} {x}) ({name} {y}) {i}", f"squash ({name} {y}) ({name} {x}) {i}",
                           "HIT clause boundary")
            src = (f"def {name} : Trunc Bool -> Trunc Bool\n  | inc {a} => inc {b}\n"
                   f"  | squash {x} {y} {i} => {sq}")
            res, arg = TRUNC, TRUNC
        self.globals.append((name, 0, [arg], res))
        for _ in range(r.choice([1, 2])):
            src += f"\n#eval {name} {self.tm(arg, [], [], 2)}"
        if r.random() < 0.5:
            j = self.fresh("j")
            src += f"\n#eval \\({j} : I) -> {name} ({self.tm(arg, [], [j], 2)})"
        return src


PRELUDE = """import loopspace
import hits
def notE : Equiv Bool Bool := isoToEquiv Bool Bool not not notnot notnot
"""


def resolve(text, sites, flip=None):
    def rep(m):
        n = int(m.group(1))
        good, bad, _ = sites[n]
        return resolve(bad if n == flip else good, sites, flip)
    return re.sub(r"§(\d+)§", rep, text)


def generate(seed, case, ndefs):
    g = Gen(random.Random(f"{seed}-{case}"))
    parts = []
    for k in range(ndefs):
        parts.append(g.split(k) if g.chance(0.2) else g.defn(k))
    text = PRELUDE + "\n\n".join(parts) + "\n"
    return text, g.sites


def run(bin_, path, timeout, flags):
    env = dict(os.environ)
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    env["KUBUS_PATH"] = os.path.join(root, "lib")
    try:
        p = subprocess.run([bin_] + flags + [path], capture_output=True, text=True, timeout=timeout, env=env)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return None, "timeout"


VIOLATION = re.compile(r"\[(conv-refl|conv-symmetry|roundtrip|recheck|stability)\]")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=20)
    ap.add_argument("--seed", default="0")
    ap.add_argument("--case", type=int, default=None, help="run only this case")
    ap.add_argument("--defs", type=int, default=4, help="definitions per case")
    ap.add_argument("--keep", default=None, help="directory for generated files (default: temporary)")
    ap.add_argument("--bin", default=None)
    ap.add_argument("--timeout", type=float, default=20)
    ap.add_argument("--no-mutants", action="store_true")
    args = ap.parse_args()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    bin_ = args.bin or os.path.join(root, ".lake/build/bin/kubus")
    outdir = args.keep or tempfile.mkdtemp(prefix="kubus-fuzz-")
    os.makedirs(outdir, exist_ok=True)
    cases = [args.case] if args.case is not None else range(args.cases)
    stats = {"cases": 0, "mutants": 0, "fail": 0, "timeout": 0}
    for c in cases:
        text, sites = generate(args.seed, c, args.defs)
        path = os.path.join(outdir, f"fuzz_{args.seed}_{c}.ktt")
        with open(path, "w") as f:
            f.write(resolve(text, sites))
        stats["cases"] += 1
        code, out = run(bin_, path, args.timeout, ["--selfcheck-main"])
        if code is None:
            stats["timeout"] += 1
            print(f"TIMEOUT case {c}: {path}")
            continue
        if code != 0 or VIOLATION.search(out):
            stats["fail"] += 1
            print(f"FAIL case {c} (well-typed program rejected or invariant violated): {path}")
            print("  " + "\n  ".join(out.strip().splitlines()[-12:]))
            continue
        if args.no_mutants:
            continue
        for n, (_, _, kind) in enumerate(sites):
            mtext = resolve(text, sites, flip=n)
            if mtext == resolve(text, sites):
                continue
            mpath = os.path.join(outdir, f"fuzz_{args.seed}_{c}_m{n}.ktt")
            with open(mpath, "w") as f:
                f.write(mtext)
            stats["mutants"] += 1
            code, out = run(bin_, mpath, args.timeout, [])
            if code is None:
                stats["timeout"] += 1
                print(f"TIMEOUT case {c} mutant {n} ({kind}): {mpath}")
            elif code == 0:
                stats["fail"] += 1
                print(f"FAIL case {c} mutant {n} ({kind}): ill-typed program accepted: {mpath}")
            elif "internal" in out or "parse error" in out or VIOLATION.search(out):
                stats["fail"] += 1
                print(f"FAIL case {c} mutant {n} ({kind}): bad rejection: {mpath}")
                print("  " + "\n  ".join(out.strip().splitlines()[-6:]))
            else:
                os.remove(mpath)
    print(f"fuzz seed {args.seed}: {stats['cases']} cases, {stats['mutants']} mutants, "
          f"{stats['fail']} failures, {stats['timeout']} timeouts (files in {outdir})")
    sys.exit(1 if stats["fail"] else 0)


if __name__ == "__main__":
    main()
