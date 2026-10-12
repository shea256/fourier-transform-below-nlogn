"""ccgen.py: a carrier certificate (JSON, schema `carrier-cert/1`) -> a Lean `SSC.CCert`
(Work/CarrierCheck/CCert.lean) plus the kernel-check modules, after a Python MIRROR of the three Lean checks.

usage: ccgen.py <json> <Name> [mirror-only] [--out <dir>]
   writes <dir>/Work/CarrierCheck/Gen/<Name>.lean, <Name>Lab.lean, <Name>Shape.lean, <Name>Scal.lean, <Name>Hist.lean
   and    <dir>/Work/CarrierCheck/<Name>Cert.lean          (default <dir>: tools/gen/out, never the source tree)
   e.g.   ccgen.py tools/certificate/c2-combine-best-h16.json Cr2h16

Format change against the JSON:
  A = F4 ++ F5, B = F6 ++ F7; every part is "old" (all roles have a first label), `F6intro` is dropped;
  an F7 op carries the real piece coefficients; the tables src / pieces / perps / bank are not used;
  the final entries of the y roles become the shift list `ysh`.

The generated Lean files name this script by its path in the tree they were made in
(`checks/wht12/carrier-check/py/ccgen.py`); that text is kept so that the output is byte-identical.
"""
import sys, json, os
from fractions import Fraction

# repository root = two levels above this file (tools/gen/ccgen.py); OUT = where the files are written
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "tools", "gen", "out")
GEN = OUT + "/Work/CarrierCheck/Gen"
M64 = 18446744073709551615


class Par:
    def __init__(s, h, w, d, cnt):
        s.h, s.w, s.d, s.cnt = h, w, d, cnt
        s.K, s.K2, s.K3 = w * h, 2 * w * h, 3 * w * h
        s.hm = (1 << h) - 1
        s.km = sum(1 << ((w - 1) * i) for i in range(h))
        s.mm = sum(1 << (w * i) for i in range(h))
        s.n = 1 << d

    def spread(s, z):
        return ((z & s.hm) * s.km) & s.mm

    def upd(s, L, z):
        zh = s.spread(z)
        return (L ^ (zh ^ (((L & zh) << s.K) ^ ((zh * (z & s.hm)) << s.K2)))) + (s.cnt << s.K3)

    def updS(s, L, z):
        return L ^ (s.spread(z) << s.K)


def enc(L):
    return (L << 64) + (L % M64)


def dec(P):
    return P >> 64


def conv_part(pt):
    if pt[0] == "stay":
        return ("stay", pt[1])
    return ("old", pt[1], list(pt[2]), pt[3])


def coef(num, den):
    return (num < 0, abs(num), den)


def convert(J):
    v, R, h = J["v"], J["R"], J["h"]
    p = J["par"]
    A, B = [], []
    for op in J["F4"] + J["F5"]:
        assert op["coef"] == [1, 1]
        A.append(("bip", [conv_part(x) for x in op["src"]], [conv_part(x) for x in op["tgt"]], []))
    for op in J["F6intro"]:
        assert op["tgt"] == [] and len(op["src"]) == 1 and op["src"][0][2] == [] and op["src"][0][3] == 0
    for op, bk in zip(J["F6"], J["bank"]):
        assert len(op["src"]) == 1 and len(op["tgt"]) == 1
        assert bk == [op["tgt"][0][1], op["src"][0][1]] + op["coef"]
        B.append(("bip", [conv_part(op["src"][0])], [conv_part(op["tgt"][0])], [[coef(*op["coef"])]]))
    assert len(J["F6"]) == len(J["bank"])
    for S, op in enumerate(J["F7"]):
        pcs = J["pieces"][S]
        if op["tgt"]:
            assert [x[1] for x in op["src"]] == [v + q for q, _, _ in pcs], "F7 sources are not the piece rows"
            assert len(op["tgt"]) == 1 and op["tgt"][0][1] == v + R + S
            B.append(("bip", [conv_part(x) for x in op["src"]], [conv_part(op["tgt"][0])],
                      [[coef(n, d) for _, n, d in pcs]]))
        else:
            assert not pcs and len(op["src"]) == 1 and op["src"][0][1] == v + R + S
            B.append(("bip", [conv_part(op["src"][0])], [], []))
    fins = [(r, list(dirs), sh, int(e)) for r, dirs, sh, e in J["fins"]]
    assert [f[0] for f in fins] == list(range(2 * v + R))
    eF = int(J["eF"])
    assert all(f[3] == eF for f in fins)
    ysh = []
    for S in range(v):
        r, dirs, sh, _ = fins[v + R + S]
        assert dirs == [J["trips"][S]]
        ysh.append(sh)
    return dict(par=Par(p["h"], p["w"], p["d"], p["cnt"]), v=v, R=R, trips=list(J["trips"]), A=A, B=B,
                fins=fins[:v + R], ysh=ysh, N=J["N"], ret=list(J["ret"]), retLab=[int(x) for x in J["retLab"]],
                scat=[[(k, coef(n, d)) for k, n, d in row] for row in J["scat"]], eF=eF, h=h)


# ---- mirror of SSC.check (labelCheck) --------------------------------------------------------------------
def mirror_label(D):
    p, v, R = D["par"], D["v"], D["R"]
    n = 2 * v + R
    assert n <= p.n and p.cnt == 1 and 0 < p.h < p.w
    tab = [enc(p.upd(0, z)) for z in D["trips"]] + [0] * (R + v)
    cnt = 0
    ranks = {"x": [], "s": [], "y": []}

    def kind(r):
        return "x" if r < v else ("s" if r < v + R else "y")

    def move(r, dirs, sh):
        nonlocal cnt
        L = dec(tab[r])
        for z in dirs:
            assert z & p.hm, "zero direction"
            L = p.upd(L, z)
        cnt += len(dirs)
        return enc(p.updS(L, sh))

    def part(pt):
        if pt[0] == "stay":
            return tab[pt[1]]
        _, r, dirs, sh = pt
        assert r < n
        tab[r] = move(r, dirs, sh)
        ranks[kind(r)].append(len(dirs))
        return tab[r]

    def run(ops):
        for _, srcs, tgts, _ in ops:
            assert srcs
            ls = [part(x) for x in srcs + tgts]
            assert all(l == ls[0] for l in ls), "gate at unequal labels"

    run(D["A"])
    for k, q in enumerate(D["ret"]):
        assert tab[v + q] == D["retLab"][k], "retained label"
    for S in range(v):
        assert tab[v + R + S] == 0, "a y role moved before the scatter"
    run(D["B"])
    for r, dirs, sh, e in D["fins"]:
        assert move(r, dirs, sh) == e
        ranks[kind(r)].append(len(dirs))
    for S in range(v):
        assert move(v + R + S, [D["trips"][S]], D["ysh"][S]) == D["eF"]
    assert cnt == D["N"], (cnt, D["N"])
    L = dec(D["eF"])
    for i in range(p.h):
        for j in range(p.h):
            assert ((L >> (p.K2 + p.w * i + j)) & 1) == (1 if i == j else 0)
    assert (L >> p.K3) == p.h
    ranks["c"] = [dec(x) >> p.K3 for x in D["retLab"]]
    return ranks


def mirror_shape(D):
    v, R = D["v"], D["R"]
    n = 2 * v + R
    role = lambda pt: pt[1]
    for _, srcs, tgts, _ in D["A"] + D["B"]:
        assert all(role(x) < n for x in srcs + tgts)
        for s in srcs:
            for t in tgts:
                assert role(s) < v + R and v <= role(t) and role(s) != role(t), "illegal gate"
    assert len(D["trips"]) == v == len(D["ysh"]) == len(D["scat"]) and len(D["ret"]) == len(D["retLab"])
    assert all(q < R for q in D["ret"]) and all(k < len(D["ret"]) for row in D["scat"] for k, _ in row)
    assert [f[0] for f in D["fins"]] == list(range(v + R)) and all(f[3] == D["eF"] for f in D["fins"])


def gates_of(D):
    """all gates (t, s, coef) in order: A, scatter, B   (mirror of gatesM / the scatter rows)"""
    v, R = D["v"], D["R"]

    def ops(l):
        for _, srcs, tgts, coefs in l:
            for i, t in enumerate(tgts):
                row = coefs[i] if i < len(coefs) else []
                for j, s in enumerate(srcs):
                    yield t[1], s[1], (row[j] if j < len(row) else (False, 1, 1))

    yield from ops(D["A"])
    for S, row in enumerate(D["scat"]):
        for k, cf in row:
            yield v + R + S, v + D["ret"][k], cf
    yield from ops(D["B"])


def mirror_scalar(D, sw):
    """mirror of CCert.scalarCheck; returns the largest digit met"""
    v, R = D["v"], D["R"]
    y0 = v + R
    tm = sum(1 << (sw * i) for i in range(v)) << (sw - 1)
    P = {i: 1 << (sw * i) for i in range(v)}
    N = {}
    big = 0
    assert sw >= 3
    for t, s, (ng, num, den) in gates_of(D):
        assert s < y0 and t != s
        if t >= y0:
            assert den in (1, 2)
            w = num if den == 2 else 2 * num
        else:
            assert den == 1
            w = num
        ps, ns = P.get(s, 0), N.get(s, 0)
        a, b = (ns, ps) if ng else (ps, ns)
        for acc, add in ((P, a), (N, b)):
            x = acc.get(t, 0)
            for _ in range(w):
                x += add
                assert x & tm == 0, "digit overflow: raise sw"
            acc[t] = x
    for S in range(v):
        assert P.get(y0 + S, 0) == N.get(y0 + S, 0) + (2 << (sw * S)), ("scalar identity fails at target", S)
    mask = (1 << sw) - 1
    for tabl in (P, N):
        for x in tabl.values():
            while x:
                big = max(big, x & mask)
                x >>= sw
    return big


# ---- Lean output -----------------------------------------------------------------------------------------
def lean_list(xs):
    return "[" + ", ".join(xs) + "]"


def lean_part(t):
    if t[0] == "stay":
        return f".stay {t[1]}"
    return f".{t[0]} {t[1]} {lean_list(map(str, t[2]))} {t[3]}"


def lean_coef(c):
    neg, num, den = c
    return f"⟨{'true' if neg else 'false'}, {num}, {den}⟩"


def lean_op(op):
    _, ps, pt, coefs = op
    cs = lean_list(lean_list(map(lean_coef, row)) for row in coefs)
    return f".bip {lean_list(map(lean_part, ps))} {lean_list(map(lean_part, pt))} {cs}"


def lean_fin(fe):
    r, dirs, sh, e = fe
    return f"⟨{r}, {lean_list(map(str, dirs))}, {sh}, {e}⟩"


def chunks(name, typ, items, fmt, size, out):
    names = []
    for i in range(0, len(items), size):
        nm = f"{name}{i // size}"
        names.append(nm)
        out.append(f"noncomputable def {nm} : List {typ} := [\n  " + ",\n  ".join(map(fmt, items[i:i + size])) + "]")
    out.append(f"noncomputable def {name} : List (List {typ}) := {lean_list(names)}")


def hist(ranks):
    allr = ranks["x"] + ranks["s"] + ranks["y"] + ranks["c"]
    top = max(allr)
    return top, [allr.count(r) for r in range(top + 1)]


def write(D, name, sw, ranks, src):
    p = D["par"]
    ns = f"SSC.{name}"
    out = ["import Work.CarrierCheck.CCert",
           f"/-! Carrier certificate (`SSC.CCert`), h = {D['h']}: v = {D['v']} triples, R = {D['R']} helper slots, "
           f"{D['N']} kernel moves\n(the {D['v']} fictitious completions of the y roles included).  Source: {src}.\n"
           "Generated by checks/wht12/carrier-check/py/ccgen.py (do not edit). -/",
           "set_option maxRecDepth 100000", f"namespace {ns}", "open SSC",
           f"def par : Par := ⟨{p.h}, {p.w}, {p.d}, {p.cnt}⟩",
           f"noncomputable def trips : List Nat := {lean_list(map(str, D['trips']))}"]
    chunks("A", "Op", D["A"], lean_op, 150, out)
    chunks("B", "Op", D["B"], lean_op, 150, out)
    chunks("fins", "FinE", D["fins"], lean_fin, 150, out)
    out.append(f"noncomputable def ysh : List Nat := {lean_list(map(str, D['ysh']))}")
    out.append(f"noncomputable def ret : List Nat := {lean_list(map(str, D['ret']))}")
    out.append(f"noncomputable def retLab : List Nat := {lean_list(map(str, D['retLab']))}")
    pair = lambda x: f"({x[0]}, {lean_coef(x[1])})"
    out.append("noncomputable def scat : List (List (Nat × Coef)) := [\n  " +
               ",\n  ".join(lean_list(map(pair, l)) for l in D["scat"]) + "]")
    out.append(f"def eF : Nat := {D['eF']}")
    out.append(f"/-- the certificate -/\nnoncomputable def cert : CCert :=\n  ⟨par, {D['v']}, {D['R']}, {sw}, trips, A, B, "
               f"fins, ysh, {D['N']}, ret, retLab, scat, eF⟩")
    out.append(f"end {ns}\n")
    with open(f"{GEN}/{name}.lean", "w") as fh:
        fh.write("\n".join(out))
    for suffix, fn, doc in (("Lab", "labelCheck", "every gate at one common label; final labels; move count"),
                            ("Shape", "shapeCheck", "shape tests: none into x, none reading y, sizes, final entries"),
                            ("Scal", "scalarCheck", "the scalar identity: every y_S receives exactly x_S")):
        imp = "Work.CarrierCheck.ScalDef\nimport " if suffix == "Scal" else ""
        with open(f"{GEN}/{name}{suffix}.lean", "w") as fh:
            fh.write(f"""import {imp}Work.CarrierCheck.Gen.{name}
/-! Kernel check ({doc}) of the carrier certificate `{ns}.cert`.
Generated by checks/wht12/carrier-check/py/ccgen.py (do not edit). -/
set_option maxRecDepth 100000
namespace {ns}
open SSC
theorem {fn}_ok : cert.{fn} = true := by decide +kernel
end {ns}
#print axioms {ns}.{fn}_ok
""")
    top, cnts = hist(ranks)
    v, R = D["v"], D["R"]
    lines = [f"theorem rankBound_ok : cert.sumW (wGt {top}) = 0 := by decide +kernel"]
    lines += [f"theorem rank{r}_ok : cert.sumW (wEq {r}) = {c} := by decide +kernel" for r, c in enumerate(cnts)]
    for kd, lo, hi in (("X", 0, v), ("S", v, v + R), ("Y", v + R, 2 * v + R)):
        ks = ranks[kd.lower()]
        lines += [f"theorem rank{kd}{r}_ok : cert.sumWK (wEq {r}) {lo} {hi} = {ks.count(r)} := by decide +kernel"
                  for r in range(top + 1) if ks.count(r) or r == 0]
    with open(f"{GEN}/{name}Hist.lean", "w") as fh:
        fh.write(f"""import Work.CarrierCheck.Gen.{name}
/-! Kernel count of the BLOCK RANKS of the carrier certificate `{ns}.cert`: `cert.sumW (wEq r)` blocks of one
invocation (x roles, y roles, slots, scratch copies) have rank `r`, none has rank above {top};
`rankX/S/Y`: the same per role kind (x roles, slots, y roles; rank 0 = empty frame changes, not blocks).
Generated by checks/wht12/carrier-check/py/ccgen.py (do not edit). -/
set_option maxRecDepth 100000
namespace {ns}
open SSC
""" + "\n".join(lines) + f"\nend {ns}\n")
    return top, cnts


def write_cert(D, name, top, cnts, src):
    """interface module Work/CarrierCheck/<Name>Cert.lean (as Work/Linked/Cert16.lean for a PCert)"""
    v, R, h = D["v"], D["R"], D["h"]
    nc = len(D["ret"])
    cst = sum((dec(x) >> D["par"].K3) for x in D["retLab"])
    terms = " + ".join(f"{c} * φ {r}" for r, c in enumerate(cnts) if r and c)
    blocks = ", ".join(f"({r}, {c})" for r, c in enumerate(cnts) if r and c)
    ranks = ", ".join(f"SSC.{name}.rank{r}_ok" for r in range(top + 1))
    moves = sum(r * c for r, c in enumerate(cnts))
    count = sum(c for r, c in enumerate(cnts) if r)
    assert moves == R * h + 2 * v * (h - 1) + cst, (moves, R * h + 2 * v * (h - 1) + cst)
    out = f"""import Work.CarrierCheck.Inv
import Work.CarrierCheck.Gen.{name}Hist
import Work.CarrierCheck.Gen.{name}Lab
import Work.CarrierCheck.Gen.{name}Shape
import Work.CarrierCheck.Gen.{name}Scal

/-!
# (key: carrier-check) Carrier certificate `{name}` (h = {h}): interface for network instances

GENERATED by checks/wht12/carrier-check/py/ccgen.py from {src}.  No `sorry`.

`v = {v}` triples, `R = {R}` helper slots per invocation, {nc} scratch copies, copy cost `cst = {cst}`.
Everything a network instance needs from the certificate `SSC.{name}.cert`:

* `cert`, `valid : cert.Valid`                 (kernel checks `labelCheck`, `shapeCheck`);
* `cert_h`, `cert_v`, `cert_R`, `cert_nc`      (`rfl`);
* `inv : BR.Inv (Fin cert.p.h) (Fin cert.v) (Fin cert.R) (Fin cert.ret.length)`   the invocation package of the
  bridged network: kernel check `scalarCheck` + the carrier invocation theorem (`CR.Phased.inv`);
* `inv_tv`      its lines;
* `inv_cost`    its price = the blocks of ALL roles of ONE invocation (x roles, y roles, helper slots, scratch
                copies), for every price list, from the kernel-counted histogram (`Gen.{name}Hist`);
* `invBlocks`, `inv_cost_list`   the same as a `(rank, count)` list;
* `inv_moves`   these blocks stand for `R h + 2 v (h - 1) + cst = {moves}` unit moves;
* `inv_count`   there are `{count}` of them.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving

namespace Carrier{name}
open Finset Binary Matrix RAM SS CB BR
noncomputable section

/-- the kernel-checked carrier certificate -/
abbrev cert : SSC.CCert := SSC.{name}.cert

/-- the certificate is valid (kernel checks `labelCheck`, `shapeCheck`) -/
theorem valid : cert.Valid :=
  SSC.CCert.Valid.of_checks SSC.{name}.labelCheck_ok SSC.{name}.shapeCheck_ok

theorem cert_h : cert.p.h = {h} := rfl
theorem cert_v : cert.v = {v} := rfl
theorem cert_R : cert.R = {R} := rfl
theorem cert_nc : cert.ret.length = {nc} := rfl

/-- **the invocation package of the certificate** (kernel check `scalarCheck` + `CR.Phased.inv`) -/
def inv : BR.Inv (Fin cert.p.h) (Fin cert.v) (Fin cert.R) (Fin cert.ret.length) :=
  valid.inv SSC.{name}.scalarCheck_ok

theorem inv_tv : inv.tv = cert.tv := rfl

/-- price of the rank list of one invocation, from the kernel-evaluated counts -/
theorem ranks_cost (φ : ℕ → ℝ) :
    rcost φ cert.invRanks = {terms} := by
  rw [SSC.CCert.rcost_sumW cert φ {top} SSC.{name}.rankBound_ok]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, {ranks}]
  norm_num [bcost]

/-- **Price of ONE invocation**: the blocks of all its roles (x, y, helper slots, scratch copies). -/
theorem inv_cost (φ : ℕ → ℝ) :
    inv.cost φ = {terms} := by
  have e : inv.cost φ = rcost φ cert.invRanks := valid.inv_cost SSC.{name}.scalarCheck_ok φ
  rw [e, ranks_cost φ]

/-- the blocks of one invocation, as `(rank, count)` -/
def invBlocks : List (ℕ × ℕ) := [{blocks}]

theorem inv_cost_list (φ : ℕ → ℝ) :
    inv.cost φ = (invBlocks.map fun b => (b.2 : ℝ) * φ b.1).sum := by
  rw [inv_cost φ]
  simp only [invBlocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  try ring

/-- the blocks of one invocation stand for `R h + 2 v (h - 1) + cst` unit moves, `cst = {cst}` -/
theorem inv_moves : inv.cost (fun r => (r:ℝ)) = {R} * {h} + 2 * {v} * ({h} - 1) + {cst} := by
  rw [inv_cost]
  norm_num

/-- number of blocks of one invocation -/
theorem inv_count : inv.cost (fun _ => (1:ℝ)) = {count} := by
  rw [inv_cost]
  norm_num

end

end Carrier{name}

end PowerSaving
end OAI
#print axioms OAI.PowerSaving.Carrier{name}.valid
#print axioms OAI.PowerSaving.Carrier{name}.inv
#print axioms OAI.PowerSaving.Carrier{name}.inv_cost
#print axioms OAI.PowerSaving.Carrier{name}.inv_moves
#check @OAI.PowerSaving.Carrier{name}.inv
#check @OAI.PowerSaving.Carrier{name}.inv_cost
"""
    with open(f"{OUT}/Work/CarrierCheck/{name}Cert.lean", "w") as fh:
        fh.write(out)


if __name__ == "__main__":
    if "--out" in sys.argv:
        i = sys.argv.index("--out")
        OUT = os.path.abspath(sys.argv[i + 1])
        GEN = OUT + "/Work/CarrierCheck/Gen"
        del sys.argv[i:i + 2]
    path, name = sys.argv[1], sys.argv[2]
    J = json.load(open(path))
    assert J["format"] == "carrier-cert/1"
    D = convert(J)
    ranks = mirror_label(D)
    mirror_shape(D)
    sw = 16
    big = mirror_scalar(D, sw)
    blocks = {k: {r: ranks[k].count(r) for r in sorted(set(ranks[k])) if r} for k in "xysc"}
    jb = {k: {int(r): c for r, c in J["blocks"][k].items()} for k in "xysc"}
    print(f"{name}: h={D['h']} v={D['v']} R={D['R']} N={D['N']} ops A={len(D['A'])} B={len(D['B'])} "
          f"mirror label/shape/scalar OK (sw={sw}, largest final digit {big})")
    print("blocks", blocks, "== JSON blocks:", blocks == jb)
    if len(sys.argv) > 3 and sys.argv[3] == "mirror-only":
        sys.exit(0)
    os.makedirs(GEN, exist_ok=True)
    top, cnts = write(D, name, sw, ranks, os.path.basename(path))
    write_cert(D, name, top, cnts, os.path.basename(path))
    print("wrote", name, os.path.getsize(f"{GEN}/{name}.lean"), "bytes; rank histogram", list(enumerate(cnts)))
