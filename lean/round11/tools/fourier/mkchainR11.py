#!/usr/bin/env python3
"""mkchainR11.py -- modified copy of tools/fourier/mkchain233.py of github.com/chafreaky/wht-power-saving-lean
(commit fd19e46, Apache-2.0), made for shea256/fourier-transform-below-nlogn: only the constants, names and comments
below differ.  mkchain.py for Jain's round-eleven circuit: Work/FourierR11/<11 files>, Goal.lean and the comparator challenge,
suffix X, seam Work.FourierR11.Seam (kernel program of the circuit of Swapnil Jain's round-eleven word at 1 - 7150885/10^10), exponent 1 - 6700000/10^10.
Only the constants below differ from mkchain.py (diff the two files).

usage: mkchain.py <seam module> [--only NAME ...]
  <seam module> is the module that replaces OpenAI's TensorProgram import in the first copied file:
  Work.FourierR11.Seam.

What it does (nothing else):
  * every declaration of the 11 copied OpenAI files gets the suffix X on its last name component,
    and every occurrence of such a component in the 11 files is renamed with it;
  * the 9 seam names (hills, alpha, ...) are renamed to the seam's names (hillsX, alphaX, ...);
  * the 5 statement names of OpenAI's Goal.lean that depend on the exponent get the suffix X;
  * imports of copied files point to Work.FourierR11.*; the TensorProgram import points to the seam;
  * per-file literal patches listed in PATCHES (each must match exactly the stated number of times).
OpenAI's files are only read.
"""
import re, sys, os, json

V = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # the repository root
FT = V + "/OAI/Computability/FourierTransform"
OUT = os.environ.get("FOURIER_OUT") or os.path.join(__import__("tempfile").gettempdir(), "fourier-out")
# (never the repository files themselves: tools/fourier/regen_check.py compares the output with them)
os.makedirs(OUT, exist_ok=True)
HERE = OUT

COPIED = ["SectorAlgorithm", "SynchronizedAlgorithm", "WorkingTransform", "WorkingCompiler",
          "WorkingPreparation", "ArbitraryLength", "TransformProgram", "ConvolutionProgram",
          "UniformBounds", "Asymptotics", "Main"]
SUF = "X"
SEAM = {"hills": "hillsX", "alpha": "alphaX", "hills_pos": "hillsX_pos", "hills_mono": "hillsX_mono",
        "hills_le": "hillsX_le", "hills_real": "hillsX_real", "alpha_pos": "alphaX_pos",
        "alpha_lt": "alphaX_lt", "hills_program": "hillsX_program"}
GOAL = ["decimalExponent", "decimalTime", "TimeBounds", "DFTGoal", "ConvGoal"]
THEOREMS = ["transform_main", "convolution_main"]
OLD_EXP = "1 - 1/(10^(13:ℕ))"
NEW_EXP = "1 - 6700000/(10^(10:ℕ))"

# literal per-file patches applied AFTER renaming: (old, new, expected count, reason)
PATCHES = {
    "Main": [
        ("let d : ℝ := 2/(10:ℝ)^11", "let d : ℝ := 7150885/(10:ℝ)^10", 1,
         "alpha_thetaX: the local constant d must equal 1 - alphaX"),
        ("theorem transform_mainX : DFTGoalX :=",
         "/-- **The discrete Fourier transform of every length in `O(n (log n)^(1 - 6700000/10^10))`.**\n"
         "OpenAI's `transform_main` (one fixed program, OpenAI's own `DFTProgram`, `paperTime` and `nlogn`)\n"
         "with the decimal exponent `1 - 1/10^13` replaced by `decimalExponentX = 1 - 6700000/10^10`\n"
         "(Work/FourierR11/Goal.lean). Sibling of the Walsh-Hadamard theorem `wht_main_block_B2GR11x`: both\n"
         "follow from one kernel program, `RAM.hillsX_program` (Work/FourierR11/Seam.lean). -/\n"
         "theorem transform_mainX : DFTGoalX :=", 1, "docstring added"),
        ("theorem convolution_mainX : ConvGoalX :=",
         "/-- **Convolution of every length with the same bounds** (OpenAI's `convolution_main`, same change). -/\n"
         "theorem convolution_mainX : ConvGoalX :=", 1, "docstring added"),
    ],
}

# Per-file qualification of names. A copied file sees a larger environment than OpenAI's original did
# (all of OpenAI's files and ours are imported through the seam), so a few short names that the original
# reached through `open` are now shadowed by a different declaration in an enclosing namespace.
# (file -> {short name: qualified name}); applied to tokens not preceded by a dot.
QUALIFY = {
    "SynchronizedAlgorithm": {"canopy": "Grove.canopy"},
}

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class|opaque)\s+([^\s:({\[]+)", re.M)
TOKEN = re.compile(r"[^\W\d][\w']*")


def declared(text):
    """fully qualified names (namespace stack tracked) of the declarations of a file"""
    st, out = [], []
    for l in text.split("\n"):
        m = re.match(r"^\s*namespace\s+(\S+)", l)
        if m:
            st.append(m.group(1)); continue
        if re.match(r"^\s*(noncomputable\s+)?section\b", l):
            st.append(None); continue
        if re.match(r"^\s*end\b", l) and st:
            st.pop(); continue
        m = DECL.match(l)
        if m:
            out.append(".".join([x for x in st if x] + [m.group(1)]))
    return out


def rename(text, mp):
    return TOKEN.sub(lambda m: mp.get(m.group(0), m.group(0)), text)


def main():
    seam = sys.argv[1]
    only = sys.argv[sys.argv.index("--only") + 1:] if "--only" in sys.argv else COPIED + ["Goal", "Challenge"]
    src = {c: open(f"{FT}/{c}.lean", encoding="utf-8").read() for c in COPIED}
    # A declaration needs the suffix on its last component unless an enclosing namespace component is
    # itself a declaration of the copied files directly under ...Bench (a structure or Prop-valued def
    # such as `Weft`): then the renamed parent already makes the full name new (`WeftZ.transfer`).
    alld = [(c, full) for c in COPIED for full in declared(src[c])]
    fullset = {full for _, full in alld}
    keys, kept = {}, {}
    for c, full in alld:
        parts = full.split(".")
        parent_renamed = any(".".join(parts[:i]) in fullset for i in range(1, len(parts)))
        (kept if parent_renamed else keys).setdefault(parts[-1], []).append(f"{c}:{full}")
    both = sorted(set(keys) & set(kept))
    assert not both, both
    mp = {k: k + SUF for k in keys}
    for k in SEAM:
        assert k not in mp, k
    mp.update(SEAM)
    for k in GOAL:
        assert k not in mp, k
        mp[k] = k + SUF
    # report: keys that are also declared (as a last component) in OpenAI files that are NOT copied
    other = {}
    for f in sorted(os.listdir(FT)):
        if f.endswith(".lean") and f[:-5] not in COPIED:
            for full in declared(open(f"{FT}/{f}", encoding="utf-8").read()):
                other.setdefault(full.split(".")[-1], []).append(f"{f[:-5]}:{full}")
    clash = {k: (keys[k], other[k]) for k in keys if k in other}
    newclash = {k: other[mp[k]] for k in mp if mp[k] in other}
    json.dump({"map": mp, "declared": keys, "kept_under_renamed_parent": kept,
               "also_declared_in_uncopied_files": clash,
               "new_name_already_exists": newclash},
              open(f"{HERE}/rename-map.json", "w"), indent=1, ensure_ascii=False)
    print(f"{len(keys)} declared names; {len(clash)} share a last component with an uncopied file; "
          f"{len(newclash)} new names already exist")
    os.makedirs(OUT, exist_ok=True)
    for c in COPIED:
        if c not in only:
            continue
        t = src[c]
        lines = t.split("\n")
        body_start = 0
        imports = []
        while lines[body_start].startswith("import "):
            mod = lines[body_start][7:].strip()
            base = mod.split(".")[-1]
            if mod == "OAI.Computability.FourierTransform.TensorProgram":
                imports.append(f"import {seam}")
            elif mod.startswith("OAI.Computability.FourierTransform.") and base in COPIED:
                imports.append(f"import Work.FourierR11.{base}")
            else:
                imports.append(lines[body_start])
            body_start += 1
        if c == "Main":
            imports.append("import Work.FourierR11.Goal")
        body = rename("\n".join(lines[body_start:]), mp)
        notes = []
        for short, qual in QUALIFY.get(c, {}).items():
            body, cnt = re.subn(r"(?<![\w.'])" + re.escape(short) + r"(?![\w'])", qual, body)
            assert cnt > 0, (c, short)
            notes.append(f"  * `{short}` written `{qual}` ({cnt} places): in the larger environment of this copy the"
                         " short name is shadowed by another declaration")
        for old, new, cnt, why in PATCHES.get(c, []):
            assert body.count(old) == cnt, (c, old, body.count(old))
            body = body.replace(old, new)
            notes.append(f"  * `{old}`: {why}" if new.endswith(old) else f"  * literal `{old}` -> `{new}` ({why})")
        hdr = [
            "/-",
            f"Modified copy of lean/OAI/Computability/FourierTransform/{c}.lean of github.com/openai/math",
            "(commit fd4aeeb, Apache-2.0), generated by `tools/fourier/mkchainR11.py`. OpenAI's file itself is",
            "unmodified in this repository and still imported. Changed for this repository, all mechanically:",
            f"  * every declaration of this file (and of the other 10 copied files) has the suffix `{SUF}`",
            "    on its name, so that it does not collide with OpenAI's original;",
            "  * OpenAI's exponent `alpha = 1 - 2/10^11` and envelope `hills` are replaced by",
            "    `alphaX = 1 - 7150885/10^10` and `hillsX` (Work/FourierR11/Seam.lean), and the single use of",
            "    OpenAI's `hills_program` by `hillsX_program`;",
            "  * `decimalExponent`, `decimalTime`, `TimeBounds`, `DFTGoal`, `ConvGoal` are replaced by their",
            "    `X` versions from Work/FourierR11/Goal.lean (exponent `1 - 6700000/10^10`);",
            "  * imports point to the copies.",
        ] + notes + [
            "Comments and docstrings below are OpenAI's and describe OpenAI's network, not ours.",
            "-/",
        ]
        open(f"{OUT}/{c}.lean", "w", encoding="utf-8").write(
            "\n".join(imports) + "\n\n" + "\n".join(hdr) + "\n" + body)
    if "Goal" in only:
        g = open(f"{FT}/Goal.lean", encoding="utf-8").read().split("\n")

        def block(start_pat, nlines):
            i = next(k for k, l in enumerate(g) if l.startswith(start_pat))
            return g[i:i + nlines]
        parts = (block("def decimalExponent", 1) + [""] + block("def decimalTime", 1) + [""]
                 + block("/-- Thm 1 (intro main)", 4) + [""] + block("def DFTGoal", 1) + [""]
                 + block("def ConvGoal", 1))
        gm = {k: k + SUF for k in GOAL}
        txt = rename("\n".join(parts), gm)
        assert txt.count(OLD_EXP) == 1
        txt = txt.replace(OLD_EXP, NEW_EXP)
        hdr = f"""import OAI.Computability.FourierTransform.Goal

/-
Modified copy of five definitions of lean/OAI/Computability/FourierTransform/Goal.lean of
github.com/openai/math (commit fd4aeeb, Apache-2.0; lines 30, 35, 75-78, 80, 82), generated by
`tools/fourier/mkchain.py`. Changed for this repository:
  * the exponent `{OLD_EXP}` is replaced by `{NEW_EXP}`;
  * the five names have the suffix `X` (OpenAI's own definitions keep their names and values).
Everything else they mention (`paperTime`, `nlogn`, `DFTProgram`, `ConvProgram`) is OpenAI's own,
imported unmodified.
-/

namespace OAI

namespace PowerSaving
noncomputable section
open RAM RAM.Ty Filter Asymptotics

"""
        open(f"{OUT}/Goal.lean", "w", encoding="utf-8").write(hdr + txt + "\n\nend\nend PowerSaving\n\nend OAI\n")
    if "Challenge" in only:
        ch = open(f"{V}/third-party/openai-math/lean/ComparatorChallenges/UniformFourier.lean", encoding="utf-8").read()
        cm = {k: k + SUF for k in GOAL + THEOREMS}
        new = rename(ch, cm)
        assert new.count(OLD_EXP) == 1
        new = new.replace(OLD_EXP, NEW_EXP)
        head = "import Mathlib\n"
        assert new.startswith(head)
        comment = f"""
/-
Comparator challenge. Modified copy of lean/ComparatorChallenges/UniformFourier.lean of
github.com/openai/math (commit fd4aeeb, Apache-2.0), generated by `tools/fourier/mkchainR11.py`.
Changed for this repository, exactly:
  1. this comment;
  2. the exponent: `{OLD_EXP}` is replaced by `{NEW_EXP}`;
  3. seven names have the suffix `X`: {', '.join(GOAL + THEOREMS)}.
     (Forced: the proof imports OpenAI's unmodified files, where these names already carry
     OpenAI's values, and the comparator requires same-named constants to agree.)
Every other byte is OpenAI's. The two `sorry`s are the statements to be proved.
-/
"""
        open(f"{OUT}/UniformFourierChallenge.lean", "w", encoding="utf-8").write(head + comment + new[len(head):])
        json.dump({
            "challenge_module": "Work.FourierR11.UniformFourierChallenge",
            "solution_module": "Work.FourierR11.Main",
            "theorem_names": ["OAI.PowerSaving.transform_mainX", "OAI.PowerSaving.convolution_mainX"],
            "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": False,
        }, open(f"{OUT}/UniformFourierR11.json", "w"), indent=2)
        open(f"{OUT}/UniformFourierR11.json", "a").write("\n")


main()
print("written to " + OUT)
