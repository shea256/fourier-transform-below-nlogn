"""Render the README chart of the exact-DFT record progression (Matplotlib 3.9.4).

Order, values, players, times and evidence levels follow the leaderboard at
https://bigospeedrun.com/exact-dft (retrieved 2026-10-10).
"""
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

ROOT = Path(__file__).resolve().parents[1] / 'assets'
# (x label in PT, player, construction, exact score, displayed delta, evidence)
# Evidence: 'lean' = Lean verified on the leaderboard; 'checked' = listed as Claimed there,
# with exact finite certificates passing `python3 verification/run_checks.py` in this repository;
# 'leanrepo' = listed as Claimed there, with a Lean proof in lean/round11 that passes the official comparator locally.
ROWS = [
    ('Oct 6', 'OpenAI', 'Published headline', '1/10000000000000', '1e-13', 'lean'),
    ('Oct 7\n10:20 PM', 'OpenAI', 'Uniform frontier', '1/50000000000', '2e-11 \u2212 \u03b5', 'lean'),
    ('Oct 8\n4:56 PM', 'Ryan Shea', 'Two-stage network', '73/1000000', '7.3e-5', 'checked'),
    ('Oct 9\n2:34 AM', 'eumemic', 'Batched paired-cube', '607/1250000', '4.85e-4 \u2212 \u03b5', 'claimed'),
    ('Oct 9\n8:24 AM', 'Ryan Shea', 'Retired-copy network', '67/100000', '6.7e-4', 'leanrepo'),
    ('Oct 9\n12:00 PM', 'Jacob Sussman', 'Five-stage framework', '3737273/5000000000', '7.47e-4', 'claimed'),
    ('Oct 9\n6:43 PM', 'Sussman & Boukhalfa', 'Five-stage network', '47171/62500000', '7.54e-4', 'lean'),
    ('Oct 10\n3:44 PM', 'Jacob Sussman', 'E8 unit', '4381239/5000000000', '8.76e-4', 'lean'),
    ('Oct 11\n6:07 AM', 'Nil Mamano', 'Nine-stage certificate', '2555269/2500000000', '1.0221e-3', 'lean'),
]
ys = [float(Fraction(r[3])) for r in ROWS]
assert ys == sorted(ys), 'each leaderboard entry should improve the record'
assert ys[-1] == 0.0010221076
evidence = [r[5] for r in ROWS]
gray, blue, green = '#555555', '#2d7dd2', '#19aa80'
ink, muted, faint = '#1a1a1a', '#6b6b6b', '#9a9a9a'
L = .085  # shared left margin for all figure text
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 13, 'mathtext.fontset': 'dejavusans'})
fig, ax = plt.subplots(figsize=(16, 9), dpi=180, facecolor='white')
fig.subplots_adjust(left=L + .015, right=.955, bottom=.32, top=.80)
fig.text(L, .935, 'Exact Fourier transform: increasing the exponent saving',
         fontsize=24, color=ink, va='top', fontweight='semibold')
fig.text(L, .862, r'$T(n) = O\left(n\,(\log n)^{1-\delta}\right)$   ·   larger $\delta$ means a stronger asymptotic bound',
         fontsize=15, color=muted, va='top')
ax.set_yscale('log')
ax.set_ylim(3e-14, .03)
ax.set_xlim(-.35, 8.4)
ax.set_yticks([1e-13, 1e-11, 1e-9, 1e-7, 1e-5, 1e-3])
ax.set_yticklabels([rf'$10^{{{e}}}$' for e in (-13, -11, -9, -7, -5, -3)])
ax.set_ylabel(r'Exponent saving $\delta$ (log scale)', labelpad=12, color=muted)
ax.grid(axis='y', color='#ececec', linewidth=1)
ax.set_axisbelow(True)
for side in ['top', 'right', 'left']:
    ax.spines[side].set_visible(False)
ax.spines['bottom'].set_color('#cfcfcf')
ax.tick_params(axis='both', length=0, colors=muted, pad=10)
ax.set_xticks(range(len(ROWS)))
ax.set_xticklabels([r[0] for r in ROWS], fontsize=11.5, linespacing=1.4)
n = len(ROWS)
ax.step(range(n), ys, where='post', color=blue, lw=2.5, zorder=2, solid_joinstyle='round')
for i in range(n):
    if evidence[i] == 'lean':
        ax.scatter([i], [ys[i]], s=140, color=green, edgecolors='white', linewidths=2, zorder=4)
    elif evidence[i] == 'leanrepo':
        ax.scatter([i], [ys[i]], s=120, color=blue, edgecolors=green, linewidths=2.5, zorder=4)
    elif evidence[i] == 'checked':
        ax.scatter([i], [ys[i]], s=140, color=blue, edgecolors='white', linewidths=2, zorder=4)
    else:
        ax.scatter([i], [ys[i]], s=110, facecolors='white', edgecolors=gray, linewidths=2.5, zorder=4)

def label(i, dx, dy, ha='left', va='bottom'):
    _, player, name, _, value, level = ROWS[i]
    color = {'lean': green, 'leanrepo': blue, 'checked': blue, 'claimed': gray}[level]
    ax.annotate(f'{player}\n{name}\n' + '\u03b4 = ' + value, xy=(i, ys[i]), xytext=(dx, dy),
                textcoords='offset points', fontsize=10.6, color=color, ha=ha, va=va, linespacing=1.4,
                arrowprops=dict(arrowstyle='-', color=color, lw=.8, shrinkA=2, shrinkB=6) if dy < -40 else None,
                fontweight='semibold' if i == n - 1 else 'normal')

label(0, -6, 16)
label(1, -6, 16)
label(2, 10, -16, va='top')
label(3, 8, -16, va='top')
label(4, 8, -74, va='top')
label(5, 8, -16, va='top')
label(6, 8, -74, va='top')
label(7, 8, -16, va='top')
label(8, 6, 16, ha='right')
ax.legend(handles=[
    Line2D([], [], marker='o', color=green, markeredgecolor='white', linestyle='none', markersize=10, label='Lean verified'),
    Line2D([], [], marker='o', color=blue, markeredgecolor=green, markeredgewidth=2.5, linestyle='none', markersize=10, label='Lean proof in this repo (lean/round11), official comparator passes; leaderboard lists Claimed'),
    Line2D([], [], marker='o', color=blue, markeredgecolor='white', linestyle='none', markersize=10, label='Machine-checked finite certificates in this repo; not in Lean'),
    Line2D([], [], marker='o', color=gray, markerfacecolor='white', markeredgewidth=2, linestyle='none', markersize=8, label='Claimed')],
    loc='lower right', bbox_to_anchor=(1.0, 0.04), frameon=False, fontsize=11.5, labelcolor=muted,
    handletextpad=.4, borderaxespad=0)

notes = [
    ('Model: exact complex arithmetic · supplied root of unity · unrestricted coefficients · unit-cost logarithmic-word indexing. '
     'Scalar preparation and array organization included.', muted),
    ('Values are exponent parameters, not measured speedups. Lean and Claimed levels as listed by the leaderboard; \u2212 \u03b5 marks a strict bound.', muted),
    ('Fourier applications and integration: Ryan Shea / this project.', muted),
    ('Upstream formal framework: Jacob Sussman · stronger circuit/program: Chafik Boukhalfa', muted),
    ('Circuit lineage: icekylinx, eumemic, an664, Avi Eisenberg · composition/ledger: Henry Grant, SovereignSteak', muted),
    ('Full credits: CrocSwap/integer-mult-bounds/CONTRIBUTORS.md · beyond-n-log-n.netlify.app', muted),
]
y = .218
for k, (text, color) in enumerate(notes):
    fig.text(L, y, text, fontsize=10.5, color=color)
    y -= .029 if k != 1 else .041
fig.text(L, .016, 'github.com/shea256/fourier-transform-below-nlogn  ·  Order, values and times (PT): bigospeedrun.com/exact-dft, checked Oct 12, 2026',
         fontsize=10, color=faint)
fig.savefig(ROOT / 'fourier-exponent-progress.png', dpi=180, facecolor='white')
print('Saved assets/fourier-exponent-progress.png (2880 × 1620).')
