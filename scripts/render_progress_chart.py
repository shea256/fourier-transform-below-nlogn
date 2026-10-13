"""Render the exact-DFT history and this repository's new bound (Matplotlib 3.9.4).

Historical entries follow https://bigospeedrun.com/exact-dft (checked 2026-10-12).
The final point is the locally verified complex588 result, published in PR #4
at 2026-10-12 19:40 UTC (12:40 PM PT); leaderboard verification is outstanding.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

ROOT = Path(__file__).resolve().parents[1] / 'assets'
# (date in PT, contributor, construction, exact score, strict endpoint, evidence)
# Evidence: 'lean' = Lean verified on the leaderboard; 'checked' = listed as Claimed there,
# with exact finite certificates passing `python3 verification/run_checks.py` in this repository;
# 'leanrepo' = local official-comparator, Lean and nanoda checks passed; the
# leaderboard lists round11 as Claimed and has no entry for complex588 yet.
ROWS = [
    ('Oct 6', 'OpenAI', 'Initial bound', '1/10000000000000', False, 'lean'),
    ('Oct 7\n10:20 PM', 'OpenAI', 'Uniform bound', '1/50000000000', True, 'lean'),
    ('Oct 8\n4:56 PM', 'Ryan Shea', 'Two-stage network', '73/1000000', False, 'checked'),
    ('Oct 9\n2:34 AM', 'eumemic', 'Paired-cube batching', '607/1250000', True, 'claimed'),
    ('Oct 9\n8:24 AM', 'Ryan Shea', 'Retired-copy network', '67/100000', False, 'leanrepo'),
    ('Oct 9\n12:00 PM', 'Jacob Sussman', 'Five-stage framework', '3737273/5000000000', False, 'claimed'),
    ('Oct 9\n6:43 PM', 'Jacob Sussman & Chafik Boukhalfa', 'Five-stage network', '47171/62500000', False, 'lean'),
    ('Oct 10\n3:44 PM', 'Jacob Sussman', 'E8 unit', '4381239/5000000000', False, 'lean'),
    ('Oct 11\n6:07 AM', 'Nil Mamano', 'Nine-stage certificate', '2555269/2500000000', False, 'lean'),
    ('Oct 12\n12:40 PM', 'Ryan Shea', 'PR588 with cyclic banks', '12331685/10000000000', False, 'leanrepo'),
]
scores = [Fraction(r[3]) for r in ROWS]
assert all(a < b for a, b in zip(scores, scores[1:])), 'each point should improve the bound'
registry = json.loads((ROOT.parent / 'results/registry.json').read_text())
current = next(r for r in registry['results'] if r['id'] == registry['current'])
assert current['id'] == 'complex588', 'update the chart for the new selected result'
assert scores[-1] == Fraction(current['fourier_saving'])
ys = [float(score) for score in scores]
evidence = [r[5] for r in ROWS]
gray, blue, green = '#555555', '#2d7dd2', '#19aa80'
ink, muted, faint = '#1a1a1a', '#6b6b6b', '#9a9a9a'
L = .085  # shared left margin for all figure text
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 13, 'mathtext.fontset': 'dejavusans'})
fig, ax = plt.subplots(figsize=(16, 7.2), dpi=180, facecolor='white')
fig.subplots_adjust(left=L + .015, right=.955, bottom=.15, top=.77)
fig.text(L, .935, 'Exact Fourier transform: exponent savings',
         fontsize=24, color=ink, va='top', fontweight='semibold')
fig.text(L, .862, r'$T(n) = O\left(n\,(\log n)^{1-\delta}\right)$   ·   Larger $\delta$ gives a stronger bound',
         fontsize=15, color=muted, va='top')
ax.set_yscale('log')
ax.set_ylim(3e-14, .03)
ax.set_xlim(-.35, len(ROWS) - .6)
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

def format_saving(score, strict):
    """Round labels to four significant digits; plot the full rational scores."""
    with localcontext() as context:
        context.prec = 40
        value = Decimal(score.numerator) / Decimal(score.denominator)
        mantissa, exponent = f'{value:.3E}'.split('E')
    endpoint = r' - \varepsilon' if strict else ''
    return rf'$\delta \approx {mantissa} \times 10^{{{int(exponent)}}}{endpoint}$'


def label(i, dx, dy, ha='left', va='bottom'):
    _, player, name, _, strict, level = ROWS[i]
    color = {'lean': green, 'leanrepo': blue, 'checked': blue, 'claimed': gray}[level]
    value = format_saving(scores[i], strict)
    ax.annotate(f'{player}\n{name}\n{value}', xy=(i, ys[i]), xytext=(dx, dy),
                textcoords='offset points', fontsize=10.6, color=color, ha=ha, va=va, linespacing=1.4,
                arrowprops=dict(arrowstyle='-', color=color, lw=.8, shrinkA=2, shrinkB=6) if dy < -40 else None,
                fontweight='normal')

label(0, -6, 16)
label(1, 6, 16, ha='right')
label(2, -6, 16)
label(3, 8, -16, va='top')
label(4, 8, -74, va='top')
label(5, 8, -16, va='top')
label(6, 8, -74, va='top')
label(7, 8, -16, va='top')
label(8, 8, -74, va='top')
label(9, 6, 16, ha='right')
ax.legend(handles=[
    Line2D([], [], marker='o', color=green, markeredgecolor='white', linestyle='none', markersize=10, label='Lean verified (leaderboard)'),
    Line2D([], [], marker='o', color=blue, markeredgecolor=green, markeredgewidth=2.5, linestyle='none', markersize=10, label='Lean verified (local)'),
    Line2D([], [], marker='o', color=blue, markeredgecolor='white', linestyle='none', markersize=10, label='Finite checks (local)'),
    Line2D([], [], marker='o', color=gray, markerfacecolor='white', markeredgewidth=2, linestyle='none', markersize=8, label='Claimed')],
    loc='lower right', bbox_to_anchor=(1.0, 0.04), frameon=False, fontsize=11.5, labelcolor=muted,
    handletextpad=.4, borderaxespad=0)

# Model details, display conventions and contributor credits live in the README.
fig.text(L, .025, 'bigospeedrun.com/exact-dft + this repo · Oct 12, 2026 · Local results await leaderboard verification.',
         fontsize=10, color=faint)
fig.savefig(ROOT / 'fourier-exponent-progress.png', dpi=180, facecolor='white')
print('Saved assets/fourier-exponent-progress.png (2880 × 1296).')
