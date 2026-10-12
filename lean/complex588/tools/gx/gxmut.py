"""gxmut.py: mutation test of the Python mirror: every mutant must be REJECTED.
usage: gxmut.py <gcert1.json[.gz]>"""
import sys, copy
import gxpaths
import gxcore as gc

c0 = gc.load(sys.argv[1])
h, v = c0['h'], c0['v']


def m_coef(c):      # flip the sign of the last add of B (an x-carrying delivery)
    g = c['B'][-1]; g[3][-1][1] = -g[3][-1][1]
def m_coefA(c):     # double a coefficient of an early gate of A
    c['A'][0][3][0][1] *= 2
def m_frame(c):     # a gate of B at a frame that does not contain the register's frame
    c['B'][len(c['B']) // 2][1] = 2
def m_final(c):     # a y role ends at the full frame
    c['final'][v] = 1
def m_table(c):     # a frame-table entry that is not reduced
    f = c['frames'][-1]; f[0] ^= f[-1] if len(f) > 1 else 1 << (h + 1)
def m_port(c):      # an even port
    c['ports'][0] ^= 1 << (c['ports'][0].bit_length() - 1)
def m_kind(c):      # a gate of A writing a y role
    c['A'][0][3][0][0] = v
def m_ret(c):       # a retained slot at another frame
    c['ret'][0][2] = 1 if c['ret'][0][2] != 1 else 0
def m_blocks(c):    # a wrong price
    k = next(iter(c['blocks']['s'])); c['blocks']['s'][k] += 1
def m_drop(c):      # a gate of B removed
    del c['B'][len(c['B']) // 3]
def m_scat(c):      # scatter coefficient changed
    if 'table' in c['scat']: c['scat']['table'][0][0][1] *= -1
    else: c['scat']['inside'] = [1, 2]
def m_N(c):
    c['N'] += 1


bad = 0
for f in (m_coef, m_coefA, m_frame, m_final, m_table, m_port, m_kind, m_ret, m_blocks, m_drop, m_scat, m_N):
    c = copy.deepcopy(c0)
    f(c)
    try:
        gc.mirror(gc.normal(c))
        print('ACCEPTED (BAD):', f.__name__); bad += 1
    except gc.Reject as e:
        print('rejected %-9s %s' % (f.__name__, str(e)[:90]))
print('%s: %d mutants, %d wrongly accepted' % (sys.argv[1].split('/')[-1], 12, bad))
