import Work.Combine.XG

/-!
# (key: bridge-377) The idle blocks of the data of one port over the 8 replicas (PR #377)

Credits: the compressed nine-stage layout, its banks and padding are jacklightChen's (CrocSwap/integer-mult-bounds
PR #377); the bridged word B_K is DaysSky's (PR #363); B_2, the engine, the stage geometry and the E8 unit are Jacob
Sussman's (wht-power-saving-lean, Apache-2.0).  Written by w-bridge3/gen377/gen377.py (from genk.py).

Per role and replica (X and Y, h = 9): the first idle climbs 16, 32, 48 and the window climbs 8, 8, 8 of pairs
2..4, the finals 48, 32, 16 of pairs 1..3 (pair 4 ends at rank 0).
-/

namespace OAI
namespace PowerSaving
namespace GX
open CB
noncomputable section

/-- idle climbs of the data of ONE port over all 8 replicas, X and Y (h = 9). -/
def bankPrice377 (φ : ℕ → ℝ) : ℝ :=
  16 * (2 * bcost φ 48 + 2 * bcost φ 32 + 2 * bcost φ 16 + 3 * bcost φ 8)

end
end GX
end PowerSaving
end OAI
