import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Basic

/-!
# (key: carrier-thm) The dirt rule as an identity in a (noncommutative) ring

`px`, `py` are orthogonal idempotents (the coordinate projectors on the x roles and on the y
roles; `ps := 1 - px - py` is the projector on the helper slots), `m` is the product of ALL gates
of the main phase and `mi` its inverse, with

    px * m = px      no gate INTO an x role  (the x rows of `m` are unit rows),
    m * py = py      no gate READS a y role  (the y columns of `m` are unit columns).

* `dirt_fwd`:  `g8 * m * g1 = 1 + py * m * px`,  where
      `g1 = 1 - py * m * ps`             (`y -= K s`: the dirt is subtracted in advance),
      `g8 = px + py + ps * mi`           (the slot rows of `m⁻¹`: every gate into a slot undone);
* `dirt_bwd`:  `g1i * mi * h8 = 1 - py * m * px`,  where `g1i = 1 + py * m * ps` and
      `h8 = px + py + ps * m` are the inverses of `g1`, `g8` (the backward word is the
      transposed inverse, gate by gate).

So the whole word is the shear `1 + py * m * px` as soon as the block `py * m * px` (what the y
roles receive from the x roles in the main phase) is the identity block.

No `sorry`.
-/

namespace OAI
namespace PowerSaving
namespace CR

section
variable {R : Type*} [Ring R] {px py m mi : R}

lemma dirt_xi (xm : px * m = px) (mi' : m * mi = 1) : px * mi = px := by
  calc px * mi = (px * m) * mi := by rw [xm]
    _ = px * (m * mi) := mul_assoc _ _ _
    _ = px := by rw [mi', mul_one]

lemma dirt_iy (my : m * py = py) (im : mi * m = 1) : mi * py = py := by
  calc mi * py = mi * (m * py) := by rw [my]
    _ = (mi * m) * py := (mul_assoc _ _ _).symm
    _ = py := by rw [im, one_mul]

/-- **The dirt rule, forward.** -/
theorem dirt_fwd (xx : px * px = px) (yy : py * py = py) (xy : px * py = 0) (yx : py * px = 0)
    (xm : px * m = px) (my : m * py = py) (im : mi * m = 1) (mi' : m * mi = 1) :
    (px + py + (1 - px - py) * mi) * m * (1 - py * m * (1 - px - py)) = 1 + py * m * px := by
  have xi := dirt_xi xm mi'
  have iy := dirt_iy my im
  have xx' : ∀ z, px * (px * z) = px * z := fun z => by rw [← mul_assoc, xx]
  have yy' : ∀ z, py * (py * z) = py * z := fun z => by rw [← mul_assoc, yy]
  have xy' : ∀ z, px * (py * z) = 0 := fun z => by rw [← mul_assoc, xy, zero_mul]
  have yx' : ∀ z, py * (px * z) = 0 := fun z => by rw [← mul_assoc, yx, zero_mul]
  have xm' : ∀ z, px * (m * z) = px * z := fun z => by rw [← mul_assoc, xm]
  have my' : ∀ z, m * (py * z) = py * z := fun z => by rw [← mul_assoc, my]
  have im' : ∀ z, mi * (m * z) = z := fun z => by rw [← mul_assoc, im, one_mul]
  have mi'' : ∀ z, m * (mi * z) = z := fun z => by rw [← mul_assoc, mi', one_mul]
  have xi' : ∀ z, px * (mi * z) = px * z := fun z => by rw [← mul_assoc, xi]
  have iy' : ∀ z, mi * (py * z) = py * z := fun z => by rw [← mul_assoc, iy]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_zero, zero_mul,
    mul_assoc, xx, yy, xy, yx, xm, my, im, mi', xi, iy, xx', yy', xy', yx', xm', my', im',
    mi'', xi', iy', sub_zero, add_zero, zero_add]
  abel

/-- **The dirt rule, backward** (the inverse of the forward product). -/
theorem dirt_bwd (xx : px * px = px) (yy : py * py = py) (xy : px * py = 0) (yx : py * px = 0)
    (xm : px * m = px) (my : m * py = py) (im : mi * m = 1) (mi' : m * mi = 1) :
    (1 + py * m * (1 - px - py)) * mi * (px + py + (1 - px - py) * m) = 1 - py * m * px := by
  have xi := dirt_xi xm mi'
  have iy := dirt_iy my im
  have xx' : ∀ z, px * (px * z) = px * z := fun z => by rw [← mul_assoc, xx]
  have yy' : ∀ z, py * (py * z) = py * z := fun z => by rw [← mul_assoc, yy]
  have xy' : ∀ z, px * (py * z) = 0 := fun z => by rw [← mul_assoc, xy, zero_mul]
  have yx' : ∀ z, py * (px * z) = 0 := fun z => by rw [← mul_assoc, yx, zero_mul]
  have xm' : ∀ z, px * (m * z) = px * z := fun z => by rw [← mul_assoc, xm]
  have my' : ∀ z, m * (py * z) = py * z := fun z => by rw [← mul_assoc, my]
  have im' : ∀ z, mi * (m * z) = z := fun z => by rw [← mul_assoc, im, one_mul]
  have mi'' : ∀ z, m * (mi * z) = z := fun z => by rw [← mul_assoc, mi', one_mul]
  have xi' : ∀ z, px * (mi * z) = px * z := fun z => by rw [← mul_assoc, xi]
  have iy' : ∀ z, mi * (py * z) = py * z := fun z => by rw [← mul_assoc, iy]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_zero, zero_mul,
    mul_assoc, xx, yy, xy, yx, xm, my, im, mi', xi, iy, xx', yy', xy', yx', xm', my', im',
    mi'', xi', iy', sub_zero, add_zero, zero_add]
  abel

end

/-! ### side identities: the unit rows and columns of the four dirt gates -/
section Side
variable {R : Type*} [Ring R] {px py : R}

lemma side_cx (xx : px * px = px) (xy : px * py = 0) : px * (1 - px - py) = 0 := by
  rw [mul_sub, mul_sub, mul_one, xx, xy, sub_self, sub_zero]

lemma side_cy (yy : py * py = py) (yx : py * px = 0) : py * (1 - px - py) = 0 := by
  rw [mul_sub, mul_sub, mul_one, yx, yy, sub_zero, sub_self]

lemma side_xc (xx : px * px = px) (yx : py * px = 0) : (1 - px - py) * px = 0 := by
  rw [sub_mul, sub_mul, one_mul, xx, yx, sub_self, sub_zero]

lemma side_yc (yy : py * py = py) (xy : px * py = 0) : (1 - px - py) * py = 0 := by
  rw [sub_mul, sub_mul, one_mul, xy, yy, sub_zero, sub_self]

/-- `n = py * w * ps` is killed by `px` on the left. -/
lemma side_n_left (xy : px * py = 0) (w : R) : px * (py * w * (1 - px - py)) = 0 := by
  rw [mul_assoc, ← mul_assoc, xy, zero_mul]

/-- `n = py * w * ps` is killed by `px` on the right. -/
lemma side_n_right (xx : px * px = px) (yx : py * px = 0) (w : R) :
    py * w * (1 - px - py) * px = 0 := by
  rw [mul_assoc, side_xc xx yx, mul_zero]

/-- `px + py + ps * w` has unit x rows. -/
lemma side_g_x (xx : px * px = px) (xy : px * py = 0) (w : R) :
    px * (px + py + (1 - px - py) * w) = px := by
  rw [mul_add, mul_add, xx, xy, add_zero, ← mul_assoc, side_cx xx xy, zero_mul, add_zero]

/-- `px + py + ps * w` has unit y rows. -/
lemma side_g_y (yy : py * py = py) (yx : py * px = 0) (w : R) :
    py * (px + py + (1 - px - py) * w) = py := by
  rw [mul_add, mul_add, yx, yy, zero_add, ← mul_assoc, side_cy yy yx, zero_mul, add_zero]

/-- `px + py + ps * w` has unit y columns when `w` has. -/
lemma side_g_ycol (yy : py * py = py) (xy : px * py = 0) {w : R} (hw : w * py = py) :
    (px + py + (1 - px - py) * w) * py = py := by
  rw [add_mul, add_mul, xy, yy, zero_add, mul_assoc, hw, side_yc yy xy, add_zero]

end Side
end CR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CR.dirt_fwd
#print axioms OAI.PowerSaving.CR.dirt_bwd
