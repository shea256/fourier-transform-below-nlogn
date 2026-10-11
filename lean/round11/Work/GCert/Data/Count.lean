import Work.Combine.Ranks

/-!
# (key: gx-data) Kernel-friendly rank counts on explicit rank lists

Core Lean only.  `GXD.wsumK wt l acc = acc + ∑ wt x` with the accumulator forced at every step
(`SSC.forceN`), so that `decide +kernel` evaluates it on lists of tens of thousands of ranks without
deep recursion.  `wsumK_eq` turns a kernel count into `(l.map wt).sum`, which is `SSC.wsum wt l`
(`Work/Combine/Hist.lean`) by `rfl`.  Weights: `SSC.wEq r`, `SSC.wGt B` (`Work/Combine/Ranks.lean`).
-/

namespace GXD

/-- `acc + ∑ wt x` over the list, accumulator forced at every step -/
noncomputable def wsumK (wt : Nat → Nat) (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih acc => SSC.forceN (Nat.add acc (wt a)) ih) l

theorem forceN_eq {α : Type} (n : Nat) (k : Nat → α) : SSC.forceN n k = k n := by
  cases n <;> rfl

theorem wsumK_nil (wt : Nat → Nat) (acc : Nat) : wsumK wt [] acc = acc := rfl

theorem wsumK_cons (wt : Nat → Nat) (a : Nat) (l : List Nat) (acc : Nat) :
    wsumK wt (a :: l) acc = wsumK wt l (acc + wt a) := by
  show SSC.forceN (Nat.add acc (wt a)) (wsumK wt l) = _
  rw [forceN_eq]
  rfl

/-- **the kernel count is the sum of the weights** -/
theorem wsumK_eq (wt : Nat → Nat) (l : List Nat) : ∀ acc, wsumK wt l acc = acc + (l.map wt).sum := by
  induction l with
  | nil => intro acc; simp [wsumK_nil]
  | cons a l ih => intro acc; rw [wsumK_cons, ih]; simp [Nat.add_assoc]

/-- a kernel count from zero, as a sum -/
theorem sum_of_wsumK {wt : Nat → Nat} {l : List Nat} {n : Nat} (h : wsumK wt l 0 = n) :
    (l.map wt).sum = n := by
  rw [wsumK_eq] at h
  simpa using h

end GXD

#print axioms GXD.wsumK_eq
#print axioms GXD.sum_of_wsumK
