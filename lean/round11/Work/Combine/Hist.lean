import Work.Combine.XCirc

/-!
# (key: combine) The price of the blocks of an invocation from kernel-evaluated counts

`PCert.sumW c wt` (core Lean, `Work.Combine.Ranks`; evaluated by the kernel in the data modules
`Work.Combine.Gen.*Hist`) is `∑ wt (rank)` over the blocks of one invocation:

    PCert.sumW_eq   : c.sumW wt = wsum wt c.invRanks.

With the weights `wEq r` (count the blocks of rank `r`) and `wGt B` (count the blocks of rank
above `B`) this gives the price of the rank list for every price list `φ`:

    PCert.rcost_sumW : c.sumW (wGt B) = 0 →
        rcost φ c.invRanks = ∑ r ∈ range (B+1), (c.sumW (wEq r)) * bcost φ r.

No `sorry`.
-/

namespace SSC
open OAI.PowerSaving.CB Finset

/-- `∑ wt x` over a list -/
def wsum (wt : Nat → Nat) (l : List Nat) : Nat := (l.map wt).sum

theorem wsum_nil (wt : Nat → Nat) : wsum wt [] = 0 := rfl
theorem wsum_cons (wt : Nat → Nat) (a : Nat) (l : List Nat) : wsum wt (a :: l) = wt a + wsum wt l := by
  simp [wsum]
theorem wsum_append (wt : Nat → Nat) (a b : List Nat) : wsum wt (a ++ b) = wsum wt a + wsum wt b := by
  simp [wsum]

theorem lenK_eq {α : Type} (l : List α) : ∀ acc, lenK l acc = acc + l.length := by
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    show lenK l (Nat.succ acc) = _
    rw [ih, List.length_cons]
    omega

theorem moveW_eq (wt : Nat → Nat) (v R r : Nat) (dirs : List Nat) (acc : Nat) :
    moveW wt v (v + R) r dirs acc = acc + wsum wt (moveRanks v R r dirs) := by
  unfold moveW moveRanks
  by_cases h : v ≤ r ∧ r < v + R
  · have h1 : Nat.ble v r = true := Nat.ble_eq_true_of_le h.1
    have h2 : Nat.ble (Nat.succ r) (v + R) = true := Nat.ble_eq_true_of_le h.2
    rw [if_pos h, h1, h2]
    show acc + wt (lenK dirs 0) = acc + wsum wt [dirs.length]
    rw [lenK_eq, Nat.zero_add, wsum_cons, wsum_nil, Nat.add_zero]
  · rw [if_neg h, wsum_nil, Nat.add_zero]
    cases h1 : Nat.ble v r with
    | false => rfl
    | true =>
      cases h2 : Nat.ble (Nat.succ r) (v + R) with
      | false => rfl
      | true => exact absurd ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩ h

theorem partW_eq (wt : Nat → Nat) (v R : Nat) (pt : Part) (acc : Nat) :
    partW wt v (v + R) pt acc = acc + wsum wt (pt.ranks v R) := by
  cases pt with
  | old r dirs sh => exact moveW_eq wt v R r dirs acc
  | new r dirs sh => exact moveW_eq wt v R r dirs acc
  | stay r => rfl

theorem partsW_eq (wt : Nat → Nat) (v R : Nat) (pts : List Part) :
    ∀ acc, partsW wt v (v + R) pts acc = acc + wsum wt (pts.flatMap (Part.ranks v R)) := by
  induction pts with
  | nil => intro acc; rfl
  | cons pt pts ih =>
    intro acc
    show forceN (partW wt v (v + R) pt acc) (partsW wt v (v + R) pts) = _
    rw [forceN_eq, ih, partW_eq, List.flatMap_cons, wsum_append]
    omega

theorem opW_eq (wt : Nat → Nat) (v R : Nat) (op : Op) (acc : Nat) :
    opW wt v (v + R) op acc = acc + wsum wt (op.ranks v R) := by
  cases op with
  | bip srcs tgts coefs =>
    show partsW wt v (v + R) tgts (partsW wt v (v + R) srcs acc)
      = acc + wsum wt ((srcs ++ tgts).flatMap (Part.ranks v R))
    rw [partsW_eq, partsW_eq, List.flatMap_append, wsum_append]
    omega
  | copy s d => rfl
  | copyNew s d => rfl
  | erase d => rfl
  | expect r e => rfl

theorem opsW_eq (wt : Nat → Nat) (v R : Nat) (ops : List Op) :
    ∀ acc, opsW wt v (v + R) ops acc = acc + wsum wt (opsRanks v R ops) := by
  induction ops with
  | nil => intro acc; rfl
  | cons op ops ih =>
    intro acc
    show forceN (opW wt v (v + R) op acc) (opsW wt v (v + R) ops) = _
    rw [forceN_eq, ih, opW_eq]
    show _ = acc + wsum wt ((op :: ops).flatMap (Op.ranks v R))
    rw [List.flatMap_cons, wsum_append]
    show acc + wsum wt (op.ranks v R) + wsum wt (ops.flatMap (Op.ranks v R)) = _
    omega

theorem chunksW_eq (wt : Nat → Nat) (v R : Nat) (cs : List (List Op)) :
    ∀ acc, chunksW wt v (v + R) cs acc = acc + wsum wt (opsRanks v R cs.flatten) := by
  induction cs with
  | nil => intro acc; rfl
  | cons ops cs ih =>
    intro acc
    show forceN (opsW wt v (v + R) ops acc) (chunksW wt v (v + R) cs) = _
    rw [forceN_eq, ih, opsW_eq]
    show _ = acc + wsum wt ((ops ++ cs.flatten).flatMap (Op.ranks v R))
    rw [List.flatMap_append, wsum_append]
    show acc + wsum wt (ops.flatMap (Op.ranks v R)) + wsum wt (cs.flatten.flatMap (Op.ranks v R)) = _
    omega

theorem finsW_eq (wt : Nat → Nat) (v R : Nat) (fs : List FinE) :
    ∀ acc, finsW wt v (v + R) fs acc = acc + wsum wt (finsRanks v R fs) := by
  induction fs with
  | nil => intro acc; rfl
  | cons fe fs ih =>
    intro acc
    show forceN (finW wt v (v + R) fe acc) (finsW wt v (v + R) fs) = _
    rw [forceN_eq, ih]
    have e : finW wt v (v + R) fe acc = acc + wsum wt (fe.ranks v R) :=
      moveW_eq wt v R fe.r fe.dirs acc
    rw [e]
    show _ = acc + wsum wt ((fe :: fs).flatMap (FinE.ranks v R))
    rw [List.flatMap_cons, wsum_append]
    show acc + wsum wt (fe.ranks v R) + wsum wt (fs.flatMap (FinE.ranks v R)) = _
    omega

theorem finChunksW_eq (wt : Nat → Nat) (v R : Nat) (fs : List (List FinE)) :
    ∀ acc, finChunksW wt v (v + R) fs acc = acc + wsum wt (finsRanks v R fs.flatten) := by
  induction fs with
  | nil => intro acc; rfl
  | cons fl fs ih =>
    intro acc
    show forceN (finsW wt v (v + R) fl acc) (finChunksW wt v (v + R) fs) = _
    rw [forceN_eq, ih, finsW_eq]
    show _ = acc + wsum wt ((fl ++ fs.flatten).flatMap (FinE.ranks v R))
    rw [List.flatMap_append, wsum_append]
    show acc + wsum wt (fl.flatMap (FinE.ranks v R)) + wsum wt (fs.flatten.flatMap (FinE.ranks v R)) = _
    omega

theorem cenW_eq (wt : Nat → Nat) (p : Par) (ls : List Nat) :
    ∀ acc, cenW wt p ls acc = acc + wsum wt (ls.map fun L => cntOf p (dec L)) := by
  induction ls with
  | nil => intro acc; rfl
  | cons L ls ih =>
    intro acc
    show forceN (Nat.add acc (wt (cntOf p (dec L)))) (cenW wt p ls) = _
    rw [forceN_eq, ih, List.map_cons, wsum_cons]
    show acc + wt (cntOf p (dec L)) + _ = _
    omega

/-- **the kernel-evaluated sum is the sum over the rank list of one invocation** -/
theorem PCert.sumW_eq (c : PCert) (wt : Nat → Nat) : c.sumW wt = wsum wt c.invRanks := by
  show cenW wt c.p c.retLab (finChunksW wt c.v (c.v + c.R) c.fins
    (chunksW wt c.v (c.v + c.R) c.F7 (chunksW wt c.v (c.v + c.R) c.F5
      (chunksW wt c.v (c.v + c.R) c.F4 0)))) = _
  rw [cenW_eq, finChunksW_eq, chunksW_eq, chunksW_eq, chunksW_eq]
  simp only [PCert.invRanks, PCert.ranks4, PCert.ranks5, PCert.ranks7, PCert.ranksF,
    PCert.cenRanks, wsum_append, Nat.zero_add]

theorem wEq_apply (r n : Nat) : wEq r n = if n = r then 1 else 0 := by
  show Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq n r) = _
  by_cases h : n = r
  · subst h; rw [if_pos rfl, Nat.beq_refl]
  · rw [if_neg h]
    have hb : Nat.beq n r = false := by
      cases hb : Nat.beq n r with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [hb]

theorem wGt_apply (B n : Nat) : wGt B n = if n ≤ B then 0 else 1 := by
  show Bool.rec (motive := fun _ => Nat) 1 0 (Nat.ble n B) = _
  by_cases h : n ≤ B
  · rw [if_pos h, Nat.ble_eq_true_of_le h]
  · rw [if_neg h]
    have hb : Nat.ble n B = false := by
      cases hb : Nat.ble n B with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [hb]

theorem wsum_wEq (r : Nat) (l : List Nat) : wsum (wEq r) l = l.count r := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wsum_cons, ih, wEq_apply, List.count_cons]
    by_cases h : a = r
    · simp [h]; omega
    · simp [h]

theorem wsum_wGt (B : Nat) (l : List Nat) (h : wsum (wGt B) l = 0) : ∀ x ∈ l, x ≤ B := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    rw [wsum_cons, wGt_apply] at h
    intro x hx
    rcases List.mem_cons.mp hx with e | e
    · rw [e]
      by_contra hc
      rw [if_neg hc] at h
      omega
    · exact ih (by omega) x e

/-- the price of a rank list is the price of its counts -/
theorem rcost_count (φ : ℕ → ℝ) (l : List ℕ) (B : ℕ) (hB : ∀ x ∈ l, x ≤ B) :
    rcost φ l = ∑ r ∈ range (B+1), (l.count r : ℝ) * bcost φ r := by
  induction l with
  | nil => simp [rcost_nil]
  | cons a l ih =>
    have ha : a ≤ B := hB a (List.mem_cons_self ..)
    rw [rcost_cons, ih (fun x hx => hB x (List.mem_cons_of_mem _ hx))]
    have e : ∀ r, ((List.count r (a :: l) : ℕ) : ℝ) * bcost φ r
        = (l.count r : ℝ) * bcost φ r + (if a = r then bcost φ r else 0) := by
      intro r
      rw [List.count_cons]
      by_cases h : a = r
      · simp [h]; ring
      · simp [h]
    simp_rw [e]
    rw [sum_add_distrib, sum_ite_eq (range (B+1)) a (fun r => bcost φ r)]
    simp only [mem_range.mpr (Nat.lt_succ_of_le ha), if_true]
    ring

/-- **the price of the blocks of one invocation from the kernel-evaluated counts** -/
theorem PCert.rcost_sumW (c : PCert) (φ : ℕ → ℝ) (B : ℕ) (hB : c.sumW (wGt B) = 0) :
    rcost φ c.invRanks = ∑ r ∈ range (B+1), (c.sumW (wEq r) : ℝ) * bcost φ r := by
  rw [c.sumW_eq] at hB
  rw [rcost_count φ c.invRanks B (wsum_wGt B _ hB)]
  refine sum_congr rfl (fun r _ => ?_)
  rw [c.sumW_eq, wsum_wEq]

end SSC

#print axioms SSC.PCert.sumW_eq
#print axioms SSC.PCert.rcost_sumW
