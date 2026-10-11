import Work.CarrierCheck.Valid

/-!
# (key: carrier-check) The live roles of a carrier certificate as a type

`c.Rl = (Fin v ⊕ Fin v) ⊕ Fin R`: the x roles, the y roles, the helper slots (this is
`CR.L3 (Fin v) (Fin R)` of `Work.Carrier`), with the role numbers of the certificate:
`x_t ↦ t`, `y_S ↦ v + R + S`, slot `q ↦ v + q`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

namespace CCert
variable (c : CCert)

/-- the live roles: x, y, slots -/
abbrev Rl : Type := (Fin c.v ⊕ Fin c.v) ⊕ Fin c.R

def emb3 : c.Rl → Nat
  | .inl (.inl t) => t.val
  | .inl (.inr S) => c.v + c.R + S.val
  | .inr q => c.v + q.val

def unemb3 (hv : 0 < c.v) (hR : 0 < c.R) (r : Nat) : c.Rl :=
  if r < c.v then .inl (.inl ⟨r % c.v, Nat.mod_lt _ hv⟩)
  else if r < c.v + c.R then .inr ⟨(r - c.v) % c.R, Nat.mod_lt _ hR⟩
  else .inl (.inr ⟨(r - c.v - c.R) % c.v, Nat.mod_lt _ hv⟩)

theorem emb3_lt (q : c.Rl) : c.emb3 q < c.n := by
  rcases q with (t | S) | q
  · have := t.isLt
    show t.val < c.v + c.R + c.v
    omega
  · have := S.isLt
    show c.v + c.R + S.val < c.v + c.R + c.v
    omega
  · have := q.isLt
    show c.v + q.val < c.v + c.R + c.v
    omega

theorem unemb3_emb3 (hv : 0 < c.v) (hR : 0 < c.R) (q : c.Rl) : c.unemb3 hv hR (c.emb3 q) = q := by
  rcases q with (t | S) | q
  · have h1 : t.val < c.v := t.isLt
    show c.unemb3 hv hR t.val = _
    unfold unemb3
    rw [if_pos h1]
    exact congrArg (fun x => (Sum.inl (Sum.inl x) : c.Rl)) (Fin.ext (Nat.mod_eq_of_lt h1))
  · have h0 : S.val < c.v := S.isLt
    have h1 : ¬ (c.v + c.R + S.val < c.v) := by omega
    have h2 : ¬ (c.v + c.R + S.val < c.v + c.R) := by omega
    have h3 : c.v + c.R + S.val - c.v - c.R = S.val := by omega
    show c.unemb3 hv hR (c.v + c.R + S.val) = _
    unfold unemb3
    rw [if_neg h1, if_neg h2]
    exact congrArg (fun x => (Sum.inl (Sum.inr x) : c.Rl)) (Fin.ext (by
      show (c.v + c.R + S.val - c.v - c.R) % c.v = S.val
      rw [h3, Nat.mod_eq_of_lt h0]))
  · have h0 : q.val < c.R := q.isLt
    have h1 : ¬ (c.v + q.val < c.v) := by omega
    have h2 : c.v + q.val < c.v + c.R := by omega
    have h3 : c.v + q.val - c.v = q.val := by omega
    show c.unemb3 hv hR (c.v + q.val) = _
    unfold unemb3
    rw [if_neg h1, if_pos h2]
    exact congrArg (fun x => (Sum.inr x : c.Rl)) (Fin.ext (by
      show (c.v + q.val - c.v) % c.R = q.val
      rw [h3, Nat.mod_eq_of_lt h0]))

theorem emb3_unemb3 (hv : 0 < c.v) (hR : 0 < c.R) (r : Nat) (hr : r < c.n) :
    c.emb3 (c.unemb3 hv hR r) = r := by
  have hn : r < c.v + c.R + c.v := hr
  unfold unemb3
  by_cases h1 : r < c.v
  · rw [if_pos h1]
    show r % c.v = r
    exact Nat.mod_eq_of_lt h1
  · rw [if_neg h1]
    by_cases h2 : r < c.v + c.R
    · rw [if_pos h2]
      have h3 : r - c.v < c.R := by omega
      show c.v + (r - c.v) % c.R = r
      rw [Nat.mod_eq_of_lt h3]
      omega
    · rw [if_neg h2]
      have h3 : r - c.v - c.R < c.v := by omega
      show c.v + c.R + (r - c.v - c.R) % c.v = r
      rw [Nat.mod_eq_of_lt h3]
      omega

/-- the x role of the triple `t`, the y role of the target `S`, the slot `q` -/
abbrev rX (t : Fin c.v) : c.Rl := Sum.inl (Sum.inl t)
abbrev rY (S : Fin c.v) : c.Rl := Sum.inl (Sum.inr S)
abbrev rS (q : Fin c.R) : c.Rl := Sum.inr q

variable {c}

theorem Valid.complete3 (V : c.Valid) : Complete c.p c.lab0 c.H0 c.tot c.emb3 :=
  V.complete c.emb3 c.emb3_lt

end CCert

end SSC
