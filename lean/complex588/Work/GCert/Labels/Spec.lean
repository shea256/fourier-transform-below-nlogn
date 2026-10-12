import Work.GCert.Labels.Elim

/-!
# (key: gx-labels) The label replay: semantic form, composition of segments

State = `SSC.Trie` (register ↦ frame id).  A register `r` named by a gate at frame `f`:
`vOut` (new state), `vRanks` (rank of its block, if it climbs), `vOk` (it is a register, and a
climb goes to a strictly larger dimension), `vCl` (the code it climbs from).  Lists of
registers: `rOut`, `rRanks`, `rOk`, `rCl`; a gate: `gOut`, `gRanks`, `gOk` (with `GSub`: the
digits of every code climbed from lie in the span of the digits of the gate's code); gate
lists: `runOut`, `runRanks`, `runOk`.

`Run p S gs S' rs`  the gates `gs` are legal from `S`, end at `S'`, with block ranks `rs`.
`Run.append`        **composition of segments**.
`Feeds`             bookkeeping of the packed accumulator.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary
noncomputable section

/-- state after `r` is named by a gate at frame `f` -/
def vOut (f : Nat) (S : Trie) (r : Nat) : Trie := if S.get r = f then S else S.set r f

def vRanks (p : Par) (f : Nat) (S : Trie) (r : Nat) : List Nat :=
  if S.get r = f then [] else [cdim (p.tab.get f) - cdim (p.tab.get (S.get r))]

def vCl (p : Par) (f : Nat) (S : Trie) (r : Nat) : List Nat :=
  if S.get r = f then [] else [p.tab.get (S.get r)]

def vOk (p : Par) (f : Nat) (S : Trie) (r : Nat) : Prop :=
  r < p.n ∧ (S.get r ≠ f → cdim (p.tab.get (S.get r)) < cdim (p.tab.get f))

def rOut (f : Nat) : Trie → List Nat → Trie
  | S, [] => S
  | S, r :: l => rOut f (vOut f S r) l

def rRanks (p : Par) (f : Nat) : Trie → List Nat → List Nat
  | _, [] => []
  | S, r :: l => vRanks p f S r ++ rRanks p f (vOut f S r) l

def rCl (p : Par) (f : Nat) : Trie → List Nat → List Nat
  | _, [] => []
  | S, r :: l => vCl p f S r ++ rCl p f (vOut f S r) l

def rOk (p : Par) (f : Nat) : Trie → List Nat → Prop
  | _, [] => True
  | S, r :: l => vOk p f S r ∧ rOk p f (vOut f S r) l

theorem rOut_append (f : Nat) (S : Trie) (l l' : List Nat) :
    rOut f S (l ++ l') = rOut f (rOut f S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons r l ih => exact ih _

theorem rRanks_append (p : Par) (f : Nat) (S : Trie) (l l' : List Nat) :
    rRanks p f S (l ++ l') = rRanks p f S l ++ rRanks p f (rOut f S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons r l ih =>
    show vRanks p f S r ++ rRanks p f (vOut f S r) (l ++ l') = _
    rw [ih, ← List.append_assoc]; rfl

theorem rCl_append (p : Par) (f : Nat) (S : Trie) (l l' : List Nat) :
    rCl p f S (l ++ l') = rCl p f S l ++ rCl p f (rOut f S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons r l ih =>
    show vCl p f S r ++ rCl p f (vOut f S r) (l ++ l') = _
    rw [ih, ← List.append_assoc]; rfl

theorem rOk_append (p : Par) (f : Nat) (S : Trie) (l l' : List Nat) :
    rOk p f S (l ++ l') ↔ rOk p f S l ∧ rOk p f (rOut f S l) l' := by
  induction l generalizing S with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons r l ih =>
    show (vOk p f S r ∧ rOk p f (vOut f S r) (l ++ l')) ↔ _
    rw [ih]; exact and_assoc.symm

/-- the digits of every code of `cl` lie in the span of the digits of the code of frame `f` -/
def GSub (p : Par) (f : Nat) (cl : List Nat) : Prop :=
  (∀ ca ∈ cl, cP p.h ca < 2 ^ (p.h * p.h)) → ∀ Sp : Space (Fin p.h) → Prop, Sp 0 →
    (∀ x y, Sp x → Sp y → Sp (x + y)) → (∀ q, q < p.h → Sp (dv p.h (cP p.h (p.tab.get f)) q)) →
    ∀ ca ∈ cl, ∀ q, q < p.h → Sp (dv p.h (cP p.h ca) q)

def gOut (S : Trie) (g : Gate) : Trie := rOut g.frame S g.regs
def gRanks (p : Par) (S : Trie) (g : Gate) : List Nat := rRanks p g.frame S g.regs
def gOk (p : Par) (S : Trie) (g : Gate) : Prop :=
  rOk p g.frame S g.regs ∧ GSub p g.frame (rCl p g.frame S g.regs)

def runOut : Trie → List Gate → Trie
  | S, [] => S
  | S, g :: gs => runOut (gOut S g) gs

def runRanks (p : Par) : Trie → List Gate → List Nat
  | _, [] => []
  | S, g :: gs => gRanks p S g ++ runRanks p (gOut S g) gs

def runOk (p : Par) : Trie → List Gate → Prop
  | _, [] => True
  | S, g :: gs => gOk p S g ∧ runOk p (gOut S g) gs

theorem runOut_append (S : Trie) (l l' : List Gate) :
    runOut S (l ++ l') = runOut (runOut S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons g l ih => exact ih _

theorem runRanks_append (p : Par) (S : Trie) (l l' : List Gate) :
    runRanks p S (l ++ l') = runRanks p S l ++ runRanks p (runOut S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons g l ih =>
    show gRanks p S g ++ runRanks p (gOut S g) (l ++ l') = _
    rw [ih, ← List.append_assoc]; rfl

theorem runOk_append (p : Par) (S : Trie) (l l' : List Gate) :
    runOk p S (l ++ l') ↔ runOk p S l ∧ runOk p (runOut S l) l' := by
  induction l generalizing S with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons g l ih =>
    show (gOk p S g ∧ runOk p (gOut S g) (l ++ l')) ↔ _
    rw [ih]; exact and_assoc.symm

/-- **a legal replay**: the gates `gs` from the state `S` end at `S'` with block ranks `rs` -/
def Run (p : Par) (S : Trie) (gs : List Gate) (S' : Trie) (rs : List Nat) : Prop :=
  runOk p S gs ∧ runOut S gs = S' ∧ runRanks p S gs = rs

/-- **composition of segments** -/
theorem Run.append {p : Par} {S S1 S2 : Trie} {g1 g2 : List Gate} {r1 r2 : List Nat}
    (a : Run p S g1 S1 r1) (b : Run p S1 g2 S2 r2) : Run p S (g1 ++ g2) S2 (r1 ++ r2) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  subst a2
  exact ⟨(runOk_append p S g1 g2).mpr ⟨a1, b1⟩, by rw [runOut_append, b2],
    by rw [runRanks_append, a3, b3]⟩

theorem Run.nil (p : Par) (S : Trie) : Run p S [] S [] := ⟨trivial, rfl, rfl⟩

/-! ## the packed accumulator -/

/-- all digits of `A` lie in `Sp` -/
def AllIn (h : Nat) (Sp : Space (Fin h) → Prop) (A : Nat) : Prop := ∀ j, Sp (dv h A j)

/-- from `A` to `A'` the codes `cl` were appended -/
def Feeds (h A A' : Nat) (cl : List Nat) : Prop :=
  (∀ ca ∈ cl, cP h ca < 2 ^ (h * h)) → ∀ Sp : Space (Fin h) → Prop, AllIn h Sp A' →
    AllIn h Sp A ∧ ∀ ca ∈ cl, ∀ q, q < h → Sp (dv h (cP h ca) q)

theorem Feeds.refl (h A : Nat) : Feeds h A A [] :=
  fun _ Sp H => ⟨H, fun ca hca => absurd hca (List.not_mem_nil)⟩

theorem Feeds.trans {h A A' A'' : Nat} {c1 c2 : List Nat} (a : Feeds h A A' c1)
    (b : Feeds h A' A'' c2) : Feeds h A A'' (c1 ++ c2) := by
  intro hb Sp H
  obtain ⟨b1, b2⟩ := b (fun ca hca => hb ca (List.mem_append_right _ hca)) Sp H
  obtain ⟨a1, a2⟩ := a (fun ca hca => hb ca (List.mem_append_left _ hca)) Sp b1
  refine ⟨a1, fun ca hca => ?_⟩
  rcases List.mem_append.mp hca with h1 | h1
  · exact a2 ca h1
  · exact b2 ca h1

theorem Feeds.step (h A ca : Nat) : Feeds h A (A <<< (h * h) + cP h ca) [ca] := by
  intro hb Sp H
  have hP : cP h ca < 2 ^ (h * h) := hb ca (List.mem_singleton.mpr rfl)
  constructor
  · intro j
    have e : dv h (A <<< (h * h) + cP h ca) (j + h) = dv h A j := by
      funext q
      simp only [dv]
      rw [acc_bit h A _ (j + h) q.val hP q.isLt, if_neg (by omega), Nat.add_sub_cancel]
    rw [← e]; exact H _
  · intro c hc q hq
    rw [List.mem_singleton.mp hc]
    have e : dv h (A <<< (h * h) + cP h ca) q = dv h (cP h ca) q := by
      funext i
      simp only [dv]
      rw [acc_bit h A _ q i.val hP i.isLt, if_pos hq]
    rw [← e]; exact H _

end
end GLab

#print axioms GLab.Run.append
#print axioms GLab.Feeds.step
