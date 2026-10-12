import OAI.Computability.FourierTransform.RAM

namespace OAI

/-! Bounds on integer registers and array offsets. Allocation is charged as work. -/
namespace PowerSaving.RAM
open Ty

variable {α β : Type*} {l n : ℕ} {P : α → Prop}

def Ty.fits (cap : ℕ) : (t : Ty) → t.T → Prop
  | w, i => (i:ℕ) ≤ cap
  | c _, _ => True
  | p s t, v => fits cap s v.1 ∧ fits cap t v.2
  | a s, arr => (arr:Tape s.T).len ≤ cap ∧ ∀ i, fits cap s (Tape.pos arr i)

theorem Ty.fits_blank (l : ℕ) (t : Ty) : Ty.fits l t t.blank := by
  induction t with
  | w => simp [Ty.fits, Ty.blank]
  | c => simp [Ty.fits]
  | p _ _ u v => simpa [Ty.fits, Ty.blank] using And.intro u v
  | a t h =>
    change 0 ≤ l ∧ ∀ i : Fin 0, _
    exact ⟨Nat.zero_le _, fun i => Fin.elim0 i⟩

def Bill.Pres (b : Bill α) (cap : ℕ) (P : α → Prop) : Prop :=
  b.peak ≤ cap → P b.val

theorem Bill.Pres.pass {b : Bill α} {f : α → Bill β}
    {P : α → Prop} {Q : β → Prop} (h : b.Pres l P)
    (g : ∀ x, P x → (f x).Pres l Q) : (b.pass f).Pres l Q := by
  intro hm
  replace hm : _ ∧ _ := max_le_iff.mp hm
  exact g b.val (h hm.1) hm.2

theorem Bill.Pres.pay {m : ℕ} {b : Bill α} (h : b.Pres l P) : (b.pay n m).Pres l P :=
  fun hm => h (max_le_iff.mp hm).1

theorem Bill.one_pres {x : α} (h : P x) : (Bill.one x).Pres l P :=
  fun _ => h

theorem Bill.steps_pres {x : α} (hx : P x)
    {f : ℕ → α → Bill α} (hf : ∀ i, i<l → ∀ y, P y → (f i y).Pres l P) :
    (steps x f n).Pres l P := by
  induction n with
  | zero => exact Bill.one_pres hx
  | succ i ih =>
    intro hm
    rw [steps] at hm ⊢
    have hg := max_le_iff.mp hm
    have hh := ih.pass (hf i (Nat.lt_of_succ_le hg.2))
    exact hh hg.1

theorem Bill.sow_pres (s : Ty) (len n l : ℕ)
    (f : ℕ → Bill (p w s).T)
    (hf : ∀ i, i<l → (f i).Pres l (Ty.fits l (p w s))) :
    (sow len n s.blank f).Pres l (Ty.fits l (a s)) := by
  intro hm
  have le := (max_le_iff.mp hm).2
  have hb : Ty.fits l (a s) (Tape.tab len (fun _ => s.blank)) :=
    ⟨le, fun _ => Ty.fits_blank l s⟩
  unfold sow at hm ⊢
  refine Bill.Pres.pay (Bill.steps_pres hb ?_) hm
  intro i hi x hx
  refine (hf i hi).pass (fun pair hp => Bill.one_pres ?_)
  refine ⟨hx.1, fun j => ?_⟩
  unfold Tape.set
  dsimp
  split
  · exact hp.2
  · exact hx.2 j

theorem Bill.tab_pres (s : Ty) (len l : ℕ)
    (f : ℕ → Bill s.T) (hf : ∀ i, i<l → (f i).Pres l (Ty.fits l s)) :
    (tab len s.blank f).Pres l (Ty.fits l (a s)) := by
  unfold tab
  apply Bill.sow_pres
  intro i hi
  exact (hf i hi).pass (fun x hx => Bill.one_pres ⟨hi.le,hx⟩)

variable {m : Bool} {s t : Ty} {r : Port}

theorem Atom.run_pres (op : Atom m s t) (x : s.T) (hx : Ty.fits l s x) :
    (op.run x).Pres l (Ty.fits l t) := by
  cases op with
  | lit => intro h; exact h
  | int f =>
    rcases x with ⟨i,j⟩
    cases f <;> intro h <;> exact h
  | cz => intro; trivial
  | cone => intro; trivial
  | add => intro; trivial
  | sub => intro; trivial
  | scale => intro; trivial
  | inv => intro; trivial
  | cross => intro; trivial
  | id => intro; exact hx
  | fst =>
    intro
    change Ty.fits _ _ _ ∧ Ty.fits _ _ _ at hx
    exact hx.1
  | snd =>
    intro
    change Ty.fits _ _ _ ∧ Ty.fits _ _ _ at hx
    exact hx.2
  | len =>
    intro h
    exact h
  | @look t =>
    rcases x with ⟨v,i⟩
    intro h
    change Ty.fits l _ (v.look i t.blank)
    unfold Tape.look
    split
    · exact hx.1.2 _
    · exact Ty.fits_blank _ _

def Handler.Pres (l : ℕ) : (r : Port) → Handler r → Prop
  | none, _ => True
  | some (s,t), f => ∀ x, Ty.fits l s x → (f x).Pres l (Ty.fits l t)

theorem Code.run_pres (f : Code m r s t)
    (h : Handler r) (hh : Handler.Pres l r h)
    (x : s.T) (hx : Ty.fits l s x) :
    (f.run h x).Pres l (Ty.fits l t) := by
  induction f with
  | atom op => rw [Code.run]; exact Atom.run_pres _ _ hx
  | comp u v hu hv =>
    rw [Code.run]
    apply Bill.Pres.pay
    exact (hu h hh x hx).pass (fun y hy => hv h hh y hy)
  | fork u v hu hv =>
    rw [Code.run]
    exact (hu h hh x hx).pass
      (fun y hy => (hv h hh x hx).pass (fun z hz => Bill.one_pres ⟨hy,hz⟩))
  | ifz q f g hq hf hg =>
    rw [Code.run]
    apply Bill.Pres.pay
    refine (hq h hh x hx).pass (fun y _ => ?_)
    split
    · exact hf h hh x hx
    · exact hg h hh x hx
  | loop n init body hn hi hb =>
    rw [Code.run]
    apply Bill.Pres.pay
    refine (hn h hh x hx).pass (fun y hy =>
      (hi h hh x hx).pass (fun z hz => Bill.steps_pres hz ?_))
    intro i il v hv
    apply hb h hh (x,(i,v))
    exact ⟨hx, il.le, hv⟩
  | tab n body hn hb =>
    rw [Code.run]
    apply Bill.Pres.pay
    refine (hn h hh x hx).pass (fun y hy => Bill.tab_pres _ _ _ _ ?_)
    intro i il
    apply hb h hh (x,i)
    exact ⟨hx, il.le⟩
  | sow n count body hn hc hb =>
    rw [Code.run]
    apply Bill.Pres.pay
    refine (hn h hh x hx).pass (fun y hy =>
      (hc h hh x hx).pass (fun v hv => Bill.sow_pres _ _ _ _ _ ?_))
    intro i il
    apply hb h hh (x,i)
    exact ⟨hx, il.le⟩
  | importClosed f hf =>
    rw [Code.run]
    exact (hf () True.intro x hx).pay
  | call =>
    rw [Code.run]
    exact (hh x hx).pay
  | @descend r s t base step hb hs =>
    have hd (n : ℕ) (x : s.T) (hx : Ty.fits l s x) :
        (depthRun (base.run ()) step.run n x).Pres l (Ty.fits l t) := by
      induction n generalizing x with
      | zero => exact (hb () True.intro x hx).pay
      | succ n ih =>
        rw [depthRun]
        exact (hs (depthRun (base.run ()) step.run n) ih x hx).pay
    rcases x with ⟨i,x⟩
    rw [Code.run]
    exact (hd _ _ hx.2).pay

theorem prog_pres (f : Prog m s t) (x : s.T) (hx : Ty.fits l s x)
    (hb : (run f x).peak ≤ l) :
    Ty.fits l t (run f x).val :=
  Code.run_pres f () True.intro x hx hb

end PowerSaving.RAM

end OAI
