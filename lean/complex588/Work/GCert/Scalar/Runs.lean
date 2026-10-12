import Work.GCert.Scalar.End

/-!
# (key: gx-scalar) Accepted replays as propositions: items, segments, `XRun`, `YRun`

* `ItemsRun`   a list of items (chunks of `A`, the scatter, chunks of `B`) on abstract states;
* `SegOK`      what an accepted segment check gives; `SegOK.append` joins two segments at a state;
* `XRun c lo n`  an accepted replay of the whole main phase for the sources `lo .. lo+n-1`:
  four abstract states joined by `GRun` on `addsA`, `scatAdds`, `addsB`, the first holding the
  sources in the x roles, the last holding exactly source `t` in `x_t` and in `y_t`;
* `YRun c lo n`  an accepted replay of the adds of `B` that read a y role.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- unit of the content of a register -/
noncomputable def U (c : Raw) (p : SPar) : Nat → Nat := unitK p.ux p.us p.uy c.v (2 * c.v)

/-- the single adds `(tgt, src, co)` of phase A / phase B, in order -/
def addsA (c : Raw) : List (Nat × Nat × Co) := c.gatesA.flatMap Gate.adds
def addsB (c : Raw) : List (Nat × Nat × Co) := c.gatesB.flatMap Gate.adds
/-- the single adds of the scatter: `y_t += co * (register of total k)` -/
noncomputable def scatAdds (c : Raw) : List (Nat × Nat × Co) := scatAddsFrom c.ret c.v (scatRows c)

/-- sizes of the scatter: `v` rows, every total index below the number of retained totals -/
def ScatShape (c : Raw) : Prop :=
  c.v + (scatRows c).length = 2 * c.v ∧ ∀ l ∈ scatRows c, ∀ x ∈ l, x.1 < c.ret.length

abbrev okA (c : Raw) : Nat → Nat → Bool := okAK c.v (2 * c.v) (2 * c.v + c.R)
abbrev okS (c : Raw) : Nat → Nat → Bool := okSK c.v (2 * c.v) (2 * c.v + c.R)
abbrev okB (c : Raw) : Nat → Nat → Bool := okBK c.v (2 * c.v) (2 * c.v + c.R)

/-- the tests on the parameters -/
structure PGood (c : Raw) (p : SPar) (lo n : Nat) : Prop where
  hx : 1 ≤ p.ux
  hs : 1 ≤ p.us
  hy : 1 ≤ p.uy
  hsw : 1 ≤ p.sw
  hd : 2 * c.v + c.R ≤ 2^p.d
  hn : lo + n ≤ c.v
  hxs : p.ux < 2^(p.sw - 1)
  hys : p.uy < 2^(p.sw - 1)
  hx2 : p.ux < 2^31
  hy2 : p.uy < 2^31
  hret : ∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R

section
variable (c : Raw) (p : SPar) (lo n : Nat)

def ItemRun : Item → SSt → SSt → Prop
  | .cA gs, a, b => GRun p.sw n (U c p) (okA c) (fun _ => true) a (gs.flatMap Gate.adds) b
  | .scat, a, b => GRun p.sw n (U c p) (okS c) (fun _ => true) a (scatAdds c) b ∧ ScatShape c
  | .cB gs, a, b => GRun p.sw n (U c p) (okB c) (fun _ => true) a (gs.flatMap Gate.adds) b

def ItemsRun : List Item → SSt → SSt → Prop
  | [], a, b => b = a
  | it :: l, a, b => ∃ m, ItemRun c p n it a m ∧ ItemsRun l m b

/-- the first contents: the register `off + T` holds the unit `u` at digit `T` -/
def InitSt (off u : Nat) (a : SSt) : Prop :=
  ∀ r, a.N r = 0 ∧ a.P r = if off ≤ r ∧ r < off + n then u * 2^(p.sw * (r - off)) else 0

/-- the final test for the registers `base + S`, `S < v` -/
def FinSt (base u : Nat) (a : SSt) : Prop :=
  ∀ S, S < c.v → a.P (base + S) = a.N (base + S)
    + (if lo ≤ S ∧ S < lo + n then u * 2^(p.sw * (S - lo)) else 0)

def PostSt : Option Trie → SSt → Prop
  | none, b => SmallSt p.sw n b ∧ FinSt c p lo n 0 p.ux b ∧ FinSt c p lo n c.v p.uy b
  | some t, b => GOk p.d p.sw n t ∧ b = absG p.d (64 + p.sw * n) t

/-- **what an accepted segment gives** -/
def SegOK (pre : Option Trie) (items : List Item) (post : Option Trie) : Prop :=
  PGood c p lo n ∧
    match pre with
    | none => ∃ a b, InitSt p n lo p.ux a ∧ ItemsRun c p n items a b ∧ PostSt c p lo n post b
    | some t => GOk p.d p.sw n t →
        ∃ b, ItemsRun c p n items (absG p.d (64 + p.sw * n) t) b ∧ PostSt c p lo n post b

theorem ItemsRun_append (l1 l2 : List Item) : ∀ (a m b : SSt),
    ItemsRun c p n l1 a m → ItemsRun c p n l2 m b → ItemsRun c p n (l1 ++ l2) a b := by
  induction l1 with
  | nil =>
    intro a m b h1 h2
    have e : m = a := h1
    rw [e] at h2
    exact h2
  | cons x l1 ih =>
    intro a m b h1 h2
    obtain ⟨m1, hs, hr⟩ := h1
    exact ⟨m1, hs, ih m1 m b hr h2⟩

theorem ItemsRun_split (l1 l2 : List Item) : ∀ (a b : SSt),
    ItemsRun c p n (l1 ++ l2) a b → ∃ m, ItemsRun c p n l1 a m ∧ ItemsRun c p n l2 m b := by
  induction l1 with
  | nil => intro a b h; exact ⟨a, rfl, h⟩
  | cons x l1 ih =>
    intro a b h
    obtain ⟨m1, hs, hr⟩ := h
    obtain ⟨m, r1, r2⟩ := ih m1 b hr
    exact ⟨m, ⟨m1, hs, r1⟩, r2⟩

theorem SegOK.append' {pre post : Option Trie} {l1 l2 : List Item} {T : Trie}
    (h1 : SegOK c p lo n pre l1 (some T)) (h2 : SegOK c p lo n (some T) l2 post) :
    SegOK c p lo n pre (l1 ++ l2) post := by
  obtain ⟨hp, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  refine ⟨hp, ?_⟩
  cases pre with
  | none =>
    obtain ⟨a, b, hi, hr, hT, eb⟩ := h1
    obtain ⟨b', hr', hpost⟩ := h2 hT
    rw [← eb] at hr'
    exact ⟨a, b', hi, ItemsRun_append c p n l1 l2 a b b' hr hr', hpost⟩
  | some t =>
    intro ht
    obtain ⟨b, hr, hT, eb⟩ := h1 ht
    obtain ⟨b', hr', hpost⟩ := h2 hT
    rw [← eb] at hr'
    exact ⟨b', ItemsRun_append c p n l1 l2 _ b b' hr hr', hpost⟩

theorem ItemsRun_cA (cs : List (List Gate)) : ∀ (a b : SSt),
    ItemsRun c p n (cs.map Item.cA) a b →
    GRun p.sw n (U c p) (okA c) (fun _ => true) a (cs.flatten.flatMap Gate.adds) b := by
  induction cs with
  | nil => intro a b h; exact h
  | cons gs cs ih =>
    intro a b h
    obtain ⟨m, h1, h2⟩ := h
    rw [List.flatten_cons, List.flatMap_append]
    exact GRun_append _ _ _ _ _ _ _ _ _ _ h1 (ih m b h2)

theorem ItemsRun_cB (cs : List (List Gate)) : ∀ (a b : SSt),
    ItemsRun c p n (cs.map Item.cB) a b →
    GRun p.sw n (U c p) (okB c) (fun _ => true) a (cs.flatten.flatMap Gate.adds) b := by
  induction cs with
  | nil => intro a b h; exact h
  | cons gs cs ih =>
    intro a b h
    obtain ⟨m, h1, h2⟩ := h
    rw [List.flatten_cons, List.flatMap_append]
    exact GRun_append _ _ _ _ _ _ _ _ _ _ h1 (ih m b h2)

end

/-- **two segments joined at a state** -/
theorem SegOK.append {c : Raw} {p : SPar} {lo n : Nat} {pre post : Option Trie}
    {l1 l2 : List Item} {T : Trie} (h1 : SegOK c p lo n pre l1 (some T))
    (h2 : SegOK c p lo n (some T) l2 post) : SegOK c p lo n pre (l1 ++ l2) post :=
  SegOK.append' c p lo n h1 h2

/-- **An accepted replay of the main phase** for the sources `lo .. lo+n-1`. -/
def XRun (c : Raw) (lo n : Nat) : Prop :=
  ∃ (p : SPar) (a0 a1 a2 a3 : SSt), PGood c p lo n ∧ InitSt p n lo p.ux a0 ∧
    GRun p.sw n (U c p) (okA c) (fun _ => true) a0 (addsA c) a1 ∧
    GRun p.sw n (U c p) (okS c) (fun _ => true) a1 (scatAdds c) a2 ∧ ScatShape c ∧
    GRun p.sw n (U c p) (okB c) (fun _ => true) a2 (addsB c) a3 ∧
    SmallSt p.sw n a3 ∧ FinSt c p lo n 0 p.ux a3 ∧ FinSt c p lo n c.v p.uy a3

/-- **An accepted replay of the adds of `B` reading a y role**, for the y roles `lo .. lo+n-1`. -/
def YRun (c : Raw) (lo n : Nat) : Prop :=
  ∃ (p : SPar) (a0 a3 : SSt), PGood c p lo n ∧ InitSt p n (c.v + lo) p.uy a0 ∧
    GRun p.sw n (U c p) (okB c) (selY c.v (2 * c.v)) a0 (addsB c) a3 ∧
    SmallSt p.sw n a3 ∧ FinSt c p lo n c.v p.uy a3

/-- the whole program in segments is an accepted replay -/
theorem XRun.of_seg {c : Raw} {p : SPar} {lo n : Nat} (h : SegOK c p lo n none (prog c) none) :
    XRun c lo n := by
  obtain ⟨hp, a, b, hi, hr, hsm, hfx, hfy⟩ := h
  obtain ⟨m1, r1, r2⟩ := ItemsRun_split c p n _ _ a b hr
  obtain ⟨m2, ⟨rs, hsh⟩, r3⟩ := r2
  exact ⟨p, a, m1, m2, b, hp, hi, ItemsRun_cA c p n _ a m1 r1, rs, hsh,
    ItemsRun_cB c p n _ m2 b r3, hsm, hfx, hfy⟩

/-- the same, the items given as a list equal to `prog c` (the equation holds by `rfl`) -/
theorem XRun.of_segs {c : Raw} {p : SPar} {lo n : Nat} {items : List Item}
    (h : SegOK c p lo n none items none) (e : prog c = items) : XRun c lo n :=
  XRun.of_seg (e ▸ h)

#print axioms SegOK.append
#print axioms XRun.of_seg

end GS
