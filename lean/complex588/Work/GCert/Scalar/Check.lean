import Work.GCert.Scalar.Runs

/-!
# (key: gx-scalar) The kernel checks give the accepted replays

* `SegOK.of_check`   `segCheck c p lo n pre items post = true → SegOK c p lo n pre items post`;
* `XRun.of_check`    `scalCheck c p lo n = true → XRun c lo n`;
* `YRun.of_check`    `yCheck c p lo n = true → YRun c lo n`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

section
variable (c : Raw) (p : SPar) (lo n : Nat) (hp : PGood c p lo n)
include hp

theorem U_pos (r : Nat) : 1 ≤ unitK p.ux p.us p.uy c.v (2 * c.v) r :=
  unitK_pos _ _ _ _ _ _ hp.hx hp.hs hp.hy

theorem gItem_sound (it : Item) (tr : Trie) (k : Trie → Bool) (hI : GOk p.d p.sw n tr)
    (h : gItem c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
      c.ret.length it tr k = true) :
    ∃ tr', GOk p.d p.sw n tr' ∧ k tr' = true ∧
      ItemRun c p n it (absG p.d (64 + p.sw * n) tr) (absG p.d (64 + p.sw * n) tr') := by
  have hu := U_pos c p lo n hp
  cases it with
  | cA gs =>
    exact gGates_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v) (okA c) (fun _ => true) hp.hsw rfl
      rfl hu gs tr k hI h
  | scat =>
    obtain ⟨tr', hI', hk, hlen, hb, hr⟩ := gScat_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v)
      (okS c) hp.hsw rfl rfl hu c.ret c.ret.length (scatRows c) c.v tr k hI h
    exact ⟨tr', hI', hk, hr, hlen, hb⟩
  | cB gs =>
    exact gGates_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v) (okB c) (fun _ => true) hp.hsw rfl
      rfl hu gs tr k hI h

theorem gItems_sound (items : List Item) : ∀ (tr : Trie) (k : Trie → Bool), GOk p.d p.sw n tr →
    gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
      c.ret.length items tr k = true →
    ∃ tr', GOk p.d p.sw n tr' ∧ k tr' = true ∧
      ItemsRun c p n items (absG p.d (64 + p.sw * n) tr) (absG p.d (64 + p.sw * n) tr') := by
  induction items with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons it items ih =>
    intro tr k hI h
    obtain ⟨tr1, hI1, hk1, r1⟩ := gItem_sound c p lo n hp it tr _ hI h
    obtain ⟨tr2, hI2, hk2, r2⟩ := ih tr1 k hI1 hk1
    exact ⟨tr2, hI2, hk2, _, r1, r2⟩

/-- the final test of a register class, from the kernel test -/
theorem fin_of (base u : Nat) (tr : Trie) (hI : GOk p.d p.sw n tr)
    (h : gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) u base lo (lo + n) tr c.v 0 = true) :
    FinSt c p lo n base u (absG p.d (64 + p.sw * n) tr) := by
  intro S hS
  have := gFin_sound p.d p.sw (64 + p.sw * n) u base lo (lo + n) tr hI.wf c.v 0 h S hS
  rw [Nat.zero_add] at this
  exact this

end

theorem pgood_of {c : Raw} {p : SPar} {lo n : Nat} {X : Prop}
    (h : (1 ≤ p.ux ∧ 1 ≤ p.us ∧ 1 ≤ p.uy ∧ 1 ≤ p.sw) ∧ 2 * c.v + c.R ≤ 2^p.d ∧ lo + n ≤ c.v ∧
      (p.ux < 2^(p.sw - 1) ∧ p.uy < 2^(p.sw - 1) ∧ p.ux < 2^31 ∧ p.uy < 2^31) ∧
      (∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R) ∧ X) :
    PGood c p lo n ∧ X :=
  ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1.1, h.2.2.2.1.2.1,
    h.2.2.2.1.2.2.1, h.2.2.2.1.2.2.2, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩

/-- **an accepted segment check** -/
theorem SegOK.of_check {c : Raw} {p : SPar} {lo n : Nat} {pre post : Option Trie}
    {items : List Item} (h : segCheck c p lo n pre items post = true) :
    SegOK c p lo n pre items post := by
  unfold segCheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p lo n _ h)
  rw [forceN_eq] at h1
  refine ⟨hp, ?_⟩
  -- the end of the segment
  have hpost : ∀ tr3, GOk p.d p.sw n tr3 →
      Option.rec (motive := fun _ => Bool)
        (guard (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
          (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
        (fun t => beqK tr3 t) post = true →
      PostSt c p lo n post (absG p.d (64 + p.sw * n) tr3) := by
    intro tr3 hI3 hk
    cases post with
    | none =>
      obtain ⟨f1, f2⟩ := guard_true hk
      exact ⟨hI3.small, fin_of c p lo n hp 0 p.ux tr3 hI3 f1, fin_of c p lo n hp c.v p.uy tr3 hI3 f2⟩
    | some t =>
      have e : tr3 = t := beqK_eq tr3 t hk
      rw [← e]
      exact ⟨hI3, rfl⟩
  cases pre with
  | none =>
    have h2 : gInit p.sw p.ux lo n 0 (Trie.mk p.d) (fun tr0 =>
        gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
          c.ret.length items tr0 fun tr3 => Option.rec (motive := fun _ => Bool)
            (guard (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
              (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
            (fun t => beqK tr3 t) post) = true := h1
    have hle : lo + 0 + n ≤ 2^p.d := by have := hp.hd; have := hp.hn; omega
    obtain ⟨t0, hwf, hk, hval⟩ := gInit_sound p.d p.sw p.ux lo n 0 (Trie.mk p.d) _ (Trie.wf_mk p.d)
      hle h2
    obtain ⟨hI0, hinit⟩ := init_ok p.d p.sw n p.ux lo hp.hsw hp.hxs hp.hx2 t0 hwf hval
    obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p lo n hp items t0 _ hI0 hk
    exact ⟨_, _, hinit, hr, hpost tr3 hI3 hk3⟩
  | some t =>
    intro hI0
    have h2 : gItems c p (2 * c.v) (2 * c.v + c.R) (maskW p.sw n) (64 + p.sw * n)
        (2^(64 + p.sw * n)) c.ret.length items t (fun tr3 => Option.rec (motive := fun _ => Bool)
          (guard (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.ux 0 lo (lo + n) tr3 c.v 0)
            (gFin p.sw (64 + p.sw * n) (2^(64 + p.sw * n)) p.uy c.v lo (lo + n) tr3 c.v 0))
          (fun t => beqK tr3 t) post) = true := h1
    obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p lo n hp items t _ hI0 h2
    exact ⟨_, hr, hpost tr3 hI3 hk3⟩

/-- **the scalar check in one evaluation** -/
theorem XRun.of_check {c : Raw} {p : SPar} {lo n : Nat} (h : scalCheck c p lo n = true) :
    XRun c lo n := XRun.of_seg (SegOK.of_check h)

/-- **the y check** -/
theorem YRun.of_check {c : Raw} {p : SPar} {lo n : Nat} (h : yCheck c p lo n = true) :
    YRun c lo n := by
  unfold yCheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p lo n _ h)
  have hle : c.v + lo + 0 + n ≤ 2^p.d := by have := hp.hd; have := hp.hn; omega
  obtain ⟨t0, hwf, hk, hval⟩ := gInit_sound p.d p.sw p.uy (c.v + lo) n 0 (Trie.mk p.d) _
    (Trie.wf_mk p.d) hle h1
  obtain ⟨hI0, hinit⟩ := init_ok p.d p.sw n p.uy (c.v + lo) hp.hsw hp.hys hp.hy2 t0 hwf hval
  obtain ⟨tr3, hI3, hk3, hr⟩ := gChunks_sound p.d p.sw n _ _ p.ux p.us p.uy c.v (2 * c.v) (okB c)
    (selY c.v (2 * c.v)) hp.hsw rfl rfl (U_pos c p lo n hp) c.B t0 _ hI0 hk
  exact ⟨p, _, _, hp, hinit, hr, hI3.small, fin_of c p lo n hp c.v p.uy tr3 hI3 hk3⟩

#print axioms SegOK.of_check
#print axioms XRun.of_check
#print axioms YRun.of_check

end GS
