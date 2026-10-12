import Work.GCert.Scalar.Main

/-!
# (key: gauge-401) The E7 kernel check: a gauged slot never reaches a y role

DFT Bridge3, 2026-10-11.  Mirror of Jacob Sussman's `GS.yCheck` / `GS.segCheck` (`Work/GCert/Scalar/Seg.lean`,
Apache-2.0) and of `gx.py` `q2` (E7), for the entrance gauges of Dugongue (PR #401).

`eCheck c p gl`: the sources are the slot registers of the list `gl` (strictly increasing; digit `T` = the `T`-th
register of `gl`), every x role starts at 0; the adds of `A`, the scatter and the adds of `B` are replayed with the
digit rule of `gAdd`; at the end every y role holds nothing.  Soundness `eCheck_sound`: for a slot `q` whose register
is in `gl`, the column of `q` in the y rows of `Mt = MB * scatM (Jrm * Ccm) * MA` is zero.
Python mirror: w-bridge3/p401/tools/emirror.py.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

/-- the source registers: strictly increasing from `lo`, below `nr` -/
noncomputable def incK (nr : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih lo => guard (Nat.ble lo r) (guard (Nat.ble (Nat.succ r) nr) (ih (Nat.succ r))))

/-- first contents: the register `gl[T]` holds `u` at digit `T` (positive part), `T = i, i+1, ..`, with the tag -/
noncomputable def gInitL (sw u : Nat) : List Nat → Nat → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool) (fun _ t k => k t)
    (fun r _ ih i t k => forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))) fun b =>
      forceN (Nat.succ i) fun i2 => ih i2 (t.set r b) k)

/-- **The E7 check** (one evaluation): sources = the slot registers `gl`, x = 0; at the end no y role holds anything. -/
noncomputable def eCheck (c : Raw) (p : SPar) (gl : List Nat) : Bool :=
  gPre c p 0 gl.length fun v2 nr _ tm K m2 =>
    guard (incK nr gl v2) (guard (Nat.ble (Nat.succ p.us) (Nat.pow 2 (Nat.sub p.sw 1)))
      (guard (Nat.ble (Nat.succ p.us) 2147483648)
        (forceN (List.length c.ret) fun rl =>
          gInitL p.sw p.us gl 0 (Trie.mk p.d) fun tr0 =>
            gItems c p v2 nr tm K m2 rl (prog c) tr0 fun tr3 =>
              gFin p.sw K m2 p.uy c.v 0 0 tr3 c.v 0)))

theorem incK_sound (nr : Nat) : ∀ (gl : List Nat) (lo : Nat), incK nr gl lo = true →
    (∀ r ∈ gl, lo ≤ r ∧ r < nr) ∧ gl.Nodup := by
  intro gl
  induction gl with
  | nil => intro lo _; exact ⟨fun r h => absurd h List.not_mem_nil, List.nodup_nil⟩
  | cons r gl ih =>
    intro lo h
    have h' : guard (Nat.ble lo r) (guard (Nat.ble (Nat.succ r) nr) (incK nr gl (Nat.succ r))) = true := h
    obtain ⟨h1, h2⟩ := guard_true h'
    obtain ⟨h3, h4⟩ := guard_true h2
    obtain ⟨ih1, ih2⟩ := ih (Nat.succ r) h4
    have e1 := ble_true h1
    have e3 := ble_true h3
    refine ⟨fun x hx => ?_, List.nodup_cons.mpr ⟨fun hr => by have := (ih1 r hr).1; omega, ih2⟩⟩
    rcases List.mem_cons.mp hx with e | e
    · rw [e]; exact ⟨e1, by omega⟩
    · have := ih1 x e; omega

theorem gInitL_cons (sw u r : Nat) (gl : List Nat) (i : Nat) (t : Trie) (k : Trie → Bool) :
    gInitL sw u (r :: gl) i t k = forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))) fun b =>
      forceN (Nat.succ i) fun i2 => gInitL sw u gl i2 (t.set r b) k := rfl

theorem gInitL_sound (d sw u : Nat) : ∀ (gl : List Nat) (i : Nat) (t : Trie) (k : Trie → Bool), t.wf d →
    (∀ r ∈ gl, r < 2^d) → gl.Nodup → gInitL sw u gl i t k = true →
    ∃ t', t'.wf d ∧ k t' = true ∧ ∀ r, absS (2^d) t' r
      = if r ∈ gl then leaf0 sw u (i + gl.idxOf r) else absS (2^d) t r := by
  intro gl
  induction gl with
  | nil =>
    intro i t k hwf _ _ h
    exact ⟨t, hwf, h, fun r => by rw [if_neg List.not_mem_nil]⟩
  | cons r0 gl ih =>
    intro i t k hwf hlt hnd h
    rw [gInitL_cons, forceN_eq, forceN_eq] at h
    have hr0 : r0 < 2^d := hlt r0 List.mem_cons_self
    obtain ⟨hn0, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨t', hwf', hk, hval⟩ := ih (i+1) _ k (Trie.wf_set d t hwf _ _)
      (fun r hr => hlt r (List.mem_cons_of_mem _ hr)) hnd' h
    refine ⟨t', hwf', hk, fun r => ?_⟩
    rw [hval r]
    have hs := absS_set d t hwf r0 (leaf0 sw u i) hr0
    have hs' : absS (2^d) (t.set r0 (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))))
        = Function.update (absS (2^d) t) r0 (leaf0 sw u i) := hs
    rw [hs']
    by_cases e : r = r0
    · subst e
      rw [if_neg hn0, if_pos List.mem_cons_self, Function.update_self, List.idxOf_cons_self, Nat.add_zero]
    · rw [Function.update_of_ne e, List.idxOf_cons_ne _ (Ne.symm e)]
      by_cases hm : r ∈ gl
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]
        congr 1
        omega
      · rw [if_neg hm, if_neg (fun h => by rcases List.mem_cons.mp h with h | h; exact e h; exact hm h)]

/-- the state after `gInitL` on the empty trie: invariant and abstract contents -/
theorem init_okL (d sw u : Nat) (gl : List Nat) (hsw : 1 ≤ sw) (hu : u < 2^(sw - 1)) (hu2 : u < 2^31)
    (t' : Trie) (hwf : t'.wf d)
    (hval : ∀ r, absS (2^d) t' r = if r ∈ gl then leaf0 sw u (0 + gl.idxOf r) else absS (2^d) (Trie.mk d) r) :
    GOk d sw gl.length t' ∧ ∀ r, (absG d (64 + sw * gl.length) t').N r = 0 ∧
      (absG d (64 + sw * gl.length) t').P r = if r ∈ gl then u * 2^(sw * gl.idxOf r) else 0 := by
  have hus : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have key : ∀ r, (absS (2^d) t' r % 2^(64 + sw * gl.length)) >>> 64
        = (if r ∈ gl then u * 2^(sw * gl.idxOf r) else 0) ∧
      absS (2^d) t' r >>> (64 + sw * gl.length) = 0 ∧
        absS (2^d) t' r % 2^(64 + sw * gl.length) % 2^64 < 2^63 := by
    intro r
    rw [hval r, Nat.zero_add]
    by_cases hr : r ∈ gl
    · obtain ⟨f1, f2, f3⟩ := leaf0_facts sw gl.length u (gl.idxOf r) hu hsw hu2
        (List.idxOf_lt_length_of_mem hr)
      rw [if_pos hr, if_pos hr, Nat.mod_eq_of_lt f1, Nat.shiftRight_eq_div_pow _ (64 + sw * gl.length),
        Nat.div_eq_of_lt f1]
      exact ⟨f2, rfl, f3⟩
    · rw [if_neg hr, if_neg hr, absS_mk]
      exact ⟨by simp, by simp, by norm_num⟩
  refine ⟨⟨hwf, fun r => ?_⟩, fun r => ?_⟩
  · obtain ⟨k1, k2, k3⟩ := key r
    refine ⟨⟨?_, k3⟩, ?_⟩
    · rw [k1]
      intro T _
      by_cases hr : r ∈ gl
      · rw [if_pos hr, dg_mul_pow sw u hus]
        by_cases e : T = gl.idxOf r
        · rw [if_pos e]; exact hu
        · rw [if_neg e]; exact Nat.two_pow_pos _
      · rw [if_neg hr, dg_zero_left]; exact Nat.two_pow_pos _
    · rw [k2]; exact ok_zero sw gl.length
  · obtain ⟨k1, k2, _⟩ := key r
    refine ⟨?_, k1⟩
    show (absS (2^d) t' r >>> (64 + sw * gl.length)) >>> 64 = 0
    rw [k2]; rfl

theorem U_s (c : Raw) (p : SPar) (r : Nat) (h1 : 2 * c.v ≤ r) : U c p r = p.us := by
  have e1 : Nat.ble (Nat.succ r) c.v = false :=
    Bool.eq_false_iff.mpr (fun h => by have := ble_true h; omega)
  have e2 : Nat.ble (Nat.succ r) (2 * c.v) = false :=
    Bool.eq_false_iff.mpr (fun h => by have := ble_true h; omega)
  unfold U unitK
  rw [e1, e2]

/-- **An accepted E7 replay.** -/
def ERun (c : Raw) (gl : List Nat) : Prop :=
  ∃ (p : SPar) (a0 b : SSt), PGood c p 0 gl.length ∧ (∀ r ∈ gl, 2 * c.v ≤ r ∧ r < 2 * c.v + c.R) ∧
    gl.Nodup ∧ p.us < 2^(p.sw - 1) ∧
    (∀ r, a0.N r = 0 ∧ a0.P r = if r ∈ gl then p.us * 2^(p.sw * gl.idxOf r) else 0) ∧
    ItemsRun c p gl.length (prog c) a0 b ∧ ∀ S, S < c.v → b.P (c.v + S) = b.N (c.v + S)

theorem ERun.of_check {c : Raw} {p : SPar} {gl : List Nat} (h : eCheck c p gl = true) : ERun c gl := by
  unfold eCheck at h
  obtain ⟨hp, h1⟩ := pgood_of (gPre_sound c p 0 gl.length _ h)
  obtain ⟨hinc, h2⟩ := guard_true h1
  obtain ⟨hus, h3⟩ := guard_true h2
  obtain ⟨hus2, h4⟩ := guard_true h3
  rw [forceN_eq] at h4
  obtain ⟨hgl, hnd⟩ := incK_sound _ gl _ hinc
  have hu1 := ble_true hus
  have hu2 := ble_true hus2
  have hlt : ∀ r ∈ gl, r < 2^p.d := fun r hr => by have := (hgl r hr).2; have := hp.hd; omega
  obtain ⟨t0, hwf, hk, hval⟩ := gInitL_sound p.d p.sw p.us gl 0 (Trie.mk p.d) _ (Trie.wf_mk p.d) hlt hnd h4
  have hval' : ∀ r, absS (2^p.d) t0 r = if r ∈ gl then leaf0 p.sw p.us (0 + gl.idxOf r)
      else absS (2^p.d) (Trie.mk p.d) r := hval
  have husw : p.us < 2^(p.sw - 1) := by
    have e : Nat.pow 2 (Nat.sub p.sw 1) = 2^(p.sw - 1) := rfl
    omega
  obtain ⟨hI0, hinit⟩ := init_okL p.d p.sw p.us gl hp.hsw husw (by omega) t0 hwf hval'
  obtain ⟨tr3, hI3, hk3, hr⟩ := gItems_sound c p 0 gl.length hp (prog c) t0 _ hI0 hk
  refine ⟨p, _, _, hp, hgl, hnd, husw, hinit, hr, fun S hS => ?_⟩
  have := gFin_sound p.d p.sw (64 + p.sw * gl.length) p.uy c.v 0 0 tr3 hI3.wf c.v 0 hk3 S hS
  rw [Nat.zero_add, if_neg (by omega), Nat.add_zero] at this
  exact this

/-- **E7 from an accepted replay**: the column of a gauged slot in the y rows of the total matrix is zero. -/
theorem ERun.ycol {c : Raw} (hv : 0 < c.v) {gl : List Nat} (h : ERun c gl) (q : Fin c.R) (hq : 2 * c.v + q.val ∈ gl)
    (S : Fin c.v) : Mt c hv (lY S) (lS q) = 0 := by
  obtain ⟨p, a0, b, hp, hgl, hnd, husw, hi, hr, hfin⟩ := h
  obtain ⟨a1, r1, r2⟩ := ItemsRun_split c p gl.length _ _ a0 b hr
  obtain ⟨a2, ⟨rS, hsh⟩, r3⟩ := r2
  have rA := ItemsRun_cA c p gl.length _ a0 a1 r1
  have rB := ItemsRun_cB c p gl.length _ a2 b r3
  have hokA : ∀ t s, okA c t s = true → emb c (unemb c hv t) = t ∧ emb c (unemb c hv s) = s :=
    fun t s ho => ⟨emb_unemb hv t (okA_spec ho).1, emb_unemb hv s (okA_spec ho).2.1⟩
  have hokB : ∀ t s, okB c t s = true → emb c (unemb c hv t) = t ∧ emb c (unemb c hv s) = s :=
    fun t s ho => ⟨emb_unemb hv t (okB_spec ho).1, emb_unemb hv s (okB_spec ho).2.1⟩
  have hCA : Cm p.sw gl.length (U c p) (emb c) a1 = MA c hv * Cm p.sw gl.length (U c p) (emb c) a0 := by
    have := GRun_Cm p.sw gl.length (U c p) (okA c) (fun _ => true) (emb c) (unemb c hv) (unemb_emb hv) hokA
      (addsA c) a0 a1 rA
    rw [micF_true] at this
    exact this
  have hCB : Cm p.sw gl.length (U c p) (emb c) b = MB c hv * Cm p.sw gl.length (U c p) (emb c) a2 := by
    have := GRun_Cm p.sw gl.length (U c p) (okB c) (fun _ => true) (emb c) (unemb c hv) (unemb_emb hv) hokB
      (addsB c) a2 b rB
    rw [micF_true] at this
    exact this
  have hCS := cm_scat p 0 gl.length hp a1 a2 rS hsh
  have hus : p.us < 2^p.sw := lt_of_lt_of_le husw (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hT : gl.idxOf (2 * c.v + q.val) < gl.length := List.idxOf_lt_length_of_mem hq
  have u0 : (p.us : ℚ) ≠ 0 := by have := hp.hs; positivity
  have hC0 : ∀ j : Rl c, Cm p.sw gl.length (U c p) (emb c) a0 j ⟨gl.idxOf (2 * c.v + q.val), hT⟩
      = if j = lS q then 1 else 0 := by
    intro j
    show gcont p.sw (U c p) a0 (emb c j) (gl.idxOf (2 * c.v + q.val)) = _
    unfold gcont
    rw [(hi (emb c j)).1, (hi (emb c j)).2, dg_zero_left]
    by_cases hj : emb c j ∈ gl
    · rw [if_pos hj, dg_mul_pow p.sw p.us hus, U_s c p _ (hgl _ hj).1]
      by_cases e : j = lS q
      · have e' : emb c j = 2 * c.v + q.val := by rw [e]; rfl
        rw [if_pos (by rw [e']), if_pos e]
        field_simp
        simp
      · have e' : ¬ gl.idxOf (2 * c.v + q.val) = gl.idxOf (emb c j) := by
          intro he
          apply e
          have := (List.idxOf_inj hq).mp he
          rw [← unemb_emb hv j, ← this]
          exact unemb_emb hv (lS q)
        rw [if_neg e', if_neg e]
        simp
    · have e : ¬ j = lS q := fun e => hj (by rw [e]; exact hq)
      rw [if_neg hj, if_neg e, dg_zero_left]
      simp
  have key : Mt c hv (lY S) (lS q) = Cm p.sw gl.length (U c p) (emb c) b (lY S)
      ⟨gl.idxOf (2 * c.v + q.val), hT⟩ := by
    have e1 := mul_unitCol (Mt c hv) (Cm p.sw gl.length (U c p) (emb c) a0) (lS q) _ hC0 (lY S)
    rw [← e1]
    unfold Mt
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hCA, ← hCS, ← hCB]
  rw [key]
  show gcont p.sw (U c p) b (c.v + S.val) (gl.idxOf (2 * c.v + q.val)) = 0
  unfold gcont
  rw [hfin S.val S.isLt]
  simp

/-- **E7, the kernel check.** -/
theorem eCheck_sound {c : Raw} {p : SPar} {gl : List Nat} (hv : 0 < c.v) (h : eCheck c p gl = true)
    (q : Fin c.R) (hq : 2 * c.v + q.val ∈ gl) (S : Fin c.v) : Mt c hv (lY S) (lS q) = 0 :=
  ERun.ycol hv (ERun.of_check h) q hq S

end GS

#print axioms GS.eCheck_sound
