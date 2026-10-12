import Work.Combine.Split
import Work.GCert.Labels.Spec

/-!
# (key: gx-labels) Soundness of the kernel replay: `segK p gs S S' rs = true → Run p S gs S' rs`

Every kernel term of `Work.GCert.Labels.Def` is followed through its continuation:
`visitK_sound`, `loopN_sound`, `loopP_sound`, `gateK_sound` (the ONE elimination of a gate gives
`GSub` for all its climbs), `gatesK_sound`, and **`Run.of_seg`**.  No hypothesis on the tries.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary

theorem getK_true : ∀ (t : Trie) (key : Nat) (k : Nat → Bool),
    t.getK key k = true → k (t.get key) = true := by
  intro t
  induction t with
  | leaf v =>
    intro key k H
    rw [Trie.getK_leaf] at H
    by_cases hk : key = 0
    · rw [if_pos hk] at H; exact H
    · rw [if_neg hk] at H; exact absurd H Bool.false_ne_true
  | node l r il ir =>
    intro key k H
    rw [Trie.getK_node] at H
    show k (if key % 2 = 0 then l.get (key / 2) else r.get (key / 2)) = true
    by_cases hk : key % 2 = 0
    · rw [if_pos hk] at H ⊢; exact il _ _ H
    · rw [if_neg hk] at H ⊢; exact ir _ _ H

theorem visitK_sound (p : Par) (f r : Nat) (S : Trie) (A : Nat) (rs : List Nat)
    (k : Trie → Nat → List Nat → Bool)
    (H : visitK p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f (cdim (p.tab.get f)) r S A rs k
      = true) :
    ∃ A' rs', k (vOut f S r) A' rs' = true ∧ rs = vRanks p f S r ++ rs' ∧ vOk p f S r ∧
      Feeds p.h A A' (vCl p f S r) := by
  unfold visitK at H
  obtain ⟨g1, g2⟩ := guard_true H
  have hr : r < p.n := ble_true g1
  have g3 := getK_true _ _ _ g2
  beta_reduce at g3
  by_cases e : S.get r = f
  · have hb : Nat.beq (S.get r) f = true := by rw [e]; exact Nat.beq_refl f
    rw [hb] at g3
    refine ⟨A, rs, ?_, ?_, ⟨hr, fun h => absurd e h⟩, ?_⟩
    · unfold vOut; rw [if_pos e]; exact g3
    · unfold vRanks; rw [if_pos e]; rfl
    · unfold vCl; rw [if_pos e]; exact Feeds.refl _ _
  · have hb : Nat.beq (S.get r) f = false := by
      cases hbb : Nat.beq (S.get r) f
      · rfl
      · exact absurd (beq_true hbb) e
    rw [hb] at g3
    have g4 := getK_true _ _ _ g3
    beta_reduce at g4
    rw [forceN_eq] at g4
    obtain ⟨g5, g6⟩ := guard_true g4
    have hd : cdim (p.tab.get (S.get r)) < cdim (p.tab.get f) := ble_true g5
    cases rs with
    | nil => exact absurd g6 Bool.false_ne_true
    | cons r0 rs' =>
      obtain ⟨g7, g8⟩ := guard_true g6
      rw [forceN_eq] at g8
      have e0 : r0 = cdim (p.tab.get f) - cdim (p.tab.get (S.get r)) := beq_true g7
      refine ⟨A <<< (p.h * p.h) + cP p.h (p.tab.get (S.get r)), rs', ?_, ?_, ⟨hr, fun _ => hd⟩, ?_⟩
      · unfold vOut; rw [if_neg e]; exact g8
      · unfold vRanks; rw [if_neg e, e0]; rfl
      · unfold vCl; rw [if_neg e]; exact Feeds.step _ _ _

theorem loopN_sound (p : Par) (f : Nat) : ∀ (l : List Nat) (S : Trie) (A : Nat) (rs : List Nat)
    (k : Trie → Nat → List Nat → Bool),
    loopN p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f (cdim (p.tab.get f)) l S A rs k = true →
    ∃ A' rs', k (rOut f S l) A' rs' = true ∧ rs = rRanks p f S l ++ rs' ∧ rOk p f S l ∧
      Feeds p.h A A' (rCl p f S l) := by
  intro l
  induction l with
  | nil => intro S A rs k H; exact ⟨A, rs, H, rfl, trivial, Feeds.refl _ _⟩
  | cons r l ih =>
    intro S A rs k H
    have H' : visitK p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f (cdim (p.tab.get f)) r S A rs
        (fun S1 A1 rs1 => loopN p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f
          (cdim (p.tab.get f)) l S1 A1 rs1 k) = true := H
    obtain ⟨A1, rs1, hk, e1, ok1, F1⟩ := visitK_sound p f r S A rs _ H'
    obtain ⟨A2, rs2, hk2, e2, ok2, F2⟩ := ih _ _ _ _ hk
    exact ⟨A2, rs2, hk2, by rw [e1, e2, ← List.append_assoc]; rfl, ⟨ok1, ok2⟩, F1.trans F2⟩

theorem loopP_sound (p : Par) (f : Nat) : ∀ (l : List (Nat × Co)) (S : Trie) (A : Nat)
    (rs : List Nat) (k : Trie → Nat → List Nat → Bool),
    loopP p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f (cdim (p.tab.get f)) l S A rs k = true →
    ∃ A' rs', k (rOut f S (l.map Prod.fst)) A' rs' = true ∧
      rs = rRanks p f S (l.map Prod.fst) ++ rs' ∧ rOk p f S (l.map Prod.fst) ∧
      Feeds p.h A A' (rCl p f S (l.map Prod.fst)) := by
  intro l
  induction l with
  | nil => intro S A rs k H; exact ⟨A, rs, H, rfl, trivial, Feeds.refl _ _⟩
  | cons x l ih =>
    intro S A rs k H
    have H' : visitK p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f (cdim (p.tab.get f)) x.1 S A
        rs (fun S1 A1 rs1 => loopP p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f
          (cdim (p.tab.get f)) l S1 A1 rs1 k) = true := H
    obtain ⟨A1, rs1, hk, e1, ok1, F1⟩ := visitK_sound p f x.1 S A rs _ H'
    obtain ⟨A2, rs2, hk2, e2, ok2, F2⟩ := ih _ _ _ _ hk
    exact ⟨A2, rs2, hk2, by rw [e1, e2, ← List.append_assoc]; rfl, ⟨ok1, ok2⟩, F1.trans F2⟩

theorem body_sound (p : Par) (hh : 0 < p.h) (f s : Nat) (ts : List (Nat × Co)) (ex : List Nat)
    (S : Trie) (rs : List Nat) (k : Trie → List Nat → Bool)
    (H : p.tab.getK f (fun cb => forceN (Nat.land cb 255) fun db =>
      visitK p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f db s S 0 rs fun S1 A1 rs1 =>
      loopP p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f db ts S1 A1 rs1 fun S2 A2 rs2 =>
      loopN p.n p.tab (Nat.mul p.h p.h) (Nat.add 8 p.h) f db ex S2 A2 rs2 fun S3 A3 rs3 =>
      guard (elimT p.h (2 ^ p.h - 1) (rep p.h p.K) (Nat.shiftRight cb (Nat.add 8 p.h)) A3)
        (k S3 rs3)) = true) :
    ∃ rs', k (rOut f S (s :: (ts.map Prod.fst ++ ex))) rs' = true ∧
      rs = rRanks p f S (s :: (ts.map Prod.fst ++ ex)) ++ rs' ∧
      rOk p f S (s :: (ts.map Prod.fst ++ ex)) ∧
      GSub p f (rCl p f S (s :: (ts.map Prod.fst ++ ex))) := by
  have g1 := getK_true _ _ _ H
  beta_reduce at g1
  rw [forceN_eq] at g1
  obtain ⟨A1, rs1, hk1, e1, ok1, F1⟩ := visitK_sound p f s S 0 rs _ g1
  obtain ⟨A2, rs2, hk2, e2, ok2, F2⟩ := loopP_sound p f ts _ _ _ _ hk1
  obtain ⟨A3, rs3, hk3, e3, ok3, F3⟩ := loopN_sound p f ex _ _ _ _ hk2
  obtain ⟨g2, g3⟩ := guard_true hk3
  refine ⟨rs3, ?_, ?_, ?_, ?_⟩
  · show k (rOut f (vOut f S s) (ts.map Prod.fst ++ ex)) rs3 = true
    rw [rOut_append]; exact g3
  · show rs = vRanks p f S s ++ rRanks p f (vOut f S s) (ts.map Prod.fst ++ ex) ++ rs3
    rw [rRanks_append, e1, e2, e3]; simp only [List.append_assoc]
  · exact ⟨ok1, (rOk_append p f _ _ _).mpr ⟨ok2, ok3⟩⟩
  · intro hb Sp h0 hadd hcb
    have hall : AllIn p.h Sp A3 := elimT_sound p.h hh p.K _ A3 Sp h0 hadd hcb g2
    have F := (F1.trans F2).trans F3
    have e : rCl p f S (s :: (ts.map Prod.fst ++ ex))
        = (vCl p f S s ++ rCl p f (vOut f S s) (ts.map Prod.fst))
          ++ rCl p f (rOut f (vOut f S s) (ts.map Prod.fst)) ex := by
      show vCl p f S s ++ rCl p f (vOut f S s) (ts.map Prod.fst ++ ex) = _
      rw [rCl_append, List.append_assoc]
    rw [e] at hb ⊢
    exact (F hb Sp hall).2

theorem gateK_sound (p : Par) (hh : 0 < p.h) (g : Gate) (S : Trie) (rs : List Nat)
    (k : Trie → List Nat → Bool)
    (H : gateK p (2 ^ p.h - 1) (Nat.mul p.h p.h) (Nat.add 8 p.h) (rep p.h p.K) g S rs k = true) :
    ∃ rs', k (gOut S g) rs' = true ∧ rs = gRanks p S g ++ rs' ∧ gOk p S g := by
  cases g with
  | out f s ts ex =>
    obtain ⟨rs', a, b, c, d⟩ := body_sound p hh f s ts ex S rs k H
    exact ⟨rs', a, b, c, d⟩
  | inn f t ss =>
    obtain ⟨rs', a, b, c, d⟩ := body_sound p hh f t ss [] S rs k H
    rw [List.append_nil] at a b c d
    exact ⟨rs', a, b, c, d⟩

theorem gatesK_sound (p : Par) (hh : 0 < p.h) : ∀ (gs : List Gate) (S : Trie) (rs : List Nat)
    (k : Trie → List Nat → Bool),
    gatesK p (2 ^ p.h - 1) (Nat.mul p.h p.h) (Nat.add 8 p.h) (rep p.h p.K) gs S rs k = true →
    ∃ rs', k (runOut S gs) rs' = true ∧ rs = runRanks p S gs ++ rs' ∧ runOk p S gs := by
  intro gs
  induction gs with
  | nil => intro S rs k H; exact ⟨rs, H, rfl, trivial⟩
  | cons g gs ih =>
    intro S rs k H
    obtain ⟨rs1, hk, e1, ok1⟩ := gateK_sound p hh g S rs _ H
    obtain ⟨rs2, hk2, e2, ok2⟩ := ih _ _ _ hk
    exact ⟨rs2, hk2, by rw [e1, e2, ← List.append_assoc]; rfl, ⟨ok1, ok2⟩⟩

/-- **soundness of one segment of the label replay** -/
theorem Run.of_seg {p : Par} {gs : List Gate} {S S' : Trie} {rs : List Nat}
    (H : segK p gs S S' rs = true) : Run p S gs S' rs := by
  unfold segK at H
  obtain ⟨g0, g1⟩ := guard_true H
  have hh : 0 < p.h := ble_true g0
  rw [forceN_eq] at g1
  rw [forceN_eq] at g1
  obtain ⟨g2, g3⟩ := guard_true g1
  have eO : Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1) (Nat.sub (Nat.pow 2 p.h) 1)
      = rep p.h p.K := rep_of_mul p.h p.K _ hh (beq_true g2)
  rw [eO] at g3
  obtain ⟨rs1, hk, e1, ok⟩ := gatesK_sound p hh gs S rs _ g3
  obtain ⟨g4, g5⟩ := guard_true hk
  have eS := Trie.beqK_sound _ _ g4
  cases rs1 with
  | nil => exact ⟨ok, eS, by rw [e1, List.append_nil]⟩
  | cons a l => exact absurd g5 Bool.false_ne_true

end GLab

#print axioms GLab.Run.of_seg
