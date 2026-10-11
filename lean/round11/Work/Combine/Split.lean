import Work.SharedSumChecker.Impl
import Work.Combine.SplitDef

/-!
# (key: combine) The label check of a certificate in SEGMENTS (soundness)

`PCert.labelCheck_of_split`: three kernel evaluations (`segFirst`, `segMid`, `segLast` of
`Work.Combine.SplitDef`) on consecutive segments of the chunk list of a certificate, between
explicit states of the checker, give `c.labelCheck = true`, i.e. exactly the hypothesis of
`PCert.Valid.of_checks` of `Work.SharedSumChecker.Circ`.

The argument: every function of the checker is a continuation-passing test that either fails or
calls its continuation exactly once, on a state that does not depend on the continuation (`Det`).
So if a segment passes with the continuation "the state is `(T, F, C)`", then with ANY
continuation it returns what that continuation says about `(T, F, C)` (`chunksK_seg`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SSC

/-- a continuation-passing test that either fails or calls its continuation once, on a state
that does not depend on the continuation -/
def Det {σ : Type} (F : (σ → Bool) → Bool) : Prop := (∀ k, F k = false) ∨ ∃ s, ∀ k, F k = k s

namespace Det
variable {σ τ : Type}

theorem pure (s : σ) : Det (fun k : σ → Bool => k s) := Or.inr ⟨s, fun _ => rfl⟩

theorem fail : Det (fun _ : σ → Bool => false) := Or.inl (fun _ => rfl)

theorem congr {F G : (σ → Bool) → Bool} (h : ∀ k, F k = G k) (hG : Det G) : Det F := by
  rcases hG with g | ⟨s, g⟩
  · exact Or.inl (fun k => (h k).trans (g k))
  · exact Or.inr ⟨s, fun k => (h k).trans (g k)⟩

theorem bind {F : (σ → Bool) → Bool} {G : σ → (τ → Bool) → Bool} (hF : Det F)
    (hG : ∀ s, Det (G s)) : Det (fun k => F (fun s => G s k)) := by
  rcases hF with h | ⟨s, h⟩
  · exact Or.inl (fun k => h _)
  · rcases hG s with g | ⟨u, g⟩
    · exact Or.inl (fun k => (h (fun s => G s k)).trans (g k))
    · exact Or.inr ⟨u, fun k => (h (fun s => G s k)).trans (g k)⟩

theorem guardD (b : Bool) {F : (σ → Bool) → Bool} (hF : Det F) : Det (fun k => guard b (F k)) := by
  cases b
  · exact Or.inl (fun _ => rfl)
  · exact congr (fun _ => rfl) hF

end Det

theorem getK_det (t : Trie) : ∀ key, Det (fun k : Nat → Bool => t.getK key k) := by
  induction t with
  | leaf v =>
    intro key
    by_cases h : key = 0
    · exact Det.congr (fun k => by rw [Trie.getK_leaf]; simp [h]) (Det.pure v)
    · exact Det.congr (fun k => by rw [Trie.getK_leaf]; simp [h]) Det.fail
  | node l r ihl ihr =>
    intro key
    by_cases h : key % 2 = 0
    · exact Det.congr (fun k => by rw [Trie.getK_node]; simp [h]) (ihl (key/2))
    · exact Det.congr (fun k => by rw [Trie.getK_node]; simp [h]) (ihr (key/2))

theorem applyDirs_det (p : Par) (dirs : List Nat) : ∀ P c,
    Det (fun k : Nat × Nat → Bool => applyDirs p dirs P c (fun a b => k (a, b))) := by
  induction dirs with
  | nil => intro P c; exact Det.pure (P, c)
  | cons z zs ih =>
    intro P c
    cases hb : Nat.beq (Nat.land z p.hm) 0
    · refine Det.congr (fun k => ?_) (ih (updE p P z) (Nat.succ c))
      rw [applyDirs_cons, hb]
      exact forceN_eq _ _
    · refine Det.congr (fun k => ?_) Det.fail
      rw [applyDirs_cons, hb]

theorem onePart_det (p : Par) (pt : Part) (t : Trie) (f c : Nat) :
    Det (fun k : Nat × Trie × Nat × Nat → Bool =>
      onePart p pt t f c (fun L t' f' c' => k (L, t', f', c'))) := by
  cases pt with
  | old r dirs sh =>
    have h : Det (fun k : Nat × Trie × Nat × Nat → Bool => guard (Nat.ble (Nat.succ r) f)
        (t.getK r fun L0 => applyDirs p dirs L0 c fun a b =>
          k (updSE p a sh, t.set r (updSE p a sh), f, b))) :=
      Det.guardD _ (Det.bind (F := fun k1 : Nat → Bool => t.getK r k1)
        (G := fun L0 (k : Nat × Trie × Nat × Nat → Bool) => applyDirs p dirs L0 c fun a b =>
          k (updSE p a sh, t.set r (updSE p a sh), f, b))
        (getK_det t r)
        (fun L0 => Det.bind
          (F := fun k2 : Nat × Nat → Bool => applyDirs p dirs L0 c (fun a b => k2 (a, b)))
          (G := fun s (k : Nat × Trie × Nat × Nat → Bool) =>
            k (updSE p s.1 sh, t.set r (updSE p s.1 sh), f, s.2))
          (applyDirs_det p dirs L0 c) (fun s => Det.pure _)))
    refine Det.congr (fun k => ?_) h
    show guard (Nat.ble (Nat.succ r) f) (t.getK r fun L0 => applyDirs p dirs L0 c fun L1 c1 =>
        forceN (updSE p L1 sh) fun L => forceN c1 fun c2 => k (L, t.set r L, f, c2)) = _
    simp only [forceN_eq]
  | new r dirs sh =>
    have h : Det (fun k : Nat × Trie × Nat × Nat → Bool => guard (Nat.beq r f)
        (guard (Nat.ble (Nat.succ f) p.n) (applyDirs p dirs 0 c fun a b =>
          k (updSE p a sh, t.set r (updSE p a sh), Nat.succ f, b)))) :=
      Det.guardD _ (Det.guardD _ (Det.bind
        (F := fun k2 : Nat × Nat → Bool => applyDirs p dirs 0 c (fun a b => k2 (a, b)))
        (G := fun s (k : Nat × Trie × Nat × Nat → Bool) =>
          k (updSE p s.1 sh, t.set r (updSE p s.1 sh), Nat.succ f, s.2))
        (applyDirs_det p dirs 0 c) (fun s => Det.pure _)))
    refine Det.congr (fun k => ?_) h
    show guard (Nat.beq r f) (guard (Nat.ble (Nat.succ f) p.n) (applyDirs p dirs 0 c fun L1 c1 =>
        forceN (updSE p L1 sh) fun L => forceN c1 fun c2 => forceN (Nat.succ f) fun f2 =>
          k (L, t.set r L, f2, c2))) = _
    simp only [forceN_eq]
  | stay r =>
    have h : Det (fun k : Nat × Trie × Nat × Nat → Bool => t.getK r fun L => k (L, t, f, c)) :=
      Det.bind (F := fun k1 : Nat → Bool => t.getK r k1)
        (G := fun L (k : Nat × Trie × Nat × Nat → Bool) => k (L, t, f, c))
        (getK_det t r) (fun L => Det.pure _)
    exact Det.congr (fun k => rfl) h

theorem partsK_det (p : Par) (l : Nat) (pts : List Part) : ∀ t f c,
    Det (fun k : Trie × Nat × Nat → Bool => partsK p l pts t f c (fun t' f' c' => k (t', f', c'))) := by
  induction pts with
  | nil => intro t f c; exact Det.pure (t, f, c)
  | cons pt pts ih =>
    intro t f c
    have h : Det (fun k : Trie × Nat × Nat → Bool =>
        (fun k4 : Nat × Trie × Nat × Nat → Bool =>
          onePart p pt t f c (fun L t' f' c' => k4 (L, t', f', c')))
          (fun s => guard (Nat.beq s.1 l)
            (partsK p l pts s.2.1 s.2.2.1 s.2.2.2 (fun t' f' c' => k (t', f', c'))))) :=
      Det.bind (onePart_det p pt t f c) (fun s => Det.guardD (Nat.beq s.1 l) (ih s.2.1 s.2.2.1 s.2.2.2))
    exact Det.congr (fun k => rfl) h

theorem opK_det (p : Par) (op : Op) (t : Trie) (f c : Nat) :
    Det (fun k : Trie × Nat × Nat → Bool => opK p op t f c (fun t' f' c' => k (t', f', c'))) := by
  cases op with
  | bip srcs tgts coefs =>
    cases srcs with
    | nil => exact Det.congr (fun k => rfl) Det.fail
    | cons s0 rest =>
      have h : Det (fun k : Trie × Nat × Nat → Bool =>
          (fun k4 : Nat × Trie × Nat × Nat → Bool =>
            onePart p s0 t f c (fun L t' f' c' => k4 (L, t', f', c')))
            (fun s => (fun k3 : Trie × Nat × Nat → Bool =>
                partsK p s.1 rest s.2.1 s.2.2.1 s.2.2.2 (fun t' f' c' => k3 (t', f', c')))
              (fun u => partsK p s.1 tgts u.1 u.2.1 u.2.2 (fun t' f' c' => k (t', f', c'))))) :=
        Det.bind (onePart_det p s0 t f c) (fun s =>
          Det.bind (partsK_det p s.1 rest s.2.1 s.2.2.1 s.2.2.2)
            (fun u => partsK_det p s.1 tgts u.1 u.2.1 u.2.2))
      exact Det.congr (fun k => rfl) h
  | copy s d =>
    have h : Det (fun k : Trie × Nat × Nat → Bool => guard (Nat.ble (Nat.succ d) f)
        (t.getK s fun L => k (t.set d L, f, c))) :=
      Det.guardD _ (Det.bind (F := fun k1 : Nat → Bool => t.getK s k1)
        (G := fun L (k : Trie × Nat × Nat → Bool) => k (t.set d L, f, c))
        (getK_det t s) (fun L => Det.pure _))
    exact Det.congr (fun k => rfl) h
  | copyNew s d =>
    have h : Det (fun k : Trie × Nat × Nat → Bool => guard (Nat.beq d f)
        (guard (Nat.ble (Nat.succ f) p.n) (t.getK s fun L => k (t.set d L, Nat.succ f, c)))) :=
      Det.guardD _ (Det.guardD _ (Det.bind (F := fun k1 : Nat → Bool => t.getK s k1)
        (G := fun L (k : Trie × Nat × Nat → Bool) => k (t.set d L, Nat.succ f, c))
        (getK_det t s) (fun L => Det.pure _)))
    refine Det.congr (fun k => ?_) h
    show guard (Nat.beq d f) (guard (Nat.ble (Nat.succ f) p.n)
      (t.getK s fun L => forceN (Nat.succ f) fun f2 => k (t.set d L, f2, c))) = _
    simp only [forceN_eq]
  | erase d => exact Det.pure (t, f, c)
  | expect r e =>
    have h : Det (fun k : Trie × Nat × Nat → Bool =>
        t.getK r fun L => guard (Nat.beq L e) (k (t, f, c))) :=
      Det.bind (F := fun k1 : Nat → Bool => t.getK r k1)
        (G := fun L (k : Trie × Nat × Nat → Bool) => guard (Nat.beq L e) (k (t, f, c)))
        (getK_det t r) (fun L => Det.guardD _ (Det.pure _))
    exact Det.congr (fun k => rfl) h

theorem opsK_det (p : Par) (ops : List Op) : ∀ t f c,
    Det (fun k : Trie × Nat × Nat → Bool => opsK p ops t f c (fun t' f' c' => k (t', f', c'))) := by
  induction ops with
  | nil => intro t f c; exact Det.pure (t, f, c)
  | cons op ops ih =>
    intro t f c
    have h : Det (fun k : Trie × Nat × Nat → Bool =>
        (fun k3 : Trie × Nat × Nat → Bool => opK p op t f c (fun t' f' c' => k3 (t', f', c')))
          (fun s => opsK p ops s.1 s.2.1 s.2.2 (fun t' f' c' => k (t', f', c')))) :=
      Det.bind (opK_det p op t f c) (fun s => ih s.1 s.2.1 s.2.2)
    exact Det.congr (fun k => rfl) h

theorem chunksK_det (p : Par) (cs : List (List Op)) : ∀ t f c,
    Det (fun k : Trie × Nat × Nat → Bool => chunksK p cs t f c (fun t' f' c' => k (t', f', c'))) := by
  induction cs with
  | nil => intro t f c; exact Det.pure (t, f, c)
  | cons ops cs ih =>
    intro t f c
    have h : Det (fun k : Trie × Nat × Nat → Bool =>
        (fun k3 : Trie × Nat × Nat → Bool => opsK p ops t f c (fun t' f' c' => k3 (t', f', c')))
          (fun s => chunksK p cs s.1 s.2.1 s.2.2 (fun t' f' c' => k (t', f', c')))) :=
      Det.bind (opsK_det p ops t f c) (fun s => ih s.1 s.2.1 s.2.2)
    exact Det.congr (fun k => rfl) h

theorem chunksK_append (p : Par) (a b : List (List Op)) : ∀ (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool),
    chunksK p (a ++ b) t f c k = chunksK p a t f c (fun t' f' c' => chunksK p b t' f' c' k) := by
  induction a with
  | nil => intro t f c k; rfl
  | cons ops a ih =>
    intro t f c k
    rw [List.cons_append, chunksK_cons, chunksK_cons]
    congr 1
    funext t' f' c'
    exact ih t' f' c' k

theorem Trie.beqK_sound : ∀ (t t' : Trie), Trie.beqK t t' = true → t = t' := by
  intro t
  induction t with
  | leaf v =>
    intro t' h
    cases t' with
    | leaf v' =>
      have h' : Nat.beq v v' = true := h
      rw [beq_true h']
    | node l r => exact absurd h Bool.false_ne_true
  | node l r ihl ihr =>
    intro t' h
    cases t' with
    | leaf v' => exact absurd h Bool.false_ne_true
    | node l' r' =>
      have h' : guard (Trie.beqK l l') (Trie.beqK r r') = true := h
      obtain ⟨h1, h2⟩ := guard_true h'
      rw [ihl l' h1, ihr r' h2]

theorem stEqK_sound (T : Trie) (F C : Nat) (t : Trie) (f c : Nat) (h : stEqK T F C t f c = true) :
    t = T ∧ f = F ∧ c = C := by
  have h' : guard (Trie.beqK t T) (guard (Nat.beq f F) (Nat.beq c C)) = true := h
  obtain ⟨h1, h2⟩ := guard_true h'
  obtain ⟨h3, h4⟩ := guard_true h2
  exact ⟨Trie.beqK_sound t T h1, beq_true h3, beq_true h4⟩

/-- **a segment that passes with "the state is `(T, F, C)`" behaves, for every continuation,
like that continuation on `(T, F, C)`** -/
theorem chunksK_seg (p : Par) (cs : List (List Op)) (t : Trie) (f c : Nat) (T : Trie) (F C : Nat)
    (h : chunksK p cs t f c (stEqK T F C) = true) (k : Trie → Nat → Nat → Bool) :
    chunksK p cs t f c k = k T F C := by
  rcases chunksK_det p cs t f c with h0 | ⟨s, hs⟩
  · have h1 : chunksK p cs t f c (stEqK T F C) = false := h0 (fun s => stEqK T F C s.1 s.2.1 s.2.2)
    rw [h] at h1
    exact absurd h1 (by decide)
  · have h1 : chunksK p cs t f c (stEqK T F C) = stEqK T F C s.1 s.2.1 s.2.2 :=
      hs (fun s => stEqK T F C s.1 s.2.1 s.2.2)
    rw [h] at h1
    obtain ⟨e1, e2, e3⟩ := stEqK_sound T F C _ _ _ h1.symm
    have h2 : chunksK p cs t f c k = k s.1 s.2.1 s.2.2 := hs (fun s => k s.1 s.2.1 s.2.2)
    rw [h2, e1, e2, e3]

/-- **the label check from three segments** -/
theorem check_split3 (p : Par) (inits : List Nat) (csA csB csC : List (List Op))
    (fs : List (List FinE)) (N : Nat) (T1 : Trie) (F1 C1 : Nat) (T2 : Trie) (F2 C2 : Nat)
    (hA : segFirst p inits csA T1 F1 C1 = true) (hB : segMid p csB T1 F1 C1 T2 F2 C2 = true)
    (hC : segLast p csC fs N T2 F2 C2 = true) :
    check p inits (csA ++ (csB ++ csC)) fs N = true := by
  have hA1 : (initK inits (Trie.mk p.d) 0 fun t0 f0 =>
      guard (Nat.ble f0 p.n) (chunksK p csA t0 f0 0 (stEqK T1 F1 C1))) = true := hA
  rw [initK_eq] at hA1
  obtain ⟨hg, hA'⟩ := guard_true hA1
  show (initK inits (Trie.mk p.d) 0 fun t0 f0 => guard (Nat.ble f0 p.n)
    (chunksK p (csA ++ (csB ++ csC)) t0 f0 0 fun t1 _ c1 =>
      finsK p t1 fs 0 c1 fun _ c2 => Nat.beq c2 N)) = true
  rw [initK_eq, hg]
  show chunksK p (csA ++ (csB ++ csC)) _ _ 0 _ = true
  rw [chunksK_append, chunksK_seg p csA _ _ _ T1 F1 C1 hA', chunksK_append,
    chunksK_seg p csB _ _ _ T2 F2 C2 hB]
  exact hC

/-- **the label check of a certificate from three segments of its chunk list** -/
theorem PCert.labelCheck_of_split (c : PCert) (n1 n2 : Nat) (T1 : Trie) (F1 C1 : Nat) (T2 : Trie)
    (F2 C2 : Nat)
    (hA : segFirst c.p c.inits (c.cs.take n1) T1 F1 C1 = true)
    (hB : segMid c.p ((c.cs.drop n1).take n2) T1 F1 C1 T2 F2 C2 = true)
    (hC : segLast c.p ((c.cs.drop n1).drop n2) c.fins c.N T2 F2 C2 = true) :
    c.labelCheck = true := by
  have h := check_split3 c.p c.inits _ _ _ c.fins c.N T1 F1 C1 T2 F2 C2 hA hB hC
  rw [List.take_append_drop, List.take_append_drop] at h
  exact h

end SSC

#print axioms SSC.chunksK_seg
#print axioms SSC.PCert.labelCheck_of_split
