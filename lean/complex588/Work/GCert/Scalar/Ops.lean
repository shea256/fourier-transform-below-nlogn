import Work.GCert.Scalar.Step

/-!
# (key: gx-scalar) The kernel check on gates, chunks and scatter rows runs the list of adds

* `GRun`    a list of single adds `(tgt, src, co)` on abstract states (only the selected sources;
  for these the kind test holds);
* `gGates_sound`, `gChunks_sound`   the check on gates runs `GRun` on `flatMap Gate.adds`;

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- a list of adds `(t, s, co)` on abstract states: the adds with `sel s` are done (and pass the
kind test `okf t s`), the others are skipped -/
def GRun (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool) :
    SSt → List (Nat × Nat × Co) → SSt → Prop
  | a, [], b => b = a
  | a, x :: l, b => if sel x.2.1 = true then
      (okf x.1 x.2.1 = true ∧ ∃ m, GStep sw n u x.1 x.2.1 (toCoef x.2.2) a m ∧
        GRun sw n u okf sel m l b)
    else GRun sw n u okf sel a l b

section
variable (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)

theorem GRun_append (l1 l2 : List (Nat × Nat × Co)) : ∀ (a m b : SSt),
    GRun sw n u okf sel a l1 m → GRun sw n u okf sel m l2 b →
    GRun sw n u okf sel a (l1 ++ l2) b := by
  induction l1 with
  | nil =>
    intro a m b h1 h2
    have e : m = a := h1
    rw [e] at h2
    exact h2
  | cons x l1 ih =>
    intro a m b h1 h2
    show if sel x.2.1 = true then _ else _
    have h1' : if sel x.2.1 = true then (okf x.1 x.2.1 = true ∧ ∃ m', GStep sw n u x.1 x.2.1
        (toCoef x.2.2) a m' ∧ GRun sw n u okf sel m' l1 m) else GRun sw n u okf sel a l1 m := h1
    by_cases hs : sel x.2.1 = true
    · rw [if_pos hs] at h1' ⊢
      obtain ⟨ho, m1, hst, hr⟩ := h1'
      exact ⟨ho, m1, hst, ih m1 m b hr h2⟩
    · rw [if_neg hs] at h1' ⊢
      exact ih a m b h1' h2

theorem GRun_split (l1 l2 : List (Nat × Nat × Co)) : ∀ (a b : SSt),
    GRun sw n u okf sel a (l1 ++ l2) b →
    ∃ m, GRun sw n u okf sel a l1 m ∧ GRun sw n u okf sel m l2 b := by
  induction l1 with
  | nil =>
    intro a b h
    exact ⟨a, rfl, h⟩
  | cons x l1 ih =>
    intro a b h
    have h' : if sel x.2.1 = true then (okf x.1 x.2.1 = true ∧ ∃ m', GStep sw n u x.1 x.2.1
        (toCoef x.2.2) a m' ∧ GRun sw n u okf sel m' (l1 ++ l2) b)
        else GRun sw n u okf sel a (l1 ++ l2) b := h
    by_cases hs : sel x.2.1 = true
    · rw [if_pos hs] at h'
      obtain ⟨ho, m1, hst, hr⟩ := h'
      obtain ⟨m, r1, r2⟩ := ih m1 b hr
      refine ⟨m, ?_, r2⟩
      show if sel x.2.1 = true then _ else _
      rw [if_pos hs]
      exact ⟨ho, m1, hst, r1⟩
    · rw [if_neg hs] at h'
      obtain ⟨m, r1, r2⟩ := ih a b h'
      refine ⟨m, ?_, r2⟩
      show if sel x.2.1 = true then _ else _
      rw [if_neg hs]
      exact r1

theorem GRun_skip (l : List (Nat × Nat × Co)) (h : ∀ x ∈ l, sel x.2.1 = false) (a : SSt) :
    GRun sw n u okf sel a l a := by
  induction l with
  | nil => exact rfl
  | cons x l ih =>
    show if sel x.2.1 = true then _ else _
    have hs : ¬ sel x.2.1 = true := by rw [h x (List.mem_cons_self ..)]; exact Bool.false_ne_true
    rw [if_neg hs]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

end

section
variable (d sw n tm K ux us uy v v2 : Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)
  (hsw : 1 ≤ sw) (htm : tm = maskW sw n) (hK : K = 64 + sw * n)
  (hu : ∀ r, 1 ≤ unitK ux us uy v v2 r)
include hsw htm hK hu

local notation "RUN" => GRun sw n (unitK ux us uy v v2) okf

theorem gOut_sound (s : Nat) (hs : sel s = true) (tgts : List (Nat × Co)) :
    ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gOut tm K (2^K) ux us uy v v2 okf s tgts tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
        RUN sel (absG d K tr) (tgts.map fun p => (p.1, s, p.2)) (absG d K tr') := by
  induction tgts with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons x l ih =>
    intro tr k hI h
    have h' : gAdd tm K (2^K) ux us uy v v2 x.1 s x.2 (okf x.1 s) tr
        (fun tr' => gOut tm K (2^K) ux us uy v v2 okf s l tr' k) = true := h
    obtain ⟨tr1, hI1, hk1, ho, hst⟩ := gAdd_sound d sw n tm K ux us uy v v2 hsw htm hK hu _ _ _ _ tr
      hI _ h'
    obtain ⟨tr2, hI2, hk2, hr⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_⟩
    show if sel s = true then _ else _
    rw [if_pos hs]
    exact ⟨ho, _, hst, hr⟩

theorem gInn_sound (t : Nat) (srcs : List (Nat × Co)) :
    ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gInn tm K (2^K) ux us uy v v2 okf sel t srcs tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
        RUN sel (absG d K tr) (srcs.map fun p => (t, p.1, p.2)) (absG d K tr') := by
  induction srcs with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons x l ih =>
    intro tr k hI h
    have h' : Bool.rec (motive := fun _ => Bool) (gInn tm K (2^K) ux us uy v v2 okf sel t l tr k)
        (gAdd tm K (2^K) ux us uy v v2 t x.1 x.2 (okf t x.1) tr
          (fun tr' => gInn tm K (2^K) ux us uy v v2 okf sel t l tr' k)) (sel x.1) = true := h
    cases hsx : sel x.1 with
    | false =>
      rw [hsx] at h'
      obtain ⟨tr2, hI2, hk2, hr⟩ := ih tr k hI h'
      refine ⟨tr2, hI2, hk2, ?_⟩
      show if sel x.1 = true then _ else _
      rw [hsx, if_neg Bool.false_ne_true]
      exact hr
    | true =>
      rw [hsx] at h'
      obtain ⟨tr1, hI1, hk1, ho, hst⟩ := gAdd_sound d sw n tm K ux us uy v v2 hsw htm hK hu _ _ _ _
        tr hI _ h'
      obtain ⟨tr2, hI2, hk2, hr⟩ := ih tr1 k hI1 hk1
      refine ⟨tr2, hI2, hk2, ?_⟩
      show if sel x.1 = true then _ else _
      rw [if_pos hsx]
      exact ⟨ho, _, hst, hr⟩

theorem gGate_sound (g : Gate) (tr : Trie) (k : Trie → Bool) (hI : GOk d sw n tr)
    (h : gGate tm K (2^K) ux us uy v v2 okf sel g tr k = true) :
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ RUN sel (absG d K tr) g.adds (absG d K tr') := by
  cases g with
  | out f s tgts ex =>
    have h' : Bool.rec (motive := fun _ => Bool) (k tr)
        (gOut tm K (2^K) ux us uy v v2 okf s tgts tr k) (sel s) = true := h
    cases hs : sel s with
    | false =>
      rw [hs] at h'
      refine ⟨tr, hI, h', GRun_skip sw n _ okf sel _ (fun x hx => ?_) _⟩
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
      exact hs
    | true =>
      rw [hs] at h'
      exact gOut_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu s hs tgts tr k hI h'
  | inn f t srcs =>
    exact gInn_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu t srcs tr k hI h

theorem gGates_sound (gs : List Gate) : ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
    gGates tm K (2^K) ux us uy v v2 okf sel gs tr k = true →
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
      RUN sel (absG d K tr) (gs.flatMap Gate.adds) (absG d K tr') := by
  induction gs with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons g gs ih =>
    intro tr k hI h
    have h' : gGate tm K (2^K) ux us uy v v2 okf sel g tr
        (fun tr' => gGates tm K (2^K) ux us uy v v2 okf sel gs tr' k) = true := h
    obtain ⟨tr1, hI1, hk1, r1⟩ := gGate_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu g tr _
      hI h'
    obtain ⟨tr2, hI2, hk2, r2⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_⟩
    rw [List.flatMap_cons]
    exact GRun_append sw n _ okf sel _ _ _ _ _ r1 r2

theorem gChunks_sound (cs : List (List Gate)) : ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
    gChunks tm K (2^K) ux us uy v v2 okf sel cs tr k = true →
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧
      RUN sel (absG d K tr) (cs.flatten.flatMap Gate.adds) (absG d K tr') := by
  induction cs with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, rfl⟩
  | cons gs cs ih =>
    intro tr k hI h
    have h' : gGates tm K (2^K) ux us uy v v2 okf sel gs tr
        (fun tr' => gChunks tm K (2^K) ux us uy v v2 okf sel cs tr' k) = true := h
    obtain ⟨tr1, hI1, hk1, r1⟩ := gGates_sound d sw n tm K ux us uy v v2 okf sel hsw htm hK hu gs tr _
      hI h'
    obtain ⟨tr2, hI2, hk2, r2⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_⟩
    rw [List.flatten_cons, List.flatMap_append]
    exact GRun_append sw n _ okf sel _ _ _ _ _ r1 r2

end

#print axioms gChunks_sound

end GS
