import Work.GCert.Scalar.Ops

/-!
# (key: gx-scalar) The kernel check on the scatter rows runs the list of scatter adds

`gScat_sound`: the check on the scatter rows runs `GRun` on `scatAddsFrom`, there are `v` rows
(the last target is `2 v - 1`), every total index is below `rl`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- the adds of one scatter row: `t += co * (register of total k)` -/
def scatRowAdds (ret : List (Nat × Nat)) (t : Nat) (l : List (Nat × Co)) : List (Nat × Nat × Co) :=
  l.map fun x => (t, (ret.getD x.1 (0, 0)).1, x.2)

/-- the adds of the scatter rows of the targets `t, t+1, ..` -/
def scatAddsFrom (ret : List (Nat × Nat)) : Nat → List (List (Nat × Co)) → List (Nat × Nat × Co)
  | _, [] => []
  | t, l :: rows => scatRowAdds ret t l ++ scatAddsFrom ret (t+1) rows

section
variable (d sw n tm K ux us uy v v2 : Nat) (okf : Nat → Nat → Bool)
  (hsw : 1 ≤ sw) (htm : tm = maskW sw n) (hK : K = 64 + sw * n)
  (hu : ∀ r, 1 ≤ unitK ux us uy v v2 r)
include hsw htm hK hu

local notation "RUN" => GRun sw n (unitK ux us uy v v2) okf

theorem gScatRow_sound (ret : List (Nat × Nat)) (rl t : Nat) (l : List (Nat × Co)) :
    ∀ (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gScatRow tm K (2^K) ux us uy v v2 okf ret rl t l tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ (∀ x ∈ l, x.1 < rl) ∧
        RUN (fun _ => true) (absG d K tr) (scatRowAdds ret t l) (absG d K tr') := by
  induction l with
  | nil => intro tr k hI h; exact ⟨tr, hI, h, fun x hx => absurd hx List.not_mem_nil, rfl⟩
  | cons x l ih =>
    intro tr k hI h
    have h' : guard (Nat.ble (Nat.succ x.1) rl) (forceN (ret.getD x.1 (0, 0)).1 fun s =>
        gAdd tm K (2^K) ux us uy v v2 t s x.2 (okf t s) tr
          (fun tr' => gScatRow tm K (2^K) ux us uy v v2 okf ret rl t l tr' k)) = true := h
    obtain ⟨hlt, h2⟩ := guard_true h'
    rw [forceN_eq] at h2
    obtain ⟨tr1, hI1, hk1, ho, hst⟩ := gAdd_sound d sw n tm K ux us uy v v2 hsw htm hK hu _ _ _ _ tr
      hI _ h2
    obtain ⟨tr2, hI2, hk2, hb, hr⟩ := ih tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with e | e
      · rw [e]; exact ble_true hlt
      · exact hb y e
    · show if (fun _ => true) (ret.getD x.1 (0, 0)).1 = true then _ else _
      rw [if_pos rfl]
      exact ⟨ho, _, hst, hr⟩

theorem gScat_sound (ret : List (Nat × Nat)) (rl : Nat) (rows : List (List (Nat × Co))) :
    ∀ (t : Nat) (tr : Trie) (k : Trie → Bool), GOk d sw n tr →
      gScat tm K (2^K) ux us uy v v2 okf ret rl rows t tr k = true →
      ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ t + rows.length = v2 ∧
        (∀ l ∈ rows, ∀ x ∈ l, x.1 < rl) ∧
        RUN (fun _ => true) (absG d K tr) (scatAddsFrom ret t rows) (absG d K tr') := by
  induction rows with
  | nil =>
    intro t tr k hI h
    obtain ⟨h1, h2⟩ := guard_true (show guard (Nat.beq t v2) (k tr) = true from h)
    exact ⟨tr, hI, h2, beq_true h1, fun l hl => absurd hl List.not_mem_nil, rfl⟩
  | cons l rows ih =>
    intro t tr k hI h
    have h' : gScatRow tm K (2^K) ux us uy v v2 okf ret rl t l tr (fun tr' =>
        forceN (Nat.succ t) fun t2 => gScat tm K (2^K) ux us uy v v2 okf ret rl rows t2 tr' k)
        = true := h
    obtain ⟨tr1, hI1, hk1, hb1, r1⟩ := gScatRow_sound d sw n tm K ux us uy v v2 okf hsw htm hK hu
      ret rl t l tr _ hI h'
    rw [forceN_eq] at hk1
    obtain ⟨tr2, hI2, hk2, hlen, hb2, r2⟩ := ih (t+1) tr1 k hI1 hk1
    refine ⟨tr2, hI2, hk2, ?_, ?_, GRun_append sw n _ okf _ _ _ _ _ _ r1 r2⟩
    · rw [List.length_cons]; omega
    · intro l' hl'
      rcases List.mem_cons.mp hl' with e | e
      · rw [e]; exact hb1
      · exact hb2 l' e

end

#print axioms gScat_sound

end GS
