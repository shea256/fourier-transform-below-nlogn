import Work.CarrierCheck.Mat
import Work.GCert.Labels.Sound

/-!
# (key: gx-labels) Legal label moves are routes of the generalised engine (spec statement 2)

Roles `ρ` with `emb : ρ → Nat`, `un : Nat → ρ` (`Ctx`); frames of the roles in the state `S`:
`Lf p emb X S q = X.Φ (lab h (tab.get (S.get (emb q))))` for a stage-B frame map `X`.

* `vroute`      one register named by a gate: nothing, or ONE block of rank `dim b - dim a`
                (`SMv.of_sub`, i.e. the frame lemma, through `BXMap.fmv`);
* `rroute`      the registers of a gate;
* `adds_route`  elementary adds between roles with IDENTICAL labels: a free gate.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-- label of register `r` in the state `S` -/
noncomputable def Par.labS (p : Par) (S : Trie) (r : Nat) : SLbl (Fin p.h) :=
  lab p.h (p.tab.get (S.get r))

section
variable {ρ α : Type} [Fintype ρ] [DecidableEq ρ] [Fintype α] [DecidableEq α]

/-- hypotheses common to all route statements: checked table, roles = registers `< n` -/
structure Ctx (p : Par) (emb : ρ → Nat) (un : Nat → ρ) : Prop where
  hT : tabK p.h p.tab = true
  hn : p.n ≤ 2 ^ p.d
  hun : ∀ q, un (emb q) = q
  hin : ∀ r, r < p.n → emb (un r) = r
  hlt : ∀ q, emb q < p.n

/-- frames of the roles in the state `S` -/
noncomputable def Lf (p : Par) (emb : ρ → Nat) (X : BXMap (Fin p.h) α) (S : Trie) : ρ → CMat α :=
  fun q => X.Φ (p.labS S (emb q))

variable {p : Par} {emb : ρ → Nat} {un : Nat → ρ}

theorem vOut_wf (f r : Nat) (S : Trie) (hS : S.wf p.d) : (vOut f S r).wf p.d := by
  unfold vOut; split
  · exact hS
  · exact Trie.wf_set p.d S hS r f

theorem vOut_get (f r r' : Nat) (S : Trie) (hS : S.wf p.d) (hr : r < 2 ^ p.d)
    (hr' : r' < 2 ^ p.d) : (vOut f S r).get r' = if r' = r then f else S.get r' := by
  unfold vOut
  by_cases e : S.get r = f
  · rw [if_pos e]
    by_cases e' : r' = r
    · rw [if_pos e', e', e]
    · rw [if_neg e']
  · rw [if_neg e, Trie.get_set p.d S hS r r' f hr hr']

/-- **one register named by a gate**: nothing, or one block of rank `dim b - dim a`. -/
theorem vroute (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α)
    (f r : Nat) (S : Trie) (hS : S.wf p.d) (ok : vOk p f S r)
    (hcl : ∀ ca ∈ vCl p f S r, ∀ x, (lab p.h ca).Mem x → (lab p.h (p.tab.get f)).Mem x) :
    GRoute (Lf p emb X S) (Lf p emb X (vOut f S r)) id (fun φ => rcost φ (vRanks p f S r)) := by
  obtain ⟨hr, hd⟩ := ok
  by_cases e : S.get r = f
  · have e1 : vOut f S r = S := by unfold vOut; rw [if_pos e]
    have e2 : vRanks p f S r = [] := by unfold vRanks; rw [if_pos e]
    rw [e1, e2]
    exact GRoute.refl.cast (fun φ => (rcost_nil φ).symm)
  · have e2 : vRanks p f S r = [cdim (p.tab.get f) - cdim (p.tab.get (S.get r))] := by
      unfold vRanks; rw [if_neg e]
    have e3 : p.tab.get (S.get r) ∈ vCl p f S r := by
      unfold vCl; rw [if_neg e]; exact List.mem_singleton.mpr rfl
    have dU : (lab p.h (p.tab.get (S.get r))).dim = cdim (p.tab.get (S.get r)) :=
      lab_dim (tabK_good p.h p.tab C.hT (S.get r))
    have dV : (lab p.h (p.tab.get f)).dim = cdim (p.tab.get f) :=
      lab_dim (tabK_good p.h p.tab C.hT f)
    have hVle : (lab p.h (p.tab.get f)).dim ≤ p.h := by
      have := Finset.card_le_univ (lab p.h (p.tab.get f)).s
      rw [Fintype.card_fin] at this
      exact this
    have mv : SMv (Fintype.card α) (lab p.h (p.tab.get (S.get r))) (lab p.h (p.tab.get f))
        [(lab p.h (p.tab.get f)).dim - (lab p.h (p.tab.get (S.get r))).dim] :=
      SMv.of_sub _ _ (hcl _ e3) (by rw [dU, dV]; exact hd e) (by omega)
    have st := (X.fmv mv).step (un r)
    have hrd : r < 2 ^ p.d := lt_of_lt_of_le hr C.hn
    have b := GRoute.on_role (Lf p emb X S) (un r) (X.Φ (lab p.h (p.tab.get f)))
      (c := fun φ => rcost φ [(lab p.h (p.tab.get f)).dim - (lab p.h (p.tab.get (S.get r))).dim])
      (by
        show GStep (un r) (X.Φ (lab p.h (p.tab.get (S.get (emb (un r)))))) _ _
        rw [C.hin r hr]; exact st)
    have eL : Function.update (Lf p emb X S) (un r) (X.Φ (lab p.h (p.tab.get f)))
        = Lf p emb X (vOut f S r) := by
      funext q
      by_cases hq : q = un r
      · subst hq
        rw [Function.update_self]
        show _ = X.Φ (lab p.h (p.tab.get ((vOut f S r).get (emb (un r)))))
        rw [C.hin r hr, vOut_get f r r S hS hrd hrd, if_pos rfl]
      · rw [Function.update_of_ne hq]
        have hne : emb q ≠ r := fun h => hq (by rw [← C.hun q, h])
        show X.Φ (lab p.h (p.tab.get (S.get (emb q))))
          = X.Φ (lab p.h (p.tab.get ((vOut f S r).get (emb q))))
        rw [vOut_get f r (emb q) S hS hrd (lt_of_lt_of_le (C.hlt q) C.hn), if_neg hne]
    rw [eL] at b
    rw [e2, ← dU, ← dV]
    exact b

/-- **the registers of a gate**: one block per climbing register. -/
theorem rroute (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α)
    (f : Nat) : ∀ (l : List Nat) (S : Trie), S.wf p.d → rOk p f S l →
    (∀ ca ∈ rCl p f S l, ∀ x, (lab p.h ca).Mem x → (lab p.h (p.tab.get f)).Mem x) →
    GRoute (Lf p emb X S) (Lf p emb X (rOut f S l)) id (fun φ => rcost φ (rRanks p f S l)) ∧
      (rOut f S l).wf p.d := by
  intro l
  induction l with
  | nil => intro S hS _ _; exact ⟨GRoute.refl.cast (fun φ => (rcost_nil φ).symm), hS⟩
  | cons r l ih =>
    intro S hS ok hcl
    have a := vroute C X hα f r S hS ok.1 (fun ca hca => hcl ca (List.mem_append_left _ hca))
    obtain ⟨b, hS2⟩ := ih (vOut f S r) (vOut_wf f r S hS) ok.2
      (fun ca hca => hcl ca (List.mem_append_right _ hca))
    exact ⟨(a.trans b).cast (fun φ => (rcost_append φ _ _).symm), hS2⟩

theorem rOk_lt (f : Nat) : ∀ (l : List Nat) (S : Trie), rOk p f S l → ∀ r ∈ l, r < p.n := by
  intro l
  induction l with
  | nil => intro S _ r hr; exact absurd hr List.not_mem_nil
  | cons a l ih =>
    intro S ok r hr
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; exact ok.1.1
    · exact ih _ ok.2 r h

/-- after the visits every register of the gate stands at the frame of the gate -/
theorem rOut_get (f : Nat) : ∀ (l : List Nat) (S : Trie), S.wf p.d → (∀ r ∈ l, r < 2 ^ p.d) →
    ∀ r ∈ l, (rOut f S l).get r = f := by
  have key : ∀ (l : List Nat) (S : Trie), S.wf p.d → (∀ r ∈ l, r < 2 ^ p.d) →
      ∀ r', r' < 2 ^ p.d → (rOut f S l).get r' = if r' ∈ l then f else S.get r' := by
    intro l
    induction l with
    | nil => intro S _ _ r' _; simp [rOut]
    | cons a l ih =>
      intro S hS hl r' hr'
      have ha : a < 2 ^ p.d := hl a (List.mem_cons_self ..)
      show (rOut f (vOut f S a) l).get r' = _
      rw [ih _ (vOut_wf f a S hS) (fun r hr => hl r (List.mem_cons_of_mem _ hr)) r' hr',
        vOut_get f a r' S hS ha hr']
      by_cases h1 : r' ∈ l
      · simp [h1]
      · by_cases h2 : r' = a
        · simp [h2]
        · simp [h1, h2]
  intro l S hS hl r hr
  rw [key l S hS hl r (hl r hr), if_pos hr]

/-- **elementary adds between roles with identical frames are a free gate.** -/
theorem adds_route (L : ρ → CMat α) (un : Nat → ρ) : ∀ (ms : List Micro),
    (∀ t s c, Micro.add t s c ∈ ms → L (un t) = L (un s)) →
    GRoute L L (actPoint (matP un ms)) (fun _ => 0) := by
  intro ms
  induction ms with
  | nil =>
    intro _
    show GRoute L L (actPoint (1 : Matrix ρ ρ ℚ)) _
    rw [actPoint_one']; exact GRoute.refl
  | cons m ms ih =>
    intro H
    have ih' := ih (fun t s c h => H t s c (List.mem_cons_of_mem _ h))
    cases m with
    | add t s c =>
      have e := H t s c (by simp)
      have g : GRoute L L (actPoint (addMat (un t) (un s) c.val)) (fun _ => 0) :=
        GRoute.gate _ L L (fun i j hij => by
          by_cases h1 : i = j
          · rw [h1]
          · by_cases h2 : i = un t ∧ j = un s
            · rw [h2.1, h2.2, e]
            · exact absurd (by simp [addMat, h1, h2]) hij)
      show GRoute L L (actPoint (matP un ms * addMat (un t) (un s) c.val)) _
      rw [actPoint_mul]
      exact (g.trans ih').cast (fun φ => by simp)
    | dir _ _ => exact ih'
    | shift _ _ => exact ih'
    | copy _ _ => exact ih'
    | erase _ => exact ih'
    | expect _ _ => exact ih'

end
end GLab

#print axioms GLab.vroute
#print axioms GLab.rroute
#print axioms GLab.adds_route
