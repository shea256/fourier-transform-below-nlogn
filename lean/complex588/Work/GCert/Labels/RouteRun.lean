import Work.GCert.Labels.Route

/-!
# (key: gx-labels) THE ROUTE THEOREM of a legal label replay (spec statements 2 and 4, label part)

`Run.route`: a legal replay `Run p S gs S' rs` is, for every stage-B frame map `X` into an
address space with more than `h` coordinates, an exact route of the generalised engine from the
frames of `S` to the frames of `S'`, with scalar map the ordered product of the adds of `gs`
(`SSC.matP un (mic cf (gs.flatMap Gate.adds))`) AND with its transposed inverse
(`(SSC.matPinv un ..)ᵀ`), at the price of one block per listed rank; the end state is well formed.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-- the micro adds of a list of single adds `(tgt, src, coefficient)` -/
def mic (cf : Co → Coef) (l : List (Nat × Nat × Co)) : List Micro :=
  l.map fun x => Micro.add x.1 x.2.1 (cf x.2.2)

theorem adds_regs (g : Gate) (x : Nat × Nat × Co) (hx : x ∈ g.adds) :
    x.1 ∈ g.regs ∧ x.2.1 ∈ g.regs := by
  cases g with
  | out f s ts ex =>
    have hx' : x ∈ ts.map (fun q => (q.1, s, q.2)) := hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
    exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩)),
      List.mem_cons_self ..⟩
  | inn f t ss =>
    have hx' : x ∈ ss.map (fun q => (t, q.1, q.2)) := hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
    exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ (List.mem_map.mpr ⟨y, hy, rfl⟩)⟩

theorem rCl_tab (p : Par) (f : Nat) : ∀ (l : List Nat) (S : Trie), ∀ ca ∈ rCl p f S l,
    ∃ a, ca = p.tab.get a := by
  intro l
  induction l with
  | nil => intro S ca h; exact absurd h List.not_mem_nil
  | cons r l ih =>
    intro S ca h
    have h' : ca ∈ vCl p f S r ++ rCl p f (vOut f S r) l := h
    rcases List.mem_append.mp h' with h1 | h1
    · unfold vCl at h1
      split at h1
      · exact absurd h1 List.not_mem_nil
      · exact ⟨_, List.mem_singleton.mp h1⟩
    · exact ih _ ca h1

section
variable {ρ α : Type} [Fintype ρ] [DecidableEq ρ] [Fintype α] [DecidableEq α]
variable {p : Par} {emb : ρ → Nat} {un : Nat → ρ}

/-- **one gate**: its registers climb, then its adds act between identical frames. -/
theorem groute (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α)
    (W : Gate → List Micro)
    (hW : ∀ g t s c, Micro.add t s c ∈ W g → t ∈ g.regs ∧ s ∈ g.regs)
    (g : Gate) (S : Trie) (hS : S.wf p.d) (ok : gOk p S g) :
    GRoute (Lf p emb X S) (Lf p emb X (gOut S g)) (actPoint (matP un (W g)))
        (fun φ => rcost φ (gRanks p S g)) ∧ (gOut S g).wf p.d := by
  obtain ⟨ok1, ok2⟩ := ok
  have gb := tabK_good p.h p.tab C.hT g.frame
  have hcl : ∀ ca ∈ rCl p g.frame S g.regs, ∀ x, (lab p.h ca).Mem x →
      (lab p.h (p.tab.get g.frame)).Mem x := by
    intro ca hca
    obtain ⟨a, rfl⟩ := rCl_tab p g.frame g.regs S ca hca
    refine lab_sub (tabK_good p.h p.tab C.hT a) (fun q => ?_)
    exact ok2
      (fun c hc => by
        obtain ⟨a', rfl⟩ := rCl_tab p g.frame g.regs S c hc
        exact (tabK_good p.h p.tab C.hT a').bnd)
      (fun y => (lab p.h (p.tab.get g.frame)).Mem y) (mem_zero _)
      (fun x y hx hy => mem_add _ hx hy) (fun q hq => lab_bas gb ⟨q, hq⟩) _ hca q.val q.isLt
  obtain ⟨a, hS1⟩ := rroute C X hα g.frame g.regs S hS ok1 hcl
  have hlt := rOk_lt (p := p) g.frame g.regs S ok1
  have hget := rOut_get (p := p) g.frame g.regs S hS
    (fun r hr => lt_of_lt_of_le (hlt r hr) C.hn)
  have b := adds_route (Lf p emb X (gOut S g)) un (W g) (fun t s c h => by
    obtain ⟨ht, hs⟩ := hW g t s c h
    show X.Φ (lab p.h (p.tab.get ((rOut g.frame S g.regs).get (emb (un t)))))
      = X.Φ (lab p.h (p.tab.get ((rOut g.frame S g.regs).get (emb (un s)))))
    rw [C.hin t (hlt t ht), C.hin s (hlt s hs), hget t ht, hget s hs])
  exact ⟨(a.trans b).cast (fun φ => add_zero _), hS1⟩

/-- a list of gates. -/
theorem runroute (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α)
    (W : Gate → List Micro)
    (hW : ∀ g t s c, Micro.add t s c ∈ W g → t ∈ g.regs ∧ s ∈ g.regs) :
    ∀ (gs : List Gate) (S : Trie), S.wf p.d → runOk p S gs →
    GRoute (Lf p emb X S) (Lf p emb X (runOut S gs)) (actPoint (matP un (gs.flatMap W)))
        (fun φ => rcost φ (runRanks p S gs)) ∧ (runOut S gs).wf p.d := by
  intro gs
  induction gs with
  | nil =>
    intro S hS _
    refine ⟨?_, hS⟩
    show GRoute _ _ (actPoint (1 : Matrix ρ ρ ℚ)) _
    rw [actPoint_one']; exact GRoute.refl.cast (fun φ => (rcost_nil φ).symm)
  | cons g gs ih =>
    intro S hS ok
    obtain ⟨a, hS1⟩ := groute C X hα W hW g S hS ok.1
    obtain ⟨b, hS2⟩ := ih _ hS1 ok.2
    refine ⟨?_, hS2⟩
    show GRoute _ _ (actPoint (matP un (W g ++ gs.flatMap W))) _
    rw [matP_append, actPoint_mul]
    exact (a.trans b).cast (fun φ => (rcost_append φ _ _).symm)

theorem mic_flat (cf : Co → Coef) (gs : List Gate) :
    gs.flatMap (fun g => mic cf g.adds) = mic cf (gs.flatMap Gate.adds) := by
  unfold mic; rw [List.map_flatMap]

theorem mic_flat' (cf : Co → Coef) (gs : List Gate) :
    gs.flatMap (fun g => (mic cf g.adds).map swapNeg)
      = (mic cf (gs.flatMap Gate.adds)).map swapNeg := by
  unfold mic; rw [List.map_flatMap, List.map_flatMap]

/-- **THE ROUTE THEOREM of a legal label replay** (forward, and transposed inverse). -/
theorem Run.route (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α)
    (cf : Co → Coef) {S S' : Trie} {gs : List Gate} {rs : List Nat} (R : Run p S gs S' rs)
    (hS : S.wf p.d) :
    (GRoute (Lf p emb X S) (Lf p emb X S')
        (actPoint (matP un (mic cf (gs.flatMap Gate.adds)))) (fun φ => rcost φ rs) ∧
      GRoute (Lf p emb X S) (Lf p emb X S')
        (actPoint (matPinv un (mic cf (gs.flatMap Gate.adds)))ᵀ) (fun φ => rcost φ rs)) ∧
    S'.wf p.d := by
  obtain ⟨ok, rfl, rfl⟩ := R
  have hW1 : ∀ g t s c, Micro.add t s c ∈ mic cf (Gate.adds g) → t ∈ g.regs ∧ s ∈ g.regs := by
    intro g t s c h
    have h' : Micro.add t s c ∈ (Gate.adds g).map (fun x => Micro.add x.1 x.2.1 (cf x.2.2)) := h
    obtain ⟨x, hx, e⟩ := List.mem_map.mp h'
    have e' : Micro.add x.1 x.2.1 (cf x.2.2) = Micro.add t s c := e
    injection e' with e1 e2 e3
    subst e1; subst e2
    exact adds_regs g x hx
  have hW2 : ∀ g t s c, Micro.add t s c ∈ (mic cf (Gate.adds g)).map swapNeg →
      t ∈ g.regs ∧ s ∈ g.regs := by
    intro g t s c h
    obtain ⟨m, hm, e⟩ := List.mem_map.mp h
    have hm' : m ∈ (Gate.adds g).map (fun x => Micro.add x.1 x.2.1 (cf x.2.2)) := hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm'
    have e' : Micro.add x.2.1 x.1 (cf x.2.2).negate = Micro.add t s c := e
    injection e' with e1 e2 e3
    subst e1; subst e2
    exact ⟨(adds_regs g x hx).2, (adds_regs g x hx).1⟩
  obtain ⟨a, hS'⟩ := runroute C X hα (fun g => mic cf g.adds) hW1 gs S hS ok
  obtain ⟨b, _⟩ := runroute C X hα (fun g => (mic cf g.adds).map swapNeg) hW2 gs S hS ok
  rw [mic_flat] at a
  rw [mic_flat', matP_swap] at b
  exact ⟨⟨a, b⟩, hS'⟩

/-- a replay without adds (the final climbs) has scalar map `id`. -/
theorem Run.route_id (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α)
    {S S' : Trie} {gs : List Gate} {rs : List Nat} (R : Run p S gs S' rs) (hS : S.wf p.d)
    (hna : gs.flatMap Gate.adds = []) :
    GRoute (Lf p emb X S) (Lf p emb X S') id (fun φ => rcost φ rs) := by
  have a := (R.route C X hα (fun _ => ⟨false, 0, 1⟩) hS).1.1
  rw [hna] at a
  have e : actPoint (matP un (mic (fun _ => (⟨false, 0, 1⟩ : Coef)) [])) = id := actPoint_one'
  rw [e] at a
  exact a

end
end GLab

#print axioms GLab.Run.route
#print axioms GLab.Run.route_id
