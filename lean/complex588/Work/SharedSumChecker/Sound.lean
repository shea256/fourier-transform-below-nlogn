import Work.SharedSumChecker.Phase

/-!
# Shared-sum checker: labelled micro-programs give a `Route` of the scratch engine

A certificate is expanded into MICRO-OPS (`dir`, `shift`, `add`, `copy`, `erase`).  If the
labels justify every gate (`Ok`), the corresponding word of the engine is a `Route`
(Work.Scratch.Engine) between the matrices of the labels, with one PAID directional move per
`dir` micro-op.  The lift of the label space `F_2^h` into the address space of the engine is
arbitrary (`Lift`): one certificate serves every invocation of a stage.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving.Binary OAI.PowerSaving.RAM Finset Matrix

/-- How the label space `F_2^h` sits in the address space `F_2^α` of the engine: a linear map
`ι` on directions with adjoint `π` on addresses. -/
structure Lift (p : Par) (α : Type*) [Fintype α] [DecidableEq α] where
  ι : (Nat → F) → Space α
  π : Space α → (Nat → F)
  adj : ∀ z x, dot (ι z) x = ∑ i ∈ range p.h, z i * π x i
  inj : ∀ z : Nat, z &&& p.hm ≠ 0 → ι (vec z) ≠ 0

section
variable {p : Par} {α : Type*} [Fintype α] [DecidableEq α]

/-- matrix of a role whose label is `L` (`Base` is a common right factor) -/
noncomputable def Lift.mat (lf : Lift p α) (Base : CMat α) (L : Nat) : CMat α :=
  wrap (fun x => Phi p L (lf.π x)) * Base

theorem Lift.mat_dir (lf : Lift p α) (hh : 0 < p.h) (hw : p.h < p.w) (Base : CMat α) (L z : Nat) :
    OAI.PowerSaving.Binary.dir (lf.ι (vec z)) * lf.mat Base L
      = lf.mat Base (upd p L (spread p z) z) := by
  unfold Lift.mat
  rw [← mul_assoc, dir_phase, wrap_mul]
  congr 2
  funext x
  rw [lf.adj, Phi_upd p hh hw, mul_comm]

theorem Lift.mat_shift (lf : Lift p α) (hh : 0 < p.h) (hw : p.h < p.w) (Base : CMat α) (L z : Nat) :
    OAI.PowerSaving.Binary.shift (lf.ι (vec z)) * lf.mat Base L = lf.mat Base (updS p L z) := by
  unfold Lift.mat
  rw [← mul_assoc, shift_phase, wrap_mul]
  congr 2
  funext x
  rw [lf.adj, Phi_updS p hh hw, mul_comm]

theorem Lift.mat_zero (lf : Lift p α) (Base : CMat α) : lf.mat Base 0 = Base := by
  unfold Lift.mat
  simp only [Phi_zero]
  rw [wrap_one, one_mul]

end

/-! ## micro-ops -/

inductive Micro where
  | dir (r z : Nat)
  | shift (r z : Nat)
  | add (t s : Nat) (c : Coef)
  | copy (s d : Nat)
  | erase (d : Nat)
  | expect (r e : Nat)

/-- the rational number `± num / den` -/
noncomputable def Coef.val (c : Coef) : ℚ :=
  (if c.neg then -(c.num : ℚ) else (c.num : ℚ)) / (c.den : ℚ)

def stepLab (p : Par) : Micro → (Nat → Nat) → (Nat → Nat)
  | .dir r z, lab => Function.update lab r (upd p (lab r) (spread p z) z)
  | .shift r z, lab => Function.update lab r (updS p (lab r) z)
  | .add _ _ _, lab => lab
  | .copy s d, lab => Function.update lab d (lab s)
  | .erase _, lab => lab
  | .expect _ _, lab => lab

def okMicro (p : Par) : Micro → (Nat → Nat) → Prop
  | .dir r z, _ => r < p.n ∧ z &&& p.hm ≠ 0
  | .shift r _, _ => r < p.n
  | .add t s _, lab => t < p.n ∧ s < p.n ∧ lab t = lab s
  | .copy s d, _ => s < p.n ∧ d < p.n
  | .erase _, _ => True
  | .expect r e, lab => r < p.n ∧ lab r = dec e

def runLab (p : Par) (lab : Nat → Nat) (ms : List Micro) : Nat → Nat :=
  ms.foldl (fun l m => stepLab p m l) lab

/-- every gate of the micro-program finds its two roles at one label -/
def Ok (p : Par) : (Nat → Nat) → List Micro → Prop
  | _, [] => True
  | lab, m :: ms => okMicro p m lab ∧ Ok p (stepLab p m lab) ms

def tollM : Micro → Nat
  | .dir _ _ => 1
  | _ => 0

/-- number of paid kernel moves -/
def countM (ms : List Micro) : Nat := (ms.map tollM).sum

theorem runLab_nil (p : Par) (lab : Nat → Nat) : runLab p lab [] = lab := rfl
theorem runLab_cons (p : Par) (lab : Nat → Nat) (m : Micro) (ms : List Micro) :
    runLab p lab (m :: ms) = runLab p (stepLab p m lab) ms := rfl
theorem runLab_append (p : Par) (lab : Nat → Nat) (a b : List Micro) :
    runLab p lab (a ++ b) = runLab p (runLab p lab a) b := by
  simp [runLab, List.foldl_append]

theorem Ok_append (p : Par) (lab : Nat → Nat) (a b : List Micro) :
    Ok p lab (a ++ b) ↔ Ok p lab a ∧ Ok p (runLab p lab a) b := by
  induction a generalizing lab with
  | nil => simp [Ok, runLab_nil]
  | cons m ms ih =>
    simp only [List.cons_append, Ok, runLab_cons, ih, and_assoc]

theorem countM_nil : countM [] = 0 := rfl
theorem countM_cons (m : Micro) (ms : List Micro) : countM (m :: ms) = tollM m + countM ms := by
  simp [countM]
theorem countM_append (a b : List Micro) : countM (a ++ b) = countM a + countM b := by
  simp [countM]

/-! ## scalar action -/

section
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

noncomputable def gMicro (emb : Nat → ρ) : Micro → (ρ → ℂ) → (ρ → ℂ)
  | .add t s c, x => fun r => if r = emb t then x (emb t) + ((c.val : ℚ) : ℂ) * x (emb s) else x r
  | .copy s d, x => fun r => if r = emb d then x (emb s) else x r
  | .erase d, x => fun r => if r = emb d then 0 else x r
  | .dir _ _, x => x
  | .shift _ _, x => x
  | .expect _ _, x => x

/-- scalar map of a micro-program (frame changes do nothing) -/
noncomputable def gsemM (emb : Nat → ρ) : List Micro → (ρ → ℂ) → (ρ → ℂ)
  | [] => id
  | m :: ms => gsemM emb ms ∘ gMicro emb m

theorem gsemM_nil (emb : Nat → ρ) : gsemM emb [] = id := rfl
theorem gsemM_cons (emb : Nat → ρ) (m : Micro) (ms : List Micro) :
    gsemM emb (m :: ms) = gsemM emb ms ∘ gMicro emb m := rfl
theorem gsemM_append (emb : Nat → ρ) (a b : List Micro) :
    gsemM emb (a ++ b) = gsemM emb b ∘ gsemM emb a := by
  induction a with
  | nil => rfl
  | cons m ms ih => rw [List.cons_append, gsemM_cons, gsemM_cons, ih]; rfl

/-- `a += c * b` as a rational matrix -/
def addMat (a b : ρ) (c : ℚ) : Matrix ρ ρ ℚ :=
  fun i j => (if i = j then 1 else 0) + (if i = a ∧ j = b then c else 0)

theorem actPoint_addMat (a b : ρ) (c : ℚ) (x : ρ → ℂ) (r : ρ) :
    actPoint (addMat a b c) x r = if r = a then x a + (c:ℂ) * x b else x r := by
  unfold actPoint addMat
  simp only [Rat.cast_add, add_mul, sum_add_distrib]
  rw [sum_ind_right r x]
  by_cases h : r = a
  · subst h
    rw [if_pos rfl]
    congr 1
    rw [sum_eq_single b]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · rw [if_neg h]
    have h0 : ∑ j, (((if r = a ∧ j = b then c else 0 : ℚ)) : ℂ) * x j = 0 :=
      sum_eq_zero (fun j _ => by simp [h])
    rw [h0, add_zero]

variable {p : Par} {α : Type*} [Fintype α] [DecidableEq α]

theorem route_refl (S : ρ → CMat α) : Route S S id 0 :=
  ⟨[], rfl, fun _ _ => rfl⟩

theorem micro_step (lf : Lift p α) (hh : 0 < p.h) (hw : p.h < p.w) (Base : CMat α) (emb : Nat → ρ)
    (hemb : ∀ i j, i < p.n → j < p.n → emb i = emb j → i = j)
    (m : Micro) (lab : Nat → Nat) (S : ρ → CMat α) (hok : okMicro p m lab)
    (hS : ∀ r, r < p.n → S (emb r) = lf.mat Base (lab r)) :
    ∃ T, Route S T (gMicro emb m) (tollM m) ∧
      (∀ r, r < p.n → T (emb r) = lf.mat Base (stepLab p m lab r)) ∧
      (∀ q, (∀ r, r < p.n → emb r ≠ q) → T q = S q) := by
  cases m with
  | dir r z =>
    obtain ⟨hr, hz⟩ := hok
    have hR := Route.on_role S (emb r) (OAI.PowerSaving.Binary.dir (lf.ι (vec z))) 1
      ⟨[Move.dir (emb r) (lf.ι (vec z)) (lf.inj z hz)], rfl, fun f x => rfl⟩
    refine ⟨_, hR, ?_, ?_⟩
    · intro r' hr'
      by_cases h : r' = r
      · subst h
        simp only [if_true, stepLab, Function.update_self]
        rw [hS r' hr', lf.mat_dir hh hw]
      · have hne : emb r' ≠ emb r := fun e => h (hemb _ _ hr' hr e)
        simp only [if_neg hne, stepLab, Function.update_of_ne h]
        exact hS r' hr'
    · intro q hq
      have hne : q ≠ emb r := fun e => hq r hr e.symm
      simp only [if_neg hne]
  | shift r z =>
    have hr : r < p.n := hok
    have hR := Route.on_role S (emb r) (OAI.PowerSaving.Binary.shift (lf.ι (vec z))) 0
      ⟨[Move.shift (emb r) (lf.ι (vec z))], rfl, fun f x => rfl⟩
    refine ⟨_, hR, ?_, ?_⟩
    · intro r' hr'
      by_cases h : r' = r
      · subst h
        simp only [if_true, stepLab, Function.update_self]
        rw [hS r' hr', lf.mat_shift hh hw]
      · have hne : emb r' ≠ emb r := fun e => h (hemb _ _ hr' hr e)
        simp only [if_neg hne, stepLab, Function.update_of_ne h]
        exact hS r' hr'
    · intro q hq
      have hne : q ≠ emb r := fun e => hq r hr e.symm
      simp only [if_neg hne]
  | add t s c =>
    obtain ⟨ht, hs, hl⟩ := hok
    have hR : Route S S (actPoint (addMat (emb t) (emb s) c.val)) 0 := by
      apply Route.gate
      intro i j hij
      by_cases hd : i = j
      · rw [hd]
      · have hc : i = emb t ∧ j = emb s := by
          by_contra hc
          apply hij
          simp [addMat, hd, hc]
        rw [hc.1, hc.2, hS t ht, hS s hs, hl]
    have hg : actPoint (addMat (emb t) (emb s) c.val) = gMicro emb (.add t s c) := by
      funext x r; rw [actPoint_addMat]; rfl
    rw [hg] at hR
    exact ⟨S, hR, fun r hr => hS r hr, fun q _ => rfl⟩
  | copy s d =>
    obtain ⟨hs, hd⟩ := hok
    have hR : Route S (Function.update S (emb d) (S (emb s))) (actPoint (copyM (emb s) (emb d))) 0 := by
      apply Route.gate
      intro i j hij
      by_cases hi : i = emb d
      · have hj : j = emb s := by
          by_contra hj; apply hij; simp [copyM, hi, hj]
        rw [hi, hj, Function.update_self]
      · have hj : i = j := by
          by_contra hj; apply hij; simp [copyM, hi, hj]
        rw [← hj, Function.update_of_ne hi]
    have hg : actPoint (copyM (emb s) (emb d)) = gMicro emb (.copy s d) := by
      funext x r; rw [actPoint_copy]; rfl
    rw [hg] at hR
    refine ⟨_, hR, ?_, ?_⟩
    · intro r hr
      by_cases h : r = d
      · subst h
        simp only [stepLab, Function.update_self]
        exact hS s hs
      · have hne : emb r ≠ emb d := fun e => h (hemb _ _ hr hd e)
        simp only [stepLab, Function.update_of_ne hne, Function.update_of_ne h]
        exact hS r hr
    · intro q hq
      have hne : q ≠ emb d := fun e => hq d hd e.symm
      rw [Function.update_of_ne hne]
  | erase d =>
    have hR : Route S S (actPoint (eraseM ({emb d} : Finset ρ))) 0 := by
      apply Route.gate
      intro i j hij
      have hd : i = j := by
        by_contra h; apply hij; simp [eraseM, h]
      rw [hd]
    have hg : actPoint (eraseM ({emb d} : Finset ρ)) = gMicro emb (.erase d) := by
      funext x r; rw [actPoint_erase]; simp [gMicro]
    rw [hg] at hR
    exact ⟨S, hR, fun r hr => hS r hr, fun q _ => rfl⟩
  | expect r e => exact ⟨S, route_refl S, fun r' hr' => hS r' hr', fun q _ => rfl⟩

/-- **Soundness of labelled micro-programs.** -/
theorem micro_sound (lf : Lift p α) (hh : 0 < p.h) (hw : p.h < p.w) (Base : CMat α) (emb : Nat → ρ)
    (hemb : ∀ i j, i < p.n → j < p.n → emb i = emb j → i = j)
    (ms : List Micro) (lab : Nat → Nat) (S : ρ → CMat α) (hok : Ok p lab ms)
    (hS : ∀ r, r < p.n → S (emb r) = lf.mat Base (lab r)) :
    ∃ T, Route S T (gsemM emb ms) (countM ms) ∧
      (∀ r, r < p.n → T (emb r) = lf.mat Base (runLab p lab ms r)) ∧
      (∀ q, (∀ r, r < p.n → emb r ≠ q) → T q = S q) := by
  induction ms generalizing lab S with
  | nil => exact ⟨S, route_refl S, hS, fun _ _ => rfl⟩
  | cons m ms ih =>
    obtain ⟨hm, hrest⟩ := hok
    obtain ⟨S1, hR1, hS1, hF1⟩ := micro_step lf hh hw Base emb hemb m lab S hm hS
    obtain ⟨T, hR2, hT, hF2⟩ := ih (stepLab p m lab) S1 hrest hS1
    refine ⟨T, ?_, hT, fun q hq => (hF2 q hq).trans (hF1 q hq)⟩
    rw [gsemM_cons, countM_cons]
    exact hR1.trans hR2

end

end SSC
