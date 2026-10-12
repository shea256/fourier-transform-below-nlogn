import Work.SharedSumChecker.Impl
import Work.SharedSumStructured.Invocation

/-!
# Shared-sum checker: from a checked certificate to the label calculus of
`Work.SharedSumStructured` (projectors, `Climb`, `GPath` for an ARBITRARY frame map)

The packed label `L` of the checker contains, in its bits `2K + w*i + j`, the matrix of the
orthogonal projector of the role's frame (`pmat`), and, when `p.cnt = 1`, in its bits above
`3K` the number of kernel moves the role has made (`cntOf`).  `Lb p L` is the corresponding
single-factor label `Lbl (Fin h)` of the structured development.

If a certificate without copies is accepted and a role ends with projector `1` after exactly
`h` moves, then the `h` directions it moved along form an orthonormal basis of `F_2^h`, every
label it ever had is the projector of an initial segment of that basis, and so

* `proj_climb`: any two labels of the role, earlier and later, are related by `Climb`;
* `proj_path` : any contiguous part of the micro-program is a `GPath` for EVERY frame map
  (`FMap`), with scalar map `actPoint (matP ..)`, the product of its gate matrices.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

section
variable (p : Par)

/-- the vector of `F_2^h` with bit mask `z` -/
def vecF (z : Nat) : Space (Fin p.h) := fun i => if z.testBit i.val then 1 else 0

/-- projector part of a label -/
def pmat (L : Nat) : Matrix (Fin p.h) (Fin p.h) F :=
  fun i j => if L.testBit (p.K2 + p.w * i.val + j.val) then 1 else 0

/-- a packed label as a single-factor label of the structured development -/
def Lb (L : Nat) : Lbl (Fin p.h) := ⟨pmat p L, cntOf p L⟩

theorem pmat_zero : pmat p 0 = 0 := by
  funext i j
  show (if (0:Nat).testBit _ then (1:F) else 0) = 0
  rw [Nat.zero_testBit]; rfl

theorem cnt_zero : cntOf p 0 = 0 := Nat.zero_shiftRight _

theorem Lb_zero : Lb p 0 = zeroL := by
  show (⟨pmat p 0, cntOf p 0⟩ : Lbl (Fin p.h)) = ⟨0, 0⟩
  rw [pmat_zero, cnt_zero]

section
variable (hh : 0 < p.h) (hw : p.h < p.w)
include hh hw

theorem pmat_upd (L z : Nat) :
    pmat p (upd p L (spread p z) z) = pmat p L + tt (vecF p z) := by
  funext i j
  show (if (upd p L (spread p z) z).testBit (p.K2 + p.w * i.val + j.val) then (1:F) else 0)
    = (if L.testBit (p.K2 + p.w * i.val + j.val) then 1 else 0)
      + (if z.testBit i.val then 1 else 0) * (if z.testBit j.val then 1 else 0)
  rw [upd_B p hh hw L z i.val j.val i.isLt j.isLt]
  cases L.testBit (p.K2 + p.w * i.val + j.val) <;> cases z.testBit i.val <;>
    cases z.testBit j.val <;> decide

theorem pmat_updS (L s : Nat) : pmat p (updS p L s) = pmat p L := by
  funext i j
  show (if (updS p L s).testBit (p.K2 + p.w * i.val + j.val) then (1:F) else 0) = _
  rw [updS_B p hh hw L s i.val j.val j.isLt]
  rfl

end

/-! ## histories -/

/-- sum of the rank-one projectors of a list of vectors -/
def psum (l : List Nat) : Matrix (Fin p.h) (Fin p.h) F := (l.map fun z => tt (vecF p z)).sum

theorem psum_nil : psum p [] = 0 := rfl
theorem psum_append (a b : List Nat) : psum p (a ++ b) = psum p a + psum p b := by
  simp [psum]
theorem psum_single (z : Nat) : psum p [z] = tt (vecF p z) := by simp [psum]

/-- directions of the kernel moves made so far, per role -/
def histStep : Micro → (Nat → List Nat) → (Nat → List Nat)
  | .dir r z, H => Function.update H r (H r ++ [z])
  | _, H => H

def runHist (H : Nat → List Nat) (ms : List Micro) : Nat → List Nat :=
  ms.foldl (fun H m => histStep m H) H

theorem runHist_nil (H : Nat → List Nat) : runHist H [] = H := rfl
theorem runHist_cons (H : Nat → List Nat) (m : Micro) (ms : List Micro) :
    runHist H (m :: ms) = runHist (histStep m H) ms := rfl
theorem runHist_append (H : Nat → List Nat) (a b : List Micro) :
    runHist H (a ++ b) = runHist (runHist H a) b := by
  simp [runHist, List.foldl_append]

theorem hist_prefix (H : Nat → List Nat) (ms : List Micro) (r : Nat) :
    ∃ l, runHist H ms r = H r ++ l := by
  induction ms generalizing H with
  | nil => exact ⟨[], by simp [runHist_nil]⟩
  | cons m ms ih =>
    obtain ⟨l, hl⟩ := ih (histStep m H)
    rw [runHist_cons, hl]
    cases m with
    | dir r' z =>
      by_cases e : r = r'
      · subst e
        exact ⟨[z] ++ l, by simp [histStep]⟩
      · exact ⟨l, by simp [histStep, Function.update_of_ne e]⟩
    | shift _ _ => exact ⟨l, rfl⟩
    | add _ _ _ => exact ⟨l, rfl⟩
    | copy _ _ => exact ⟨l, rfl⟩
    | erase _ => exact ⟨l, rfl⟩
    | expect _ _ => exact ⟨l, rfl⟩

def isCopy : Micro → Bool
  | .copy _ _ => true
  | _ => false

/-- every label is the projector of its role's history and counts it -/
def HInv (lab : Nat → Nat) (H : Nat → List Nat) : Prop :=
  ∀ r, pmat p (lab r) = psum p (H r) ∧ cntOf p (lab r) = (H r).length

theorem hinv_step (hh : 0 < p.h) (hw : p.h < p.w) (hc : p.cnt = 1) (lab : Nat → Nat)
    (H : Nat → List Nat) (hi : HInv p lab H) (m : Micro) (hm : isCopy m = false) :
    HInv p (stepLab p m lab) (histStep m H) := by
  cases m with
  | dir r z =>
    intro r'
    by_cases e : r' = r
    · subst e
      simp only [stepLab, histStep, Function.update_self]
      rw [pmat_upd p hh hw, cnt_upd p hh hw, (hi r').1, (hi r').2, psum_append, psum_single, hc,
        List.length_append]
      exact ⟨rfl, rfl⟩
    · simp only [stepLab, histStep, Function.update_of_ne e]
      exact hi r'
  | shift r z =>
    intro r'
    by_cases e : r' = r
    · subst e
      simp only [stepLab, histStep, Function.update_self]
      rw [pmat_updS p hh hw, cnt_updS p hh hw]
      exact hi r'
    · simp only [stepLab, histStep, Function.update_of_ne e]
      exact hi r'
  | add _ _ _ => exact hi
  | copy _ _ => exact absurd hm (by simp [isCopy])
  | erase _ => exact hi
  | expect _ _ => exact hi

theorem hinv_run (hh : 0 < p.h) (hw : p.h < p.w) (hc : p.cnt = 1) (ms : List Micro)
    (lab : Nat → Nat) (H : Nat → List Nat) (hi : HInv p lab H)
    (hm : ∀ m ∈ ms, isCopy m = false) :
    HInv p (runLab p lab ms) (runHist H ms) := by
  induction ms generalizing lab H with
  | nil => exact hi
  | cons m ms ih =>
    rw [runLab_cons, runHist_cons]
    exact ih _ _ (hinv_step p hh hw hc lab H hi m (hm m (List.mem_cons_self ..)))
      (fun m' h' => hm m' (List.mem_cons_of_mem _ h'))

/-! ## the orthonormal basis of a complete history -/

/-- the first `n` indices -/
def pre (n : Nat) : Finset (Fin p.h) := univ.filter fun k => k.val < n

theorem card_pre (n : Nat) (hn : n ≤ p.h) : (pre p n).card = n := by
  unfold pre
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right hn

theorem pre_mono {n k : Nat} (h : n ≤ k) : pre p n ⊆ pre p k := by
  intro x hx
  simp only [pre, mem_filter, mem_univ, true_and] at hx ⊢
  omega

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : Nat → M) (l : List Nat) :
    (l.map f).sum = ∑ k ∈ range l.length, f (l.getD k 0) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [add_comm]

theorem sum_pre {M : Type*} [AddCommMonoid M] (g : Nat → M) (n : Nat) (hn : n ≤ p.h) :
    ∑ k ∈ pre p n, g k.val = ∑ k ∈ range n, g k := by
  unfold pre
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun k => if k < n then g k else 0) p.h,
    ← Finset.sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega

theorem base_exists (Z : List Nat) (hl : Z.length = p.h) (hs : psum p Z = 1) :
    ∃ A : OBase (Fin p.h), ∀ k : Fin p.h, A.v k = vecF p (Z.getD k.val 0) := by
  let v : Fin p.h → Space (Fin p.h) := fun k => vecF p (Z.getD k.val 0)
  let M : Matrix (Fin p.h) (Fin p.h) F := Matrix.of v
  have h1 : Mᵀ * M = 1 := by
    ext a b
    rw [← hs]
    unfold psum
    rw [list_sum_range (fun z => tt (vecF p z)) Z, hl, Matrix.sum_apply,
      ← Fin.sum_univ_eq_sum_range (fun k => tt (vecF p (Z.getD k 0)) a b) p.h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply, v]
    rfl
  have h2 : M * Mᵀ = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨v, fun i j => ?_⟩, fun k => rfl⟩
  have h3 := congr_fun (congr_fun h2 i) j
  simpa [M, Matrix.mul_apply, Matrix.one_apply, dot] using h3

theorem mat_pre (A : OBase (Fin p.h)) (Z : List Nat) (hl : Z.length = p.h)
    (hA : ∀ k : Fin p.h, A.v k = vecF p (Z.getD k.val 0)) (l rest : List Nat)
    (hZ : Z = l ++ rest) : A.mat (pre p l.length) = psum p l := by
  have hn : l.length ≤ p.h := by rw [← hl, hZ, List.length_append]; omega
  ext a b
  unfold psum
  rw [list_sum_range (fun z => tt (vecF p z)) l, Matrix.sum_apply]
  show ∑ k ∈ pre p l.length, A.v k a * A.v k b = _
  have e : ∀ k ∈ pre p l.length, A.v k a * A.v k b = tt (vecF p (l.getD k.val 0)) a b := by
    intro k hk
    have hk' : k.val < l.length := (mem_filter.mp hk).2
    rw [hA k, hZ, List.getD_append _ _ _ _ hk']
    rfl
  rw [Finset.sum_congr rfl e, sum_pre p (fun k => tt (vecF p (l.getD k 0)) a b) _ hn]

theorem climb_of_prefix (A : OBase (Fin p.h)) (Z : List Nat) (hl : Z.length = p.h)
    (hA : ∀ k : Fin p.h, A.v k = vecF p (Z.getD k.val 0)) (l m rest : List Nat)
    (hZ : Z = l ++ m ++ rest) (L L' : Nat) (h1 : pmat p L = psum p l)
    (c1 : cntOf p L = l.length) (h2 : pmat p L' = psum p (l ++ m))
    (c2 : cntOf p L' = (l ++ m).length) : Climb (Lb p L) (Lb p L') := by
  have hlen : (l ++ m).length ≤ p.h := by
    have h3 := congrArg List.length hZ
    simp only [List.length_append] at h3 ⊢
    omega
  have hsub : pre p l.length ⊆ pre p (l ++ m).length :=
    pre_mono p (by rw [List.length_append]; omega)
  refine ⟨A, pre p l.length, pre p (l ++ m).length, hsub, ?_, ?_, ?_⟩
  · show pmat p L = _
    rw [h1, mat_pre p A Z hl hA l (m ++ rest) (by rw [hZ, List.append_assoc])]
  · show pmat p L' = _
    rw [h2, mat_pre p A Z hl hA (l ++ m) rest hZ]
  · show cntOf p L' = cntOf p L + _
    rw [c1, c2, card_sdiff_of_subset hsub, card_pre p _ hlen,
      card_pre p _ (le_trans (by rw [List.length_append]; omega) hlen), List.length_append]
    omega

end

/-! ## the scalar matrix of a micro-program -/

section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- product of the gate matrices (later gates on the left) -/
noncomputable def matP (unemb : Nat → ρ) : List Micro → Matrix ρ ρ ℚ
  | [] => 1
  | .add t s c :: ms => matP unemb ms * addMat (unemb t) (unemb s) c.val
  | .dir _ _ :: ms => matP unemb ms
  | .shift _ _ :: ms => matP unemb ms
  | .copy _ _ :: ms => matP unemb ms
  | .erase _ :: ms => matP unemb ms
  | .expect _ _ :: ms => matP unemb ms

theorem actPoint_mul (A B : Matrix ρ ρ ℚ) : actPoint (A * B) = actPoint A ∘ actPoint B := by
  funext u
  rw [actPoint_eq_ap, actPoint_eq_ap, actPoint_eq_ap]
  exact ap_mul A B u

theorem actPoint_one' : actPoint (1 : Matrix ρ ρ ℚ) = id := by
  funext u
  rw [actPoint_eq_ap]
  exact ap_one u

/-- the roles a contiguous part may touch: only embedded ones, and no copy or erase -/
def segOK (emb : ρ → Nat) (unemb : Nat → ρ) : Micro → Prop
  | .dir r _ => emb (unemb r) = r
  | .shift _ _ => True
  | .add t s _ => emb (unemb t) = t ∧ emb (unemb s) = s
  | .copy _ _ => False
  | .erase _ => False
  | .expect _ _ => True

variable (p : Par) {α : Type} [Fintype α] [DecidableEq α]

/-- hypotheses on a complete certificate, seen as a micro-program `tot` -/
structure Complete (lab0 : Nat → Nat) (H0 : Nat → List Nat) (tot : List Micro) (emb : ρ → Nat) :
    Prop where
  hh : 0 < p.h
  hw : p.h < p.w
  hc : p.cnt = 1
  hinv : HInv p lab0 H0
  hok : Ok p lab0 tot
  hnc : ∀ m ∈ tot, isCopy m = false
  hfull : ∀ q : ρ, pmat p (runLab p lab0 tot (emb q)) = 1 ∧ cntOf p (runLab p lab0 tot (emb q)) = p.h

variable {p}

theorem Complete.base {lab0 : Nat → Nat} {H0 : Nat → List Nat} {tot : List Micro} {emb : ρ → Nat}
    (C : Complete p lab0 H0 tot emb) (q : ρ) :
    ∃ A : OBase (Fin p.h), ∀ k : Fin p.h,
      A.v k = vecF p ((runHist H0 tot (emb q)).getD k.val 0) := by
  obtain ⟨h1, h2⟩ := hinv_run p C.hh C.hw C.hc tot lab0 H0 C.hinv C.hnc (emb q)
  exact base_exists p _ (by rw [← h2, (C.hfull q).2]) (by rw [← h1, (C.hfull q).1])

/-- **Any two labels of a role, earlier and later, are related by one `Climb`.** -/
theorem Complete.climb {lab0 : Nat → Nat} {H0 : Nat → List Nat} {tot : List Micro} {emb : ρ → Nat}
    (C : Complete p lab0 H0 tot emb) (q : ρ) (a b c : List Micro) (htot : tot = a ++ b ++ c) :
    Climb (Lb p (runLab p lab0 a (emb q))) (Lb p (runLab p lab0 (a ++ b) (emb q))) := by
  obtain ⟨A, hA⟩ := C.base q
  have hna : ∀ m ∈ a, isCopy m = false := fun m hm => C.hnc m (by rw [htot]; simp [hm])
  have hnab : ∀ m ∈ a ++ b, isCopy m = false := fun m hm => C.hnc m (by
    rw [htot]; exact List.mem_append_left _ hm)
  obtain ⟨p1, c1⟩ := hinv_run p C.hh C.hw C.hc a lab0 H0 C.hinv hna (emb q)
  obtain ⟨p2, c2⟩ := hinv_run p C.hh C.hw C.hc (a ++ b) lab0 H0 C.hinv hnab (emb q)
  obtain ⟨pt, ct⟩ := hinv_run p C.hh C.hw C.hc tot lab0 H0 C.hinv C.hnc (emb q)
  obtain ⟨m, hm⟩ := hist_prefix (runHist H0 a) b (emb q)
  obtain ⟨rest, hrest⟩ := hist_prefix (runHist H0 (a ++ b)) c (emb q)
  rw [← runHist_append] at hm
  rw [← runHist_append, ← htot] at hrest
  rw [hm] at p2 c2 hrest
  exact climb_of_prefix p A _ (by rw [← ct, (C.hfull q).2]) hA _ m rest hrest _ _ p1 c1 p2 c2

/-- **A contiguous part of a complete certificate is a `GPath` for every frame map.** -/
theorem Complete.path {lab0 : Nat → Nat} {H0 : Nat → List Nat} {tot : List Micro} {emb : ρ → Nat}
    (C : Complete p lab0 H0 tot emb) (unemb : Nat → ρ) (hun : ∀ q, unemb (emb q) = q)
    (Fm : FMap (Fin p.h) α) (seg : List Micro) :
    ∀ (a c : List Micro), tot = a ++ seg ++ c → (∀ m ∈ seg, segOK emb unemb m) →
      GPath (fun q => Fm.lab (Lb p (runLab p lab0 a (emb q))))
        (fun q => Fm.lab (Lb p (runLab p lab0 (a ++ seg) (emb q))))
        (actPoint (matP unemb seg)) 0 := by
  have hinj : ∀ q q', emb q = emb q' → q = q' := fun q q' e => by
    rw [← hun q, ← hun q', e]
  induction seg with
  | nil =>
    intro a c _ _
    rw [List.append_nil]
    show GPath _ _ (actPoint (1 : Matrix ρ ρ ℚ)) 0
    rw [actPoint_one']
    exact GPath.refl
  | cons m seg ih =>
    intro a c htot hseg
    have htot' : tot = (a ++ [m]) ++ seg ++ c := by rw [htot]; simp
    have hm := hseg m (List.mem_cons_self ..)
    have ih' := ih (a ++ [m]) c htot' (fun m' h' => hseg m' (List.mem_cons_of_mem _ h'))
    have eapp : a ++ m :: seg = (a ++ [m]) ++ seg := by simp
    rw [eapp]
    have hokm : okMicro p m (runLab p lab0 a) := by
      have h1 := C.hok
      rw [htot, List.append_assoc, Ok_append] at h1
      exact h1.2.1
    cases m with
    | dir r z =>
      have hr : emb (unemb r) = r := hm
      have hcl := C.climb (unemb r) a [Micro.dir r z] (seg ++ c) (by rw [htot]; simp)
      obtain ⟨n, hreach, hd⟩ := Fm.reach hcl.climbs
      have hstep := GPath.up (fun q => Fm.lab (Lb p (runLab p lab0 a (emb q)))) (unemb r)
        (Fm.lab (Lb p (runLab p lab0 (a ++ [Micro.dir r z]) (emb (unemb r))))) n hreach hd
      have hs : Function.update (fun q => Fm.lab (Lb p (runLab p lab0 a (emb q)))) (unemb r)
          (Fm.lab (Lb p (runLab p lab0 (a ++ [Micro.dir r z]) (emb (unemb r)))))
          = fun q => Fm.lab (Lb p (runLab p lab0 (a ++ [Micro.dir r z]) (emb q))) := by
        funext q
        by_cases e : q = unemb r
        · rw [e, Function.update_self]
        · rw [Function.update_of_ne e]
          have hne : emb q ≠ r := fun h => e (by rw [← hun q, h])
          rw [runLab_append]
          show _ = Fm.lab (Lb p (stepLab p (Micro.dir r z) (runLab p lab0 a) (emb q)))
          simp only [stepLab, Function.update_of_ne hne]
      rw [hs] at hstep
      exact (hstep.trans ih').cast rfl (by omega)
    | shift r z =>
      have hs : (fun q => Fm.lab (Lb p (runLab p lab0 (a ++ [Micro.shift r z]) (emb q))))
          = fun q => Fm.lab (Lb p (runLab p lab0 a (emb q))) := by
        funext q
        rw [runLab_append]
        show Fm.lab (Lb p (stepLab p (Micro.shift r z) (runLab p lab0 a) (emb q))) = _
        by_cases e : emb q = r
        · simp only [stepLab, e, Function.update_self]
          show Fm.lab ⟨pmat p (updS p _ z), cntOf p (updS p _ z)⟩ = Fm.lab ⟨pmat p _, cntOf p _⟩
          rw [pmat_updS p C.hh C.hw, cnt_updS p C.hh C.hw]
        · simp only [stepLab, Function.update_of_ne e]
      rw [hs] at ih'
      exact ih'
    | add t s cf =>
      obtain ⟨ht, hs'⟩ := hm
      obtain ⟨_, _, hl⟩ := hokm
      have hsame : (fun q => Fm.lab (Lb p (runLab p lab0 (a ++ [Micro.add t s cf]) (emb q))))
          = fun q => Fm.lab (Lb p (runLab p lab0 a (emb q))) := by
        funext q; rw [runLab_append]; rfl
      rw [hsame] at ih'
      have hg : GPath (fun q => Fm.lab (Lb p (runLab p lab0 a (emb q))))
          (fun q => Fm.lab (Lb p (runLab p lab0 a (emb q))))
          (actPoint (addMat (unemb t) (unemb s) cf.val)) 0 := by
        apply GPath.gate
        intro i j hij
        by_cases hd : i = j
        · rw [hd]
        · have hc : i = unemb t ∧ j = unemb s := by
            by_contra hc
            apply hij
            simp [addMat, hd, hc]
          rw [hc.1, hc.2, ht, hs', hl]
      have h := hg.trans ih'
      show GPath _ _ (actPoint (matP unemb seg * addMat (unemb t) (unemb s) cf.val)) 0
      rw [actPoint_mul]
      exact h.cast rfl (by omega)
    | copy _ _ => exact False.elim hm
    | erase _ => exact False.elim hm
    | expect r e =>
      have hsame : (fun q => Fm.lab (Lb p (runLab p lab0 (a ++ [Micro.expect r e]) (emb q))))
          = fun q => Fm.lab (Lb p (runLab p lab0 a (emb q))) := by
        funext q; rw [runLab_append]; rfl
      rw [hsame] at ih'
      exact ih'

end

end SSC
