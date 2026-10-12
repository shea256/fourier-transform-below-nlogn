import OAI.Computability.FourierTransform.TensorAlgorithm

namespace OAI

namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

def threshold (u a : ℕ) := u*(a+1)
def batches (u a k : ℕ) := 2^(k-k/u-a)

def allot (u a D : ℕ) (k : ℕ) : ℕ :=
  if h : k/u<k ∧ threshold u a ≤ k then
    2^k + D*batches u a k*allot u a D (k/u)
  else 2^k
termination_by k

lemma down_lt {u k} (hu : 3≤u) {a} (hk : threshold u a ≤ k) :
    k/u<k := by
  unfold threshold at hk
  have hk' : k>0 := by
    have h : 0 < u*(a+1) := by positivity
    exact h.trans_le hk
  exact Nat.div_lt_self hk' (by omega)

lemma rounds_eq (u a k) (hu : 3≤u) (hk : threshold u a ≤ k) :
    batches u a k * (2^a*2^(k/u))=2^k := by
  have hh : a+1≤k/u := (Nat.le_div_iff_mul_le (by omega)).2 (by
    simpa [threshold,mul_comm] using hk)
  have hl : k/u*2≤k := calc
    _ ≤ k/u*u := Nat.mul_le_mul_left _ (by omega)
    _ ≤ _ := Nat.div_mul_le_self _ _
  unfold batches
  rw [← pow_add, ← pow_add]
  congr; omega

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Parameters included in the open-code guarantee. -/
structure Desc (cl : Paint) (u a : ℕ) (R : Layout ρ) where
  k : ℕ
  v : Sim ρ k → ℂ
  use : Handler (hatch cl)
  tau : ℕ
  peak : ℕ
  works : threshold u a ≤ k →
    ∀ (v : Sim ρ (k/u)→ℂ), (use (loaded cl R (k/u) v)).OK
      ((sim R (k/u)).tape (whole (k/u) v)) tau peak

def funds {ρ} (cl : Paint) (u a : ℕ) (R : Layout ρ) :
    Bank (hatch cl) (Desc cl u a R) := ⟨fun i => 2^i.k, Desc.peak, Desc.use⟩

def charging {cl u a R} (D : ℕ) (i : Desc cl u a (R:Layout ρ)) :=
  if threshold u a ≤ i.k then D*batches u a i.k*i.tau else 0

lemma rec_body (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hR : R.n=2^a) (p : PWord α ρ)
    (hp : ∀ f v, walk f p v = multiAct f (fun _ => kernel α) v) :
    let B := funds cl u a R
    Able m B (simIn cl) (bundle cl) (fun i => loaded cl R i.k i.v)
      (fun i => (sim R i.k).tape (whole i.k i.v)) B.B (charging (tally p)) := by
  intro B
  let Y := Desc cl u a R
  let K := threshold u a
  let x (i : Y) := loaded cl R i.k i.v
  have hx : Can m B.B (simIn cl) w x (fun i => i.k) B.B := Can.first
  apply Able.branch (hx.wlt (Can.wc K)) (fun i => K ≤ i.k)
    (fun i => by split <;> omega)
  -- big k. split according to r
  · let G := {i : Y // K ≤ i.k}
    let g (i : G) := i.1.k%u
    have hd (i : G) : g i<u := Nat.mod_lt _ (by omega)
    have hw : Small (fun i : G => B.B i.1) g :=
      (Small.const _ u).mono (fun i => (hd i).le)
    apply Able.dispatch (n:=g) u ((hx.reindex (fun i : G => i.1)).wmod (Can.wc u) hw) hd
    intro r hr
    let L := {i : G // g i=r}
    let l (i : L) : Y := i.1.1
    let T0 := B.comap l
    let k (i : L) := (l i).k
    let f (i : L) := k i/u
    let n (i : L) := batches u a (k i)
    have HH (i : L) : threshold u a ≤ k i := i.1.2
    have HK : Contract cl T0 f (fun i => (l i).tau) R :=
      fun i => (l i).works (HH i)
    have H := amplify (k:=k) (f:=f) (n:=n) m T0 (fun i => (l i).v)
      X R r (by omega) (fun i => by
        have h := Nat.div_add_mod (k i) u
        have hj : k i%u=r := i.2
        rw [hX,← hj]; exact h
        ) (by omega)
      (fun i => by
        change batches u a (k i)*(R.n*2^(k i/u))=2^k i
        rw [hR]
        exact rounds_eq u a _ hu (HH i)) HK (Small.self _) p hp
    exact H.mono (fun _ => le_rfl) (fun i => by
      change _ ≤ charging (tally p) (l i)
      have hi : threshold u a ≤ (l i).k := HH i
      rw [charging, ite_eq_left hi])
  · let L := {i : Y // ¬ K ≤ i.k}
    have hl (i : L) : i.1.k<K := Nat.lt_of_not_ge i.2
    apply Able.dispatch K (hx.reindex (fun i : L => i.1)) hl
    intro j hj
    let T0 := {i : L // i.1.k=j}
    let l (i : T0) := i.1.1
    let Q := B.comap l
    have H := almost_fixed m (fun i => Q.B i) (fun i => Q.B i) cl
      (fun i => (l i).k) j (fun i => i.2) R (fun i => (l i).v)
    exact (Able.of_can (b:=Q) H).mono (fun _ => le_rfl) (fun _ => Nat.zero_le _)

/-- Recursion closed. -/
theorem recurse_run (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hR : R.n=2^a) (p : PWord α ρ)
    (hp : ∀ f v, walk f p v = multiAct f (fun _ => kernel α) v) {ι : Type*}
    (k : ι→ℕ) (v : ∀ i,Sim ρ (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i)))
      (fun i => allot u a (tally p) (k i)) := by
  obtain ⟨body,C,d,hc⟩ := rec_body cl m X R u a hX hu hR p hp
  let D := tally p
  let maxwork (k : ℕ) := allot u a D k
  let c := 3*C+3
  let base : Prog m (simIn cl) (bundle cl) := .comp (.atom .snd) (.atom .snd)
  let fn := depthRun (base.run ()) body.run
  let P k := (2^k+2)^(d+1)
  have h (n : ℕ) (j : ℕ) (hj : j<n) (v : Sim ρ j → ℂ) :
      (fn n (loaded cl R j v)).OK ((sim R j).tape (whole j v)) (c*maxwork j) (max (P j) n) := by
    induction n generalizing j with
    | zero => omega
    | succ n ih =>
      let peak := max (P j) (n+1)
      let tau := c*maxwork (j/u)
      have pp (h : threshold u a ≤ j) (v : Sim ρ (j/u)→ℂ) :
          (fn n (loaded cl R (j/u) v)).OK ((sim R (j/u)).tape (whole (j/u) v)) tau peak := by
        have hi := down_lt hu h
        have he := ih (j/u) (by omega) v
        apply he.mono le_rfl
        have hh : 2^(j/u) ≤ 2^j := Nat.pow_le_pow_right (by omega) hi.le
        exact max_le_max (by unfold P; gcongr) (by omega)
      let i : Desc cl u a R := ⟨j,v,fn n,tau,peak,pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=n+1) (le_trans
        (le_max_right (P j) (n+1))
        (show peak ≤ (funds cl u a R).cap d i from le_max_right _ _))
      -- step.run definition
      apply H.mono
      · change C*(2^j+1)+charging D i +1 ≤ c*allot u a D j
        have hh : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
        have hs : C*(2^j+1)+1 ≤ c*2^j := calc
          C*(2^j+1)+1 ≤ C*(2^j+2^j)+2^j := by gcongr
          _ ≤ _ := by
            dsimp [c]
            simp only [_root_.mul_add, _root_.add_mul]
            nlinarith
        unfold charging
        by_cases ha : threshold u a≤j
        · have hd : threshold u a ≤ i.k := ha
          rw [allot, dite_eq_left ⟨down_lt hu ha,ha⟩, ite_eq_left hd]
          change C*(2^j+1)+D*batches u a j*(c*allot u a D (j/u))+1 ≤ _
          have he : D*batches u a j*(c*allot u a D (j/u))
              = c*(D*batches u a j*allot u a D (j/u)) := by ring
          rw [he, _root_.mul_add c]; omega
        · have hd : ¬threshold u a ≤ i.k := ha
          rw [allot, dite_eq_right (fun hp => ha hp.2), ite_eq_right hd, Nat.add_zero]
          exact hs
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (2^j) (show d≤d+1 by omega)).trans
          (le_max_left _ _)
  let W i := maxwork (k i)
  let B i := 2^k i
  let x i := loaded cl R (k i) (v i)
  let X1 i : Ty.T (Ty.p w (simIn cl)) := (k i+1,x i)
  have L : Can m B (Ty.p w (simIn cl)) (bundle cl)
      X1 (fun i => (sim R (k i)).tape (whole (k i) (v i))) W := by
    refine ⟨.descend base body,c+1,d+1,fun i => ?_⟩
    have hh := h (k i+1) (k i) (by omega) (v i)
    have hg : k i+1 ≤ P (k i) :=
      calc
        _ ≤ 2^(k i) := Nat.lt_two_pow_self
        _ ≤ (2^k i + 2)^1 := by simp
        _ ≤ _ := Small.pow_mono_degree _ (by omega)
    have H := hh.pay (t:=1) (z:=k i+1) (le_max_right ..)
    apply H.mono
    · change c*W i+1 ≤ _
      simp [_root_.add_mul, _root_.mul_add]
      omega
    · exact max_le (le_max_left ..) (hg.trans (le_max_left ..))
  have hsmall : Small B k :=
    (Small.self B).mono (fun i => Nat.lt_two_pow_self.le)
  have HE : Can m B (simIn cl) (Ty.p w (simIn cl)) x X1 W := by
    exact ((show Can m B (simIn cl) w x k W from Can.first).plus (Can.wc 1) hsmall (Small.const ..)).pair Can.id
  exact HE.then_do L

end
end PowerSaving.RAM

end OAI
