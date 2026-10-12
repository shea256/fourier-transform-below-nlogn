import Work.GFrame.Engine.Level

/-!
# GFrame engine, part 5: closing the recursion for generalised words (agent key: eng-ram)

Copy of `rec_bodyB` / `recurse_runB` (`Work/Block/Recursion.lean`) with the word a `GWord`
and the certificate `GLiveKernel e w`.  The cost recurrence `allotB`, the bank `fundsB`, the
descriptor `DescB` and the charging function `chargingB` are those of the block engine,
unchanged: free adapters add only to the linear term of a level.

* `grecurse_run`   ONE program, work `allotB u a w.hist k`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

lemma grec_body (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (Q : Layout σ)
    (e : σ → ρ) (he : Function.Injective e) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hQ : Q.n=2^a) (w : GWord α ρ)
    (hw : GLiveKernel e w) (hP : w.Proper u) :
    let B := fundsB cl u a Q
    Able m B (simIn cl) (bundle cl) (fun i => loaded cl Q i.k i.v)
      (fun i => (sim Q i.k).tape (whole i.k i.v)) B.B (chargingB w.hist) := by
  intro B
  let Y := DescB cl u a Q
  let K := threshold u a
  let x (i : Y) := loaded cl Q i.k i.v
  have hx : Can m B.B (simIn cl) Ty.w x (fun i => i.k) B.B := Can.first
  have hQpos : 0<Q.n := by rw [hQ]; positivity
  apply Able.branch (hx.wlt (Can.wc K)) (fun i => K ≤ i.k)
    (fun i => by split <;> omega)
  -- big k. split according to r
  · let G := {i : Y // K ≤ i.k}
    let g (i : G) := i.1.k%u
    have hd (i : G) : g i<u := Nat.mod_lt _ (by omega)
    have hw' : Small (fun i : G => B.B i.1) g :=
      (Small.const _ u).mono (fun i => (hd i).le)
    apply Able.dispatch (n:=g) u ((hx.reindex (fun i : G => i.1)).wmod (Can.wc u) hw') hd
    intro r hr
    let L := {i : G // g i=r}
    let l (i : L) : Y := i.1.1
    let T0 := B.comap l
    let k (i : L) := (l i).k
    let f (i : L) := k i/u
    let n (rk : ℕ) (i : L) := batchesB u a rk (k i)
    let τ (rk : ℕ) (i : L) := (l i).tau rk
    have HH (i : L) : threshold u a ≤ k i := i.1.2
    have HK (rk : ℕ) (h1 : 1 ≤ rk) (h2 : rk < X.n) :
        Contract cl T0 (fun i => rk * f i) (τ rk) Q :=
      fun i => (l i).works (HH i) rk h1 (hX ▸ h2)
    have H := gamplify (k:=k) (f:=f) m T0 (fun i => (l i).v)
      X R Q e he r (by omega) (fun i => by
        have h := Nat.div_add_mod (k i) u
        have hj : k i%u=r := i.2
        rw [hX,← hj]; exact h
        ) (by omega) hQpos n τ
      (fun rk _ h2 i => by
        change batchesB u a rk (k i)*(Q.n*2^(rk * (k i/u)))=2^k i
        rw [hQ]
        exact rounds_eqB u a _ rk hu (HH i) (hX ▸ h2)) HK (Small.self _) w hw
      (hX ▸ hP)
    exact H.mono (fun _ => le_rfl) (fun i => by
      change _ ≤ chargingB w.hist (l i)
      have hi : threshold u a ≤ (l i).k := HH i
      rw [chargingB, if_pos hi, GWord.cost_eq_sum u _ w hP]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro rk _
      rw [Nat.mul_assoc])
  · let L := {i : Y // ¬ K ≤ i.k}
    have hl (i : L) : i.1.k<K := Nat.lt_of_not_ge i.2
    apply Able.dispatch K (hx.reindex (fun i : L => i.1)) hl
    intro j hj
    let T0 := {i : L // i.1.k=j}
    let l (i : T0) := i.1.1
    let Q' := B.comap l
    have H := almost_fixed m (fun i => Q'.B i) (fun i => Q'.B i) cl
      (fun i => (l i).k) j (fun i => i.2) Q (fun i => (l i).v)
    exact (Able.of_can (b:=Q') H).mono (fun _ => le_rfl) (fun _ => Nat.zero_le _)

/-- **Recursion closed for block words (with scratch roles).**  One fixed program; its work on
an input of order `k` is at most `Const * allotB u a w.hist k`, where every block of rank `rk`
of the word costs `2^(k - rk*(k/u) - a)` recursive calls of order `rk * (k/u)`. -/
theorem grecurse_run (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (Q : Layout σ)
    (e : σ → ρ) (he : Function.Injective e) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hQ : Q.n=2^a) (w : GWord α ρ)
    (hw : GLiveKernel e w) (hP : w.Proper u) {ι : Type*}
    (k : ι→ℕ) (v : ∀ i,Sim σ (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl Q (k i) (v i))
      (fun i => (sim Q (k i)).tape (whole (k i) (v i)))
      (fun i => allotB u a w.hist (k i)) := by
  obtain ⟨body,C,d,hc⟩ := grec_body cl m X R Q e he u a hX hu hQ w hw hP
  let N := w.hist
  let maxwork (k : ℕ) := allotB u a N k
  let c := 3*C+3
  let base : Prog m (simIn cl) (bundle cl) := .comp (.atom .snd) (.atom .snd)
  let fn := depthRun (base.run ()) body.run
  let P k := (2^k+2)^(d+1)
  have h (n : ℕ) (j : ℕ) (hj : j<n) (v : Sim σ j → ℂ) :
      (fn n (loaded cl Q j v)).OK ((sim Q j).tape (whole j v)) (c*maxwork j) (max (P j) n) := by
    induction n generalizing j with
    | zero => omega
    | succ n ih =>
      let peak := max (P j) (n+1)
      let tau (rk : ℕ) := c*maxwork (rk*(j/u))
      have pp (h : threshold u a ≤ j) (rk : ℕ) (_ : 1 ≤ rk) (h2 : rk < u)
          (v : Sim σ (rk*(j/u))→ℂ) :
          (fn n (loaded cl Q (rk*(j/u)) v)).OK
            ((sim Q (rk*(j/u))).tape (whole (rk*(j/u)) v)) (tau rk) peak := by
        have hi := sub_order_lt (down_lt hu h) h2
        have he := ih (rk*(j/u)) (by omega) v
        apply he.mono le_rfl
        have hh : 2^(rk*(j/u)) ≤ 2^j := Nat.pow_le_pow_right (by omega) hi.le
        exact max_le_max (by unfold P; gcongr) (by omega)
      let i : DescB cl u a Q := ⟨j,v,fn n,tau,peak,pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=n+1) (le_trans
        (le_max_right (P j) (n+1))
        (show peak ≤ (fundsB cl u a Q).cap d i from le_max_right _ _))
      apply H.mono
      · change C*(2^j+1)+chargingB N i +1 ≤ c*allotB u a N j
        have hh : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
        have hs : C*(2^j+1)+1 ≤ c*2^j := calc
          C*(2^j+1)+1 ≤ C*(2^j+2^j)+2^j := by gcongr
          _ ≤ _ := by
            dsimp [c]
            simp only [_root_.mul_add, _root_.add_mul]
            nlinarith
        unfold chargingB
        by_cases ha : threshold u a≤j
        · have hd : threshold u a ≤ i.k := ha
          rw [allotB_big u a N j hu ha, if_pos hd]
          change C*(2^j+1)+(∑ rk : Fin u, N rk * batchesB u a rk j *
            (c*allotB u a N (rk*(j/u))))+1 ≤ _
          have he : (∑ rk : Fin u, N rk * batchesB u a rk j * (c*allotB u a N (rk*(j/u))))
              = c*(∑ rk : Fin u, N rk * batchesB u a rk j * allotB u a N (rk*(j/u))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro rk _
            ring
          rw [he, _root_.mul_add c]; omega
        · have hd : ¬threshold u a ≤ i.k := ha
          rw [allotB_small u a N j ha, if_neg hd, Nat.add_zero]
          exact hs
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (2^j) (show d≤d+1 by omega)).trans
          (le_max_left _ _)
  let W i := maxwork (k i)
  let B i := 2^k i
  let x i := loaded cl Q (k i) (v i)
  let X1 i : Ty.T (Ty.p Ty.w (simIn cl)) := (k i+1,x i)
  have L : Can m B (Ty.p Ty.w (simIn cl)) (bundle cl)
      X1 (fun i => (sim Q (k i)).tape (whole (k i) (v i))) W := by
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
  have HE : Can m B (simIn cl) (Ty.p Ty.w (simIn cl)) x X1 W := by
    exact ((show Can m B (simIn cl) Ty.w x k W from Can.first).plus (Can.wc 1) hsmall
      (Small.const ..)).pair Can.id
  exact HE.then_do L

end

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.grecurse_run
