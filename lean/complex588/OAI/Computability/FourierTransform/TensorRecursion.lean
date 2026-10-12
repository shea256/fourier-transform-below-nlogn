import OAI.Computability.FourierTransform.RecursiveContract

namespace OAI
namespace PowerSaving.RAM
open Binary Ty Matrix Finset
noncomputable section

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

section

variable (X : Layout α) (R : Layout ρ) (r f k : ℕ)
    (h : X.n*f+r=k)

def ebb (v : Sim ρ k → ℂ) : Grain α ρ r f :=
  fun j => v (j.1,serial X r f h j.2)
-- R not included in def

omit [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma ebb_eq (v : Sim ρ k→ℂ) :
    (fleet X R r f).tape (ebb X r f k h v) = (sim R k).tape v := by
  refine Layout.verify (sim R k) _ 0 _ ?_ ?_
  · change R.n*(book X r f).n=R.n*(bits k).n
    rw [book_len, bits_len,h]
  · rintro ⟨a,j⟩
    obtain ⟨w,hw⟩ := (serial X r f h).surjective j
    subst j
    have hd : (sim R k).loc (a,serial X r f h w) = (fleet X R r f).loc (a,w) := by
      simp only [sim,fleet,Layout.pair_loc,book_len,serial_code, h,bits_len]
    rw [hd]
    apply Layout.read _ _ (a,w) _

lemma amplifies (p : PWord α ρ)
    (hp : ∀ v, walk f p v = multiAct f (fun _ => kernel α) v)
    (v : Sim ρ k → ℂ) :
    let e := ebb X r f k h v
    let z : Grain α ρ r f := fun i => chords r f (fun j => e (i.1,j)) i.2
    coastline r f p z = ebb X r f k h (whole k v) := by
  intro e z
  funext i
  unfold coastline
  rw [hp]
  exact (ripple_grid X r f h (fun j => v (i.1,j)) i.2).symm

end

section
universe U
variable {ι : Type U} {m : Bool}
    {k f n τ : ι → ℕ} {cl : Paint} {b : Bank (hatch cl) ι}
    {v : ∀ i, Sim ρ (k i)→ℂ}

/-- Body proof with fixed r. B need only dominate 2^k polynomially. -/
lemma amplify (m : Bool) (b : Bank (hatch cl) ι) (v : ∀ i, Sim ρ (k i) → ℂ)
    (X : Layout α) (R : Layout ρ) (r : ℕ)
    (hr : 3 ≤ X.n) (hq : ∀ i, X.n*f i+r=k i) (hd : r < X.n)
    (hc : ∀ i, n i*(sim R (f i)).n=2^k i)
    (hk : Contract cl b f τ R)
    (hB : Small b.B (fun i => 2^k i))
    (p : PWord α ρ) (hp : ∀ f v, walk f p v = multiAct f (fun _ => kernel α) v) :
    Able m b (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i) (fun i => tally p*n i*τ i) := by
  let W i := 2^k i
  let s := simIn cl
  let e (i : ι) := ebb X r (f i) (k i) (hq i) (v i)
  let z (i : ι) : Grain α ρ r (f i) :=
    fun j => chords r (f i) (fun l => e i (j.1,l)) j.2
  let sz i := (fleet X R r (f i)).n
  have hsz : Dom W sz := by
    refine ⟨R.n+1, fun i => ?_⟩
    unfold W sz fleet
    rw [Layout.pair_len, book_len,hq]
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have hn (i : ι) : 0 < W i := pow_pos (by decide) _
  have hf (i) : f i ≤ k i := by
    have g := hq i
    have h := Nat.le_mul_of_pos_left (f i) (show 0 < X.n by omega)
    omega
  have hy (i) : k i ≤ W i := Nat.lt_two_pow_self.le
  have sd := hB.mono hy
  have sq := sd.mono hf
  let p2 i := 2^f i
  have hm : Small b.B p2 :=
    hB.mono (fun i => Nat.pow_le_pow_right (by omega) (hf i))
  have hcube (i) : p2 i ^ 3 ≤ W i := by
    unfold p2 W
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have hh : 3*f i ≤ X.n*f i := Nat.mul_le_mul_right _ hr
    have hg := hq i
    rw [mul_comm]
    omega
  let env (i : ι) := loaded cl R (k i) (v i)
  -- construct fields (f,p2)
  have hmf : Can m b.B s Ty.w env f W := by
    have ht : Can m b.B s Ty.w env k W := Can.first
    refine (ht.dvdW (Can.wc X.n) sd).cong (fun _ => rfl) ?_
    intro i
    rw [← hq,mul_comm X.n]
    exact Layout.div_join hd
  have hmp : Can m b.B s (Ty.p Ty.w Ty.w) env (fun i => (f i,p2 i)) W :=
    hmf.pair (hmf.wTwo sq hm (Dom.of_le (fun i => (hf i).trans (hy i))))
  let T1 := Ty.p s (Ty.p Ty.w Ty.w)
  let Y (i : ι) : T T1 := (env i,f i,p2 i)
  have hmx : Can m b.B T1 (Ty.a Ty.w) Y (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=b.B) (s:=T1) (x:=Y)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := Ty.p T1 (Ty.a Ty.w)
  let Y' (i : ι) : T T2 := (Y i,xorTab (f i))
  have hG : Rig m b.B f T2 Y' cl X R r e := by
    have H : Has m b.B T2 s Y' env := Can.fst Can.first
    refine ⟨⟨?_,?_,Can.second,hm⟩,?_,?_⟩
    · exact Can.snd (Can.snd Can.first)
    · exact Can.fst (Can.snd Can.first)
    · exact H.snd.fst
    · exact H.snd.snd.cong (fun _ => rfl) (fun i => (ebb_eq ..).symm)
  have HH : Can m b.B T2 (bundle cl) Y' (fun i => (fleet X R r (f i)).tape (z i)) W :=
    hG.dots_cost.weaken hsz
  let pre (i) := (fleet X R r (f i)).tape (z i)
  let T3 := Ty.p T2 (bundle cl)
  let A (i) : T T3 := (Y' i,pre i)
  have Hg := hG.gather id A (t:=T3) Can.first
  have G : Rig m b.B f T3 A cl X R r z := ⟨Hg.gear,Hg.imag,Can.second⟩
  have Hy := G.sweep hk (n:=n)
    (fun i => by rw [book_len,hq]; exact hc i) p
  have heq (i) : coastline r (f i) p (z i) = ebb X r (f i) (k i) (hq i) (whole (k i) (v i)) :=
    amplifies X r (f i) (k i) (hq i) p (hp _) (v i)
  have ha (i) : (fleet X R r (f i)).tape (coastline r (f i) p (z i)) =
      (sim R (k i)).tape (whole (k i) (v i)) := by
    rw [heq]; exact ebb_eq ..
  have Ho := (Hy.weaken hsz (fun _ => le_rfl)).cong (fun _ => rfl) ha
  have Hx := (Able.of_can (b:=b) hmp).save_keep
    ((Able.of_can (b:=b) hmx).save_keep ((Able.of_can (b:=b) HH).save_keep Ho))
  simpa only [Nat.zero_add] using Hx

end
end
end PowerSaving.RAM

end OAI
