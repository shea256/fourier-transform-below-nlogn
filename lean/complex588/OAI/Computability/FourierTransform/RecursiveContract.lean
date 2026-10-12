import OAI.Computability.FourierTransform.RecursiveBatches

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}

/-- Contract assumed on external calls *inside* the open body proof only. -/
def Contract (cl : Paint) (b : Bank (hatch cl) ι) (f T : ι → ℕ) (R : Layout ρ) :=
  ∀ i v, (b.use i (loaded cl R (f i) v)).OK ((sim R (f i)).tape (whole (f i) v))
             (T i) (b.ext i)

variable {m : Bool} {f n τ : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

namespace Rig
variable (h : Rig m b.B f s x cl X R r v)
include h

lemma open_dir (hk : Contract cl b f τ R)
    (hg : ∀ i, n i*(sim R (f i)).n=(book X r (f i)).n)
    (l : ρ) (z : Space α) (hz : z≠0) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.dir l z hz) (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n i*τ i) := by
  obtain ⟨j,hj⟩ := choose_pivot hz
  let X' := Layout.someLayout (Minus j)
  have he (i) : n i * R.n=(book X' r (f i)).n := by
    have hy : X'.n+1=X.n := by
      rw [← Layout.card X',← Layout.card X]; exact card_minus j
    have hz := hg i
    change n i*(R.n*2^f i) = 2^r*(2^f i)^X.n at hz
    change n i * R.n = 2^r*(2^f i)^X'.n
    rw [← hy,pow_succ, ← mul_assoc, ← mul_assoc] at hz
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hz
  let w i := (fleet X R r (f i)).n
  let y i := yieldTape l j z X' R (he i) (v i)
  let sz i := (sim R (f i)).n
  let Tt := a (bundle cl)
  have hl : 0 < R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  have hy : Able m b s Tt x y w (fun i => n i*τ i) := by
    let arg (i) (k : Fin (n i)) := fill l j z X' R (he i) (v i) k
    let g (i) (k : Fin (n i)) := (sim R (f i)).tape (whole (f i) (arg i k))
    let I (i : ι) := Fin (n i)
    let E0 (d : Σ i, I i) := (x d.1,(d.2:ℕ))
    have hs : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (bundle cl)
        E0 (fun d => g d.1 d.2) (fun d => sz d.1) (fun d => τ d.1) := by
      have HH := h.gather (Sigma.fst (β:=I)) E0 (t:=p s Ty.w) Can.first
      have Hp := HH.fill_ready l j z X' (n:=fun d=> n d.1) (fun d => he d.1)
        (fun d : Σ i,I i => d.2) Can.second
      have Hq : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (simIn cl) E0
          (fun d => loaded cl R (f d.1) (arg d.1 d.2))
          (fun d => sz d.1) (fun _ => 0) := Able.of_can Hp
      have HG := Hq.comp (Able.use_call (ι:=Σ i,I i) (s:=simIn cl) (t:=bundle cl) (m:=m) (b:=b.comap (Sigma.fst (β:=I))) (Z:=fun d => τ d.1) (y:=fun d => g d.1 d.2)
        (fun d => hk d.1 (arg d.1 d.2)))
      simpa [Nat.zero_add] using HG
    have HT : Able m b s Ty.w x n (fun _=>0) (fun _=>0) :=
      Able.of_can (h.batchSize j X' he hl)
    have HH := Able.layout (L:=fun i => Layout.std (n i)) (v:=g) (t:=bundle cl)
      (P:=sz) (H:=τ) HT hs (h.batchSmall j X' he hl)
    refine HH.weaken ⟨2,fun i => ?_⟩ ?_
    · change 0+n i+n i*sz i+1 ≤ _
      have hj := hg i
      have hsz : sz i>0 := Nat.mul_pos hl (by change 0<2^(f i); positivity)
      have hy : n i*sz i ≤ w i :=
        calc
          _ = (book X r (f i)).n := hj
          _ ≤ R.n*(book X r (f i)).n := Nat.le_mul_of_pos_left _ hl
          _ = _ := rfl
      have gr : n i ≤ n i*sz i := Nat.le_mul_of_pos_right _ hsz
      omega
    · intro i; change 0+n i*τ i ≤ n i*τ i; omega
  let K := fun i => ferry r (f i) (.dir l z hz) (v i)
  have hh :
      Can m b.B (p s Tt) (bundle cl)
        (fun i => (x i,y i)) (fun i => (fleet X R r (f i)).tape (K i)) w := by
    let s' := p s Tt
    let env i : T s' := (x i,y i)
    have h' : Rig m b.B f s' env cl X R r v := h.gather id env Can.first
    refine h'.chart _ ?_
    let I (i : ι) := Beach α ρ r (f i)
    let u (d : Σ i, I i) : T (p s' Ty.w) := (env d.1,(fleet X R r (f d.1)).loc d.2)
    have HG := h'.gather (Sigma.fst (β:=I)) u (t:=p s' Ty.w) Can.first
    exact HG.direction_get l j z X' (n:=fun d => n d.1) (fun d => he d.1) hz hj
      (Can.snd Can.first) (fun d => d.2) Can.second
  exact hy.save_keep (Able.of_can hh)

lemma open_move (hk : Contract cl b f τ R)
    (hg : ∀ i, n i*(sim R (f i)).n=(book X r (f i)).n)
    (z : Move α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) z (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => toll z * n i * τ i) := by
  cases z with
  | localM M =>
    simpa [toll,Nat.zero_mul] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.point_cost M))
  | shift r z =>
    simpa [toll,Nat.zero_mul] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.shift_cost r z))
  | dir l z hz => simpa [toll,one_mul] using h.open_dir hk hg l z hz

lemma sweep (hk : Contract cl b f τ R)
    (hg : ∀ i, n i*(sim R (f i)).n=(book X r (f i)).n)
    (P : PWord α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline r (f i) P (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => tally P * n i * τ i) := by
  induction P generalizing s v with
  | nil =>
    have ht := h.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _)
    have hz := Able.of_can (b:=b) ht
    -- coast nil
    have hg (i j) : coastline r (f i) [] (v i) j=v i j := rfl
    simp only [tally,List.map_nil,List.sum_nil, Nat.zero_mul]
    exact hz
  | cons g pth ih =>
    let v' i := ferry r (f i) g (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨hk.gear,hk.imag,Can.second⟩
    have hh := ih hl
    have H := (h.open_move (b:=b) (τ:=τ) (by assumption) hg g).save_keep hh
    simpa only [coast_cons,tally,List.map_cons,List.sum_cons,_root_.add_mul] using H

end Rig
end
end PowerSaving.RAM

end OAI
