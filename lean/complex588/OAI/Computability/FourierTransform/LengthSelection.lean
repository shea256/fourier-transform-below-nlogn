import OAI.Computability.FourierTransform.PrimeSelection

namespace OAI

/- Selection of length. Explicit loops. -/
namespace PowerSaving.Selection
open Grove
noncomputable section

structure Cart where
  l : ℕ
  q : Axes
  vol : ℕ

namespace Cart

def empty : Cart := ⟨0,fun _ => 0,1⟩
def pushQ (x : Cart) (p : ℕ) : Cart :=
  ⟨x.l+1,fun i => if i=x.l then p else x.q i, x.vol*p⟩

structure Square (x : Cart) : Prop where
  agrees : x.vol=extent x.q x.l
  isles : Isles x.q x.l

lemma Square.empty : empty.Square := by
  exact ⟨rfl,fun i hi => by change i<0 at hi; omega,
    fun i hi => by change i<0 at hi; omega⟩

variable {x : Cart}
lemma push_eq (p : ℕ) {i : ℕ} (h : i<x.l) :
    (x.pushQ p).q i=x.q i := ite_eq_right (Nat.ne_of_lt h)

lemma push_ext (p : ℕ) {i : ℕ} (h : i≤x.l) :
    extent (x.pushQ p).q i=extent x.q i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [extent,ih (by omega),extent,push_eq p (by omega)]

lemma at_push (x : Cart) (p : ℕ) :
    (x.pushQ p).q x.l=p := ite_eq_left rfl

lemma Square.pushQ (h : x.Square) {p : ℕ} (hp : p≥2) (hq : p.Coprime x.vol) :
    (x.pushQ p).Square := by
  let y := x.pushQ p
  refine ⟨?_,?_,?_⟩
  · change x.vol*p=extent y.q x.l*y.q x.l
    rw [push_ext _ le_rfl,at_push,h.agrees]
  · intro i hi
    change i<x.l+1 at hi
    by_cases g : i=x.l
    · rw [g,at_push]; exact hp
    · rw [push_eq _ (by omega)]
      exact h.isles.good _ (by omega)
  · intro i hi
    change i<x.l+1 at hi
    by_cases g : i=x.l
    · rw [g,at_push,push_ext _ le_rfl,← h.agrees]; exact hq
    · rw [push_eq _ (by omega),push_ext _ (by omega)]
      exact h.isles.apart i (by omega)

end Cart

open Cart

def reap (N : ℕ) : ℕ → Cart
  | 0 => Cart.empty
  | p+1 =>
    let x := reap N p
    if Bar p ∧ x.vol*p ≤ N then x.pushQ p else x

structure Baler (N p : ℕ) (x : Cart) : Prop where
  square : x.Square
  odd : Odd x.vol
  top : x.vol ≤ N
  count : x.l≤p
  vars : ∀ i<x.l, Bar (x.q i) ∧ x.q i<p
  more : ∀ q, p≤q → Bar q → q.Coprime x.vol
  hit : x.l=bars p ∨ ∃ q<p,N<x.vol*q

namespace Baler
variable {N p : ℕ} {x : Cart}

lemma empty (N : ℕ) (h : 0<N) : Baler N 0 Cart.empty :=
  ⟨.empty,odd_one,h,Nat.le_refl _,fun i hi => by change i<0 at hi; omega,
    fun p _ _ => Nat.coprime_one_right _,Or.inl bars_zero.symm⟩

lemma push (h : Baler N p x) (g : Bar p) (hp : x.vol*p ≤ N) :
    Baler N (p+1) (x.pushQ p) := by
  have ht : p>2 := g.2
  refine ⟨h.square.pushQ ht.le (h.more p le_rfl g),
    h.odd.mul (g.1.odd_of_ne_two (by omega)),hp,
    Nat.add_le_add_right h.count 1,?_,?_,?_⟩
  · intro i hi
    change i<x.l+1 at hi
    by_cases k : i=x.l
    · rw [k,at_push]; exact ⟨g,by omega⟩
    · rw [push_eq _ (by omega)]
      have hf := h.vars i (by omega)
      exact ⟨hf.1,Nat.lt_trans hf.2 (by omega)⟩
  · intro q hq hg
    change q.Coprime (x.vol*p)
    have hh := h.more q (by omega) hg
    apply hh.mul_right
    apply hg.1.coprime_iff_not_dvd.mpr
    intro ht'
    have := Nat.le_of_dvd (by omega : 0<p) ht'
    omega
  · rcases h.hit with hh|⟨q,hq,hg⟩
    · left; rw [bars_step,ite_eq_left g,← hh]; rfl
    · right
      have hh : x.vol*q≤x.vol*p := Nat.mul_le_mul_left _ hq.le
      omega

lemma pass (h : Baler N p x) (g : ¬ (Bar p ∧ x.vol*p≤N)) :
    Baler N (p+1) x := by
  refine ⟨h.square,h.odd,h.top,h.count.trans (Nat.le_succ _),?_,fun q hq hg =>
    h.more q (by omega) hg,?_⟩
  · intro i hi; have H := h.vars i hi
    exact ⟨H.1,H.2.trans (by omega)⟩
  · by_cases H : Bar p
    · exact Or.inr ⟨p,by omega,Nat.lt_of_not_ge fun hx => g ⟨H,hx⟩⟩
    · rw [bars_step,ite_eq_right H,Nat.add_zero]
      exact h.hit.imp id fun ⟨q,hq,hk⟩ => ⟨q,by omega,hk⟩
end Baler

lemma reap_baler (N p : ℕ) (h : 0<N) : Baler N p (reap N p) := by
  induction p with
  | zero => exact Baler.empty _ h
  | succ p ih =>
    simp only [reap]; split
    · rename_i hk; exact ih.push hk.1 hk.2
    · rename_i hg; exact ih.pass hg

def harvestN (n : ℕ) := silo (stackN n)
def bed (n : ℕ) := reap (2*n) (harvestN n+1)

-- choose dyad by doubling until ≥N
def fill (N p : ℕ) : ℕ→ℕ
  | 0 => 1
  | k+1 => let q := fill N p k
           if p*q<N then q*2 else q

namespace Fill

lemma capacity (N p i : ℕ) : fill N p i ≤ 2^i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [fill,pow_succ]; split <;> omega

lemma fills (N p i : ℕ) : N ≤ p*fill N p i ∨ fill N p i=2^i := by
  induction i with
  | zero => exact Or.inr rfl
  | succ i ih =>
    rw [fill,pow_succ]; split
    · rename_i H; right; rw [ih.resolve_left (not_le.mpr H)]
    · rename_i H; exact Or.inl (Nat.le_of_not_lt H)

lemma radius (N p i : ℕ) (hp : p<N) : p*fill N p i < 2*N := by
  induction i with
  | zero => simp only [fill,mul_one]; omega
  | succ i ih =>
    rw [fill]; split
    · rename_i hk; rw [← mul_assoc]; omega
    · exact ih
lemma dyad (N p i : ℕ) : ∃ j,fill N p i=2^j := by
  induction i with
  | zero => exact ⟨0,rfl⟩
  | succ i ih =>
    rw [fill]; split
    · obtain ⟨j,hj⟩ := ih; exact ⟨j+1,by rw [pow_succ,hj]⟩
    · exact ih

end Fill

def bead (n : ℕ) := fill (2*n) (bed n).vol (stackN n)

def barge (n : ℕ) := (bed n).pushQ (bead n)

def orderE (n : ℕ) := Nat.log 2 (2*harvestN n)+2

lemma orderE_big (n : ℕ) :
    2*harvestN n ≤ 2^orderE n :=
  (Nat.lt_pow_succ_log_self (by omega : 1<2) _).le.trans
    (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))

lemma orderE_small (n : ℕ) :
    2^orderE n ≤ 8*harvestN n := by
  have h : 0<harvestN n := lt_trans (by omega) (silo_big _)
  have hh : 2^(Nat.log 2 (2*harvestN n))≤2*harvestN n := Nat.pow_log_le_self _ (by omega)
  unfold orderE; rw [pow_add]
  norm_num at *
  omega

structure Harbor (n : ℕ) (x : Cart) : Prop where
  square : x.Square
  lower : 2*n ≤ x.vol
  upper : x.vol < 4*n
  count : x.l ≤ stackN n
  sizes : ∀ i<x.l,x.q i≤2^orderE n

theorem barge_spec (n : ℕ) (hn : 0<n) :
    Harbor n (barge n) := by
  let K := stackN n
  let X := bed n
  let S := harvestN n
  let R := 2*n
  let f := bead n
  have hK : R<2^K := stack_above _
  have HT : Baler R (S+1) X := reap_baler R (S+1) (by unfold R; omega)
  have hp : X.vol<R := by
    have H := HT.top
    have hg := HT.odd
    obtain ⟨k,hk⟩ := hg; unfold R at *; omega
  have hh : 2^X.l≤X.vol := HT.square.agrees.symm ▸ HT.square.isles.good.extent_pow
  have hx : X.l<K := Nat.lt_of_not_ge fun H =>
    not_lt.mpr (Nat.pow_le_pow_right (by omega : 0<2) H) (hh.trans_lt (hp.trans hK))
  have hV : 1≤X.vol := HT.square.agrees.symm ▸ HT.square.isles.good.extent_pos
  have hf : R ≤ X.vol*f := by
    rcases Fill.fills R X.vol K with h|h
    · exact h
    · change f=2^K at h
      rw [h]; exact hK.le.trans (Nat.le_mul_of_pos_left _ hV)
  have hg : X.vol*f < 4*n := by
    have : X.vol*f < 2*(2*n) := Fill.radius R X.vol K hp
    omega
  have ht : f≥2 := Nat.le_of_not_lt fun H =>
    not_lt.mpr hf (lt_of_le_of_lt (by
      simpa only [mul_one] using Nat.mul_le_mul_left X.vol (show f≤1 by omega)) hp)
  have hu : f ≤ 2*S := by
    have hf' : X.vol*f < 2*R := Fill.radius R X.vol K hp
    rcases HT.hit with h|⟨q,hq,H⟩
    · have hy : K < bars (S+1) := bar_bounds _
      omega
    · have hy : q ≤ S := by omega
      have hb : R<X.vol*S := H.trans_le (Nat.mul_le_mul_left _ hy)
      by_contra hh
      have H1 := Nat.mul_le_mul_left X.vol (show 2*S ≤ f by omega)
      rw [show X.vol*(2*S)=2*(X.vol*S) by ring] at H1
      omega
  have hF : f.Coprime X.vol := by
    obtain ⟨k,hk⟩ := Fill.dyad R X.vol K
    change f=2^k at hk
    rw [hk]
    exact HT.odd.coprime_two_left.pow_left k
  refine ⟨HT.square.pushQ ht hF,hf,hg,hx,?_⟩
  intro i hi
  change i<X.l+1 at hi
  change (pushQ X f).q i ≤ _
  by_cases H : i=X.l
  · rw [H,at_push]; exact hu.trans (orderE_big n)
  · rw [push_eq _ (by omega)]
    have hy : X.q i < S+1 := (HT.vars i (by omega)).2
    exact le_trans (show _≤2*S by omega) (orderE_big n)

-- explicitly chosen root-order depending on size branch
def Ports (n : ℕ) := 2^orderE n ≤ n
instance (n) : Decidable (Ports n) := inferInstanceAs (Decidable (_ ≤ _))
def express (n : ℕ) := (2*n)*(barge n).vol*2^orderE n
def receipt (n : ℕ) := if Ports n then express n else n

theorem receipt_bound (n : ℕ) (hn : 0<n) :
    0<receipt n ∧ receipt n < 8*n^3 := by
  unfold receipt; split
  · rename_i H
    have hh := barge_spec n hn
    have hx := hh.lower; have hk := hh.upper
    unfold express; unfold Ports at H
    have hg : 0<(barge n).vol := by omega
    refine ⟨by positivity,?_⟩
    calc
      _ ≤ (2*n)*(barge n).vol*n := by gcongr
      _ < (2*n)*(4*n)*n := by gcongr
      _ = 8*n^3 := by ring
  · refine ⟨hn,?_⟩
    have he : 1 ≤ n := hn
    calc
      n ≤ n*n^2 := Nat.le_mul_of_pos_right _ (by positivity)
      _ < 8*n^3 := by
        rw [show n*n^2=n^3 by ring]
        have : 0<n^3 := by positivity
        omega

lemma express_eta (n : ℕ) : 2*n ∣ express n := dvd_mul_of_dvd_left (dvd_mul_right ..) _
lemma express_volume (n : ℕ) : (barge n).vol ∣ express n := dvd_mul_of_dvd_left (dvd_mul_left ..) _
lemma express_halo (n : ℕ) (j : ℕ) (hj : j≤orderE n) : 2^j ∣ express n :=
  dvd_mul_of_dvd_right (pow_dvd_pow _ hj) _
lemma express_I (n : ℕ) : 4 ∣ express n :=
  express_halo n 2 (by unfold orderE; omega)
end
end PowerSaving.Selection

end OAI
