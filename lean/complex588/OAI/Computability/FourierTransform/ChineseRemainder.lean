import OAI.Computability.FourierTransform.SectorPacking

namespace OAI
/-! CRT permutations. Using the same scaled index for input and output,
and the appropriate primitive root on each axis. -/
namespace PowerSaving.Grove
open Finset Spectral
noncomputable section

structure Isles (r : Axes) (l : ℕ) : Prop where
  good : Splits r l
  apart : ∀ i<l, (r i).Coprime (extent r i)

lemma Isles.cut {r : Axes} {l : ℕ} (h : Isles r l) {i : ℕ} (hi : i ≤ l) :
    Isles r i := ⟨h.good.cut hi,fun j hj => h.apart j (lt_of_lt_of_le hj hi)⟩

lemma Isles.axis_dvd {r : Axes} {l : ℕ} (h : Isles r l) :
    ∀ i<l,r i ∣ extent r l := by
  induction l with
  | zero => intro i hi; omega
  | succ l ih =>
    intro i hi; rw [extent]
    by_cases hz : i=l
    · simp [hz]
    · exact dvd_mul_of_dvd_left (ih (h.cut (by omega)) _ (by omega)) _

def tide (p r a b : ℕ) := (a*r+b*p)%(p*r)

/-- Recursively mixed-radix → one-dimensional index. -/
def ford (r : Axes) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | l+1 => fun i =>
    tide (extent r l) (r l) (ford r l (i/r l)) (i%r l)

def spray (Z : ℂ) (N q : ℕ) := Z^((N/q)*(N/q))

def gale (Z : ℂ) : Wood := fun i j => Z^(i*j)

lemma spray_here (Z : ℂ) (n q : ℕ) (h : 0<q) : spray Z (n*q) q=Z^(n*n) := by
  rw [spray,Nat.mul_div_cancel _ h]

lemma spray_tide {Z : ℂ} {n q : ℕ} (hq : 0<q) (hp : n.Coprime q)
    (h : IsPrimitiveRoot Z (n*q)) :
    IsPrimitiveRoot (Z^(q*q)) n := by
  have hh := h.pow_of_dvd (p:=q) (by omega) (by simp)
  rw [Nat.mul_div_cancel _ hq] at hh
  rw [pow_mul]; exact hh.pow_of_coprime q hp.symm

lemma spray_sec {Z : ℂ} {N p r : ℕ} (hr : r ∣ N) (hh : 0<r) :
    spray Z (N*p) r=spray (Z^(p*p)) N r := by
  unfold spray
  obtain ⟨d,rfl⟩ := hr
  rw [Nat.mul_assoc,Nat.mul_div_cancel_left _ hh,Nat.mul_div_cancel_left _ hh,← pow_mul]
  ring_nf

lemma spray_axis {Z : ℂ} {r : Axes} {l : ℕ} (h : Isles r l)
    (hh : IsPrimitiveRoot Z (extent r l)) :
    ∀ i<l, IsPrimitiveRoot (spray Z (extent r l) (r i)) (r i) := by
  induction l generalizing Z with
  | zero => intro i hi; omega
  | succ l ih =>
    intro i hi
    have H := h.cut (i:=l) (by omega)
    have HR := h.apart l (by omega)
    by_cases hg : i=l
    · subst i
      rw [extent,spray_here Z _ _ h.good.here]
      have he : IsPrimitiveRoot Z (r l*extent r l) := by rw [mul_comm]; exact hh
      exact spray_tide H.good.extent_pos HR he
    · have hx : i<l := by omega
      have h1 := H.axis_dvd i hx
      have h2 : 0<r i := lt_of_lt_of_le (by norm_num) (H.good i hx)
      rw [extent,spray_sec h1 h2]
      exact ih H (spray_tide h.good.here HR.symm hh) i hx

lemma gale_mod {Z : ℂ} {n : ℕ} (h : Z^n=1) (i j : ℕ) :
    gale Z (i%n) (j%n)=gale Z i j := by
  unfold gale
  rw [pow_mul,power_mod h i]
  have ht : (Z^i)^n=1 := by rw [← pow_mul,mul_comm,pow_mul,h,one_pow]
  rw [power_mod ht,← pow_mul]

lemma gale_tide {Z : ℂ} {p r : ℕ} (h : Z^(p*r)=1)
    (a b c d : ℕ) :
    gale Z (tide p r a b) (tide p r c d) =
    gale (Z^(r*r)) a c * gale (Z^(p*p)) b d := by
  rw [tide,tide,gale_mod h]; unfold gale
  rw [← pow_mul,← pow_mul,← pow_add]
  rw [show (a*r+b*p)*(c*r+d*p)=r*r*(a*c)+p*p*(b*d)+(p*r)*(a*d+b*c) by ring]
  rw [pow_add,pow_mul Z (p*r),h,one_pow,mul_one]

lemma canopy_gale {Z : ℂ} {r : Axes} {l : ℕ} (h : Isles r l)
    (hh : IsPrimitiveRoot Z (extent r l)) :
    ∀ i<extent r l, ∀ j<extent r l,
    Grove.canopy r (fun x => gale (spray Z (extent r l) (r x))) l i j =
    gale Z (ford r l i) (ford r l j) := by
  induction l generalizing Z with
  | zero => intros; simp [canopy,gale,ford]
  | succ l ih =>
    intro i hi j hj
    have H := h.cut (i:=l) (by omega)
    have HR := h.apart l (by omega)
    have he := spray_tide h.good.here HR.symm hh
    have HG (i : ℕ) (hi : i<l) :
        spray Z (extent r (l+1)) (r i) =
        spray (Z^(r l*r l)) (extent r l) (r i) :=
      spray_sec (H.axis_dvd _ hi) (lt_of_lt_of_le (by norm_num) (H.good i hi))
    have ha := h.good.div_lt hi; have hb := h.good.div_lt hj
    simp only [canopy,ford]
    rw [canopy_congr r l H.good _ (fun i => gale (spray (Z^(r l*r l)) (extent r l) (r i)))
      (by intro i hx a ha b hb; rw [HG i hx]) _ ha _ hb,ih H he _ ha _ hb]
    rw [extent,spray_here Z _ _ h.good.here,gale_tide hh.pow_eq_one]

lemma tide_left {a b c d m n : ℕ} (h : (tide m n a b)=(tide m n c d)) :
    a*n≡c*n [MOD m] := by
  have ht : (a*n+b*m)≡(c*n+d*m) [MOD (m*n)] := h
  have hx := ht.of_dvd (dvd_mul_right m n)
  simpa [Nat.ModEq] using hx

lemma tide_right {a b c d m n : ℕ} (h : (tide m n a b)=(tide m n c d)) :
    b*m ≡ d*m [MOD n] := by
  apply tide_left (b:=a) (d:=c)
  simpa only [tide,add_comm, Nat.mul_comm n m] using h

lemma tide_inj {a b c d m n : ℕ} (h : (tide m n a b)=(tide m n c d))
    (H : m.Coprime n) (ha : a < m) (hc : c < m) (hb : b<n) (hd : d<n) :
    a=c ∧ b=d := by
  have hx := Nat.ModEq.cancel_right_of_coprime H (tide_left h)
  have hy := Nat.ModEq.cancel_right_of_coprime H.symm (tide_right h)
  simp only [Nat.ModEq,Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hd] at hx hy
  exact ⟨hx,hy⟩

theorem ford_rel {r : Axes} {l : ℕ} (h : Isles r l) :
    Reloc (extent r l) (ford r l) := by
  induction l with
  | zero =>
    refine ⟨fun i _ => by simp [ford,extent],fun i hi j hj _ => ?_⟩
    change i<1 at hi; change j<1 at hj; omega
  | succ l ih =>
    have H := h.cut (i:=l) (by omega)
    have he := ih H
    refine ⟨fun i _ => Nat.mod_lt _ h.good.extent_pos,fun i hi j hj ht => ?_⟩
    have ha := h.good.div_lt hi; have hb := h.good.div_lt hj
    obtain ⟨hg,hk⟩ := tide_inj ht (h.apart l (by omega)).symm (he.bd _ ha) (he.bd _ hb)
      (h.good.mod_lt i) (h.good.mod_lt j)
    have hh := he.inj _ ha _ hb hg
    exact (joined i _).symm.trans (by rw [hh,hk,joined])

lemma graft_ford {r : Axes} {l : ℕ} {z : ℂ} (h : Isles r l)
    (hh : IsPrimitiveRoot z (extent r l)) (x : Line) (i : ℕ) (hi : i<extent r l) :
    graft (extent r l) (canopy r (fun i => gale (spray z (extent r l) (r i))) l)
      (fun j => x (ford r l j)) i =
    freq (extent r l) z x (ford r l i) := by
  unfold graft freq
  conv_rhs => rw [← (ford_rel h).sum]
  refine sum_congr rfl ?_
  intro j hj
  rw [canopy_gale h hh _ hi _ (mem_range.mp hj)]; rfl

end
end PowerSaving.Grove

end OAI
