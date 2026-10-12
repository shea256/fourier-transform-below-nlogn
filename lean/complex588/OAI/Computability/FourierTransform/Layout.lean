import OAI.Computability.FourierTransform.Cost

namespace OAI
/-! Dense indexing on logical array shapes. -/
namespace PowerSaving
open Finset

structure Layout (α : Type*) where
  n : ℕ
  loc : α → ℕ
  bd : ∀ i, loc i < n
  inj : Function.Injective loc
  onto : ∀ j : Fin n, ∃ i, loc i = j.val

namespace Layout

variable {α β μ : Type*}

noncomputable def atFin (L : Layout α) (j : Fin L.n) : α := Classical.choose (L.onto j)
@[simp] theorem loc_atFin (L : Layout α) (j : Fin L.n) :
    L.loc (L.atFin j) = j.val := Classical.choose_spec (L.onto j)

def toIx (L : Layout α) (i : α) : Fin L.n := ⟨L.loc i,L.bd i⟩

noncomputable def index (L : Layout α) : α ≃ Fin L.n :=
  ⟨L.toIx,L.atFin,fun _ => L.inj (loc_atFin _ _), fun _ => Fin.ext (loc_atFin _ _)⟩

noncomputable def tape (L : Layout α) (x : α → μ) : Tape μ :=
  ⟨L.n, fun j => x (L.atFin j)⟩

@[simp] theorem read (L : Layout α) (x : α → μ) (i : α) (z : μ) :
    (L.tape x).look (L.loc i) z = x i := by
  rw [Tape.look_of_lt _ _ (L.bd i)]
  exact congr_arg x (L.index.left_inv _)

theorem verify (L : Layout α) (v : Tape μ) (z : μ) (x : α → μ)
    (h : v.len = L.n) (hx : ∀ i, v.look (L.loc i) z = x i) :
    v = L.tape x := by
  refine Tape.ext_look h z ?_
  intro j hj
  have hl : j<L.n := h ▸ hj
  obtain ⟨i,hi⟩ := L.onto ⟨j,hl⟩
  change L.loc i = j at hi
  subst j
  rw [hx,L.read]

def std (n : ℕ) : Layout (Fin n) :=
  ⟨n,Fin.val, Fin.is_lt, Fin.val_injective, fun j => ⟨j,rfl⟩⟩

theorem card [Fintype α] (X : Layout α) : Fintype.card α = X.n := by
  simpa using Fintype.card_congr X.index

def comap (L : Layout α) (f : β ≃ α) : Layout β where
  n := L.n
  loc := fun j => L.loc (f j)
  bd := fun j => L.bd (f j)
  inj := L.inj.comp f.injective
  onto := fun j => by
    obtain ⟨i,h⟩ := L.onto j
    exact ⟨f.symm i, by simpa using h⟩

theorem tape_comap (X : Layout α) (f : β ≃ α) (x : α → μ) :
    (X.comap f).tape (fun i => x (f i)) = X.tape x := by
  unfold tape
  congr 1
  funext i
  apply congr_arg x (X.inj _)
  exact (loc_atFin (X.comap f) i).trans (loc_atFin X i).symm

/-- A layout on any fixed finite indexing type; only used for fixed operations. -/
noncomputable def someLayout (α : Type*) [Fintype α] : Layout α :=
  (std _).comap (Fintype.equivFin α)

lemma div_join {a b n : ℕ} (hb : b < n) : (a*n+b)/n = a := by
  have hn : n>0 := by omega
  rw [add_comm, Nat.add_mul_div_right b a hn, Nat.div_eq_of_lt hb, zero_add]
lemma mod_join {a b n : ℕ} (hb : b < n) : (a*n+b)%n = b := by
  simp [Nat.mod_eq_of_lt hb]
lemma lt_join {a b m n : ℕ} (h : a < m) (g : b < n) : a*n+b  <  m*n := by
  calc
    _ < a*n+n := Nat.add_lt_add_left g _
    _ ≤ _ := by simpa [add_mul] using Nat.mul_le_mul_right n h

/-- First factor slow, second factor fast. -/
def pair (X : Layout α) (Y : Layout β) : Layout (α × β) where
  n := X.n * Y.n
  loc := fun i => X.loc i.1*Y.n + Y.loc i.2
  bd := fun i => lt_join (X.bd _) (Y.bd _)
  inj := fun {a b} h => by
    change X.loc a.1*Y.n+Y.loc a.2=X.loc b.1*Y.n+Y.loc b.2 at h
    apply Prod.ext
    · apply X.inj
      exact (div_join (Y.bd a.2)).symm.trans ((congr_arg (· / Y.n) h).trans (div_join (Y.bd b.2)))
    · apply Y.inj
      exact (mod_join (Y.bd a.2)).symm.trans ((congr_arg (· % Y.n) h).trans (mod_join (Y.bd b.2)))
  onto := fun j => by
    have hj := j.isLt
    have hy : 0 < Y.n := Nat.pos_of_ne_zero (fun g => by simp [g] at hj)
    obtain ⟨i,hi⟩ := X.onto ⟨j.val/Y.n, (Nat.div_lt_iff_lt_mul hy).mpr hj⟩
    obtain ⟨k,hk⟩ := Y.onto ⟨j.val%Y.n,Nat.mod_lt _ hy⟩
    exact ⟨(i,k),by
      dsimp
      rw [hi,hk,Nat.mul_comm]
      exact Nat.div_add_mod _ _⟩

@[simp] lemma pair_len (X : Layout α) (Y : Layout β) :
    (X.pair Y).n = X.n*Y.n := rfl

@[simp] lemma pair_loc (X : Layout α) (Y : Layout β) (i) :
    (X.pair Y).loc i = X.loc i.1*Y.n+Y.loc i.2 := rfl

lemma pair_div (X : Layout α) (Y : Layout β) (i) :
    (X.pair Y).loc i / Y.n = X.loc i.1 := div_join (Y.bd _)
lemma pair_mod (X : Layout α) (Y : Layout β) (i) :
    (X.pair Y).loc i % Y.n = Y.loc i.2 := mod_join (Y.bd _)

/-- Disjoint coordinate intervals. -/
def cat (X : Layout α) (Y : Layout β) : Layout (α ⊕ β) where
  n := X.n+Y.n
  loc := Sum.elim X.loc (fun i => X.n+Y.loc i)
  bd := by
    rintro (i|i)
    · exact lt_of_lt_of_le (X.bd i) (Nat.le_add_right ..)
    · exact Nat.add_lt_add_left (Y.bd i) _
  inj := by
    rintro (i|i) (j|j) h
    · exact congr_arg Sum.inl (X.inj h)
    · have := X.bd i; simp only [Sum.elim_inl,Sum.elim_inr] at h; omega
    · have := X.bd j; simp only [Sum.elim_inl,Sum.elim_inr] at h; omega
    · exact congr_arg Sum.inr (Y.inj (Nat.add_left_cancel h))
  onto := by
    intro j
    by_cases h : j.val < X.n
    · obtain ⟨i,hi⟩ := X.onto ⟨j.val,h⟩
      exact ⟨.inl i,hi⟩
    · have := j.isLt
      obtain ⟨i,hi⟩ := Y.onto ⟨j.val-X.n,by omega⟩
      refine ⟨.inr i,?_⟩
      change X.n + Y.loc i = _
      dsimp at hi
      omega

/- vector layout: position zero digit is fastest. -/

private def expand (X : Layout α) {k} (x : Fin k→α) :=
  ∑ i, X.loc (x i)*X.n^i.val

private lemma expand_zero (X : Layout α) (x : Fin 0→α) : expand X x=0 := by simp [expand]

private lemma expand_succ (X : Layout α) {k} (x : Fin (k+1)→α) :
    expand X x=expand X (fun i : Fin k => x i.succ)*X.n + X.loc (x 0) := by
  unfold expand
  rw [Fin.sum_univ_succ]
  simp [pow_succ, sum_mul, mul_assoc, Nat.add_comm]

private lemma expand_lt (X : Layout α) {k} (x : Fin k→α) : expand X x < X.n^k := by
  induction k with
  | zero => simp [expand_zero]
  | succ k ih => rw [expand_succ,pow_succ]; exact lt_join (ih _) (X.bd _)

private lemma expand_entry (X : Layout α) {k} (x : Fin k→α) (i : Fin k) :
    expand X x / X.n^i.val % X.n = X.loc (x i) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [expand_succ]
      simpa using mod_join (a:=expand X (fun i : Fin k => x i.succ)) (X.bd (x 0))
    · rw [expand_succ,Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, div_join (X.bd _)]
      exact ih _ j

private lemma expand_onto (X : Layout α) (k) (i : ℕ) (hi : i<X.n^k) :
    ∃ x : Fin k → α, expand X x=i := by
  induction k generalizing i with
  | zero => exact ⟨Fin.elim0, by simp at hi; simp [expand_zero,hi]⟩
  | succ k ih =>
    rw [pow_succ] at hi
    have h : 0<X.n := Nat.pos_of_ne_zero fun a => by simp [a] at hi
    obtain ⟨y,hy⟩ := ih (i/X.n) ((Nat.div_lt_iff_lt_mul h).mpr hi)
    obtain ⟨z,hz⟩ := X.onto ⟨i%X.n,Nat.mod_lt _ h⟩
    refine ⟨Fin.cons z y,?_⟩
    rw [expand_succ]
    simp [hy,hz,Nat.div_add_mod, Nat.mul_comm]

def vecFin (X : Layout α) (k : ℕ) : Layout (Fin k → α) where
  n := X.n^k
  loc := expand X
  bd := expand_lt X
  inj := by
    intro a b h
    funext i
    apply X.inj
    rw [← expand_entry X a i, ← expand_entry X b i, h]
  onto := fun j => expand_onto X k j j.isLt

/-- Uniform radix on axes in layout J. -/
def permFn (e : α ≃ β) (μ : Type*) : (α → μ) ≃ (β → μ) where
  toFun f := f ∘ e.symm
  invFun f := f ∘ e
  left_inv f := by ext; simp
  right_inv f := by ext; simp

noncomputable def digits (J : Layout β) (X : Layout α) : Layout (β → α) :=
  (vecFin X J.n).comap (permFn J.index α)

@[simp] theorem digits_len (J : Layout β) (X : Layout α) :
    (digits J X).n=X.n^J.n := rfl

theorem digits_code [Fintype β] (J : Layout β) (X : Layout α) (x : β→α) :
    (digits J X).loc x = ∑ j, X.loc (x j)*X.n^(J.loc j) := by
  change ∑ i : Fin J.n, X.loc ((x ∘ J.index.symm) i)*X.n^i.val=_
  rw [← Equiv.sum_comp J.index]
  apply sum_congr rfl
  intro j hj
  simp [show J.loc j = (J.index j).val from rfl]

theorem digits_entry (J : Layout β) (X : Layout α) (x : β→α) (j : β) :
    (digits J X).loc x / X.n^(J.loc j) % X.n=X.loc (x j) := by
  change expand X (x∘J.index.symm) / X.n^(J.index j).val % X.n = _
  simp [expand_entry]

end Layout
end PowerSaving

end OAI
