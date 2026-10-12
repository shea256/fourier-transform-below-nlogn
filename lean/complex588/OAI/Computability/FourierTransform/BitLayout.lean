import OAI.Computability.FourierTransform.Layout
import OAI.Computability.FourierTransform.DirectionalWords

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

variable {α : Type*}

abbrev Bits (k : ℕ) := Space (Fin k)

def lbit : Layout F where
  n := 2
  loc := fun i => i.val
  bd := ZMod.val_lt
  inj := by
    intro i j h
    rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;>
      first | rfl | (simp only [ZMod.val_zero,ZMod.val_one] at h; omega)
  onto := by
    intro j; fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

def shape (X : Layout α) : Layout (Space α) := X.digits lbit

def bits (k : ℕ) : Layout (Bits k) := shape (Layout.std k)

@[simp] theorem bit_len (X : Layout α) : (shape X).n=2^X.n := rfl

@[simp] theorem bits_len (k : ℕ) : (bits k).n=2^k := rfl

theorem bits_loc (k : ℕ) (x : Bits k) :
    (bits k).loc x = ∑ i : Fin k, (x i).val*2^i.val := Layout.digits_code ..

theorem bits_div (k : ℕ) (x : Bits k) (i : Fin k) :
    ((bits k).loc x / 2^i.val)%2 = (x i).val := Layout.digits_entry ..

theorem bits_lit (k : ℕ) : (bits k).loc (fun _ => 1)+1=2^k := by
  rw [bits_loc]
  simp only [ZMod.val_one]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ, pow_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, ← mul_assoc, ← sum_mul]
    omega

-- Amplification axes. First come all m groups whose f-bit digit is indexed by one of α.
-- These are followed by r spectator axes.
abbrev Layers (α : Type*) (r f : ℕ) := (α × Fin f) ⊕ Fin r
def stick (X : Layout α) (r f : ℕ) : Layout (Layers α r f) :=
  (X.pair (Layout.std f)).cat (Layout.std r)

abbrev Grid (α : Type*) (r f : ℕ) := Bits r × Sky α f

def rows (α : Type*) (f : ℕ) : Sky α f ≃ (α → Bits f) where
  toFun x i j := x j i
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl

/-- Slow spectator, then column positions in α each with an f-bit digit. -/
def bodyOrder (X : Layout α) (f : ℕ) : Layout (Sky α f) :=
  (X.digits (bits f)).comap (rows α f)

def book (X : Layout α) (r f : ℕ) : Layout (Grid α r f) :=
  (bits r).pair (bodyOrder X f)

@[simp] theorem stick_len (X : Layout α) (r f) :
    (stick X r f).n=X.n*f+r := rfl

@[simp] theorem book_len (X : Layout α) (r f) :
    (book X r f).n = 2^(X.n*f+r) := by
  change 2^r*(2^f)^X.n=_
  rw [pow_add,Nat.mul_comm X.n, pow_mul,mul_comm]

def build (α : Type*) (r f : ℕ) : Grid α r f ≃ Space (Layers α r f) where
  toFun x
    | .inl (i,j) => x.2 j i
    | .inr i => x.1 i
  invFun x := (fun i => x (.inr i), fun j i => x (.inl (i,j)))
  left_inv _ := rfl
  right_inv x := by ext (⟨i,j⟩|i) <;> rfl

theorem book_code {α : Type*} [Fintype α] (X : Layout α)
    (r f : ℕ) (x : Grid α r f) :
    (shape (stick X r f)).loc (build α r f x) = (book X r f).loc x := by
  unfold shape
  rw [Layout.digits_code,Fintype.sum_sum_type,Fintype.sum_prod_type]
  change
    (∑ i : α, ∑ j : Fin f, (x.2 j i).val * 2^(X.loc i*f+j.val)) +
    (∑ j : Fin r, (x.1 j).val * 2^(X.n*f+j.val)) =
     (bits r).loc x.1*(2^f)^X.n+(X.digits (bits f)).loc (fun i j => x.2 j i)
  rw [bits_loc,Layout.digits_code]
  simp_rw [bits_loc]
  simp only [pow_add,sum_mul]
  -- compare sums
  rw [Nat.add_comm]
  have h (a b : ℕ) : (2:ℕ)^(a*b)=(2^b)^a := by rw [Nat.mul_comm, pow_mul]
  simp_rw [h]
  simp only [mul_assoc, bits_len, mul_left_comm, mul_comm]

def normIndex (X : Layout α) {k} (h : X.n=k) : α ≃ Fin k :=
  X.index.trans (finCongr h)

lemma normIndex_val (X : Layout α) {k} (h : X.n=k) (i : α) :
    ((normIndex X h) i).val=X.loc i := rfl

lemma normal_code {α : Type*} [Fintype α] (X : Layout α) {k}
    (h : X.n=k) (x : Space α) :
    (bits k).loc ((Layout.permFn (normIndex X h) F) x) = (shape X).loc x := by
  rw [bits_loc]
  unfold shape
  rw [Layout.digits_code,← Equiv.sum_comp (normIndex X h)]
  apply sum_congr rfl
  intro j hj
  change (x ((normIndex X h).symm _)).val * _ = (x j).val * _
  simp only [Equiv.symm_apply_apply,normIndex_val]
  rfl

def serial (X : Layout α) (r f : ℕ) {k} (h : X.n*f+r=k) :
    Grid α r f ≃ Bits k :=
  (build α r f).trans (Layout.permFn (normIndex (stick X r f) h) F)

lemma serial_code {α : Type*} [Fintype α] (X : Layout α) (r f) {k}
    (h : X.n*f+r=k) (x : Grid α r f) :
    (bits k).loc (serial X r f h x) = (book X r f).loc x := by
  exact (normal_code (stick X r f) h (build α r f x)).trans (book_code X r f x)

theorem kernel_permute {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (x y : Space α) :
    kernel β (Layout.permFn e F x) (Layout.permFn e F y) = kernel α x y := by
  change (∏ j, littleC (x (e.symm j)) (y (e.symm j)))=_
  rw [← Equiv.prod_comp e]
  simp [kernel]

lemma kernel_build {α : Type*} [Fintype α] (r f : ℕ)
    (x y : Grid α r f) :
    kernel (Layers α r f) (build α r f x) (build α r f y) =
    kernel (Fin r) x.1 y.1 * digitProd (fun _ : Fin f => kernel α) x.2 y.2 := by
  unfold kernel
  simp only [digitProd_apply, Fintype.prod_sum_type,Fintype.prod_prod_type]
  change (∏ i : α, ∏ j : Fin f, littleC _ _)*(∏ i : Fin r, littleC _ _) = _
  rw [mul_comm, prod_comm]
  rfl

lemma kernel_serial {α : Type*} [Fintype α] (X : Layout α) (r f) {k}
    (h : X.n*f+r=k) (x y : Grid α r f) :
    kernel (Fin k) (serial X r f h x) (serial X r f h y) =
    kernel (Fin r) x.1 y.1 * digitProd (fun _ : Fin f => kernel α) x.2 y.2 :=
  (kernel_permute _ _ _).trans (kernel_build r f x y)

-- actValue convenience: kernel axes matrix times input
def ripple (k : ℕ) (x : Bits k → ℂ) := kernel (Fin k) *ᵥ x

def chords {α : Type*} (r f : ℕ) (x : Grid α r f → ℂ) : Grid α r f → ℂ :=
  fun i => ripple r (fun j => x (j,i.2)) i.1

lemma ripple_grid {α : Type*} [Fintype α] [DecidableEq α]
    (X : Layout α) (r f) {k} (h : X.n*f+r=k)
    (x : Bits k → ℂ) (i : Grid α r f) :
    let e := serial X r f h
    ripple k x (e i) =
    matAct f (kernel α) (fun j => chords r f (x ∘ e) (i.1,j)) i.2 := by
  intro e
  change (∑ j, kernel (Fin k) _ j*x j)=
    ∑ j, _ * ∑ l, kernel (Fin r) i.1 l*x (e (l,j))
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  simp_rw [show ∀ j, kernel (Fin k) (e i) (e j)=_ from kernel_serial X r f h i]
  simp only [mul_sum]
  rw [sum_comm]; apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro b hb
  dsimp; ac_rfl

end
end PowerSaving.Binary

end OAI
