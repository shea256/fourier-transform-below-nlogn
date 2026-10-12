import OAI.Computability.FourierTransform.TensorProgram
import OAI.Computability.FourierTransform.PowerTables

/-!
# Scratch file (key: framework) for "idea B": a Walsh-Hadamard corollary of `hills_program`

NOT part of the upstream development (github.com/openai/math, family 130); written for a
feasibility study.  It imports the upstream files unchanged and adds:

* section 0: a proposed final statement `WHTGoal`, in the style of `DFTGoal` (Goal.lean).
  Section 0 uses only `RAM.lean` and Mathlib.
* section 1: pure mathematics (`H = (1-i) S C S` entrywise, digit-weight products).
* section 2: programs in the upstream `Can` / `Bench` combinator framework
  (`weightTable`, `scale_tape`, `lum_tables`, `wht_can`).
* section 3: packaging of the `Can` statement into `WHTGoal`.

Check with:  `cd verify && . ./env.sh && lake env lean checks/wht/framework/WHT.lean`
-/

namespace OAI
namespace PowerSaving
namespace WHT
noncomputable section

/-! ## 0. Proposed statement (only `RAM.lean` and Mathlib are needed for this section) -/

section Statement
open RAM RAM.Ty Filter Asymptotics

/-- Input `(k, I, x)`: the exponent, the scalar constant `I` (the RAM has no instruction
producing it), and the data array of length `2^k`. Same register kinds as `dftInKind`. -/
abbrev whtInKind := p w (p sc (a (c Paint.left)))
abbrev whtOutKind := a (c Paint.left)

/-- Walsh-Hadamard transform of length `2^k` in natural (Sylvester) order:
`wht k x j = ∑ l, (-1)^(number of common 1-bits of j and l) * x l`. -/
def wht (k : ℕ) (x : Fin (2^k) → ℂ) : Fin (2^k) → ℂ :=
  fun j => ∑ l : Fin (2^k),
    (∏ i ∈ Finset.range k, if j.val.testBit i && l.val.testBit i then (-1 : ℂ) else 1) * x l

/-- One fixed program `solve`; on input `(k, I, x)` it returns the Walsh-Hadamard transform
of `x`, every run is valid (no division by zero), all integers produced and the work
allowance are polynomial in `N = 2^k`, and the work is at most `W k`. -/
def WHTProgram (solve : Prog false whtInKind whtOutKind) (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ k : ℕ,
    let N := 2^k
    let cap := (N+2)^cBound
    W k + 10*(N+2) ≤ cap ∧
    ∀ x : Fin N → ℂ,
      let result := run solve (k, Complex.I, (⟨N,x⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ result.work ≤ W k ∧
      result.val = (⟨N, wht k x⟩ : Tape ℂ)

/-- The exponent of the upstream Lean development (`alpha` in TensorSaving.lean). -/
def whtExponent : ℝ := 1 - 2/(10:ℝ)^11

/-- `W = O(2^k (k+1)^whtExponent)` and `W = o(2^k k)`; with `N = 2^k` this is
`O(N (log₂ N + 1)^(1 - 2e-11))` and `o(N log N)`. -/
def WHTTimeBounds (W : ℕ → ℕ) : Prop :=
  let W' := fun k : ℕ => (W k : ℝ)
  W' =O[atTop] (fun k : ℕ => (2:ℝ)^k * ((k:ℝ)+1)^whtExponent) ∧
  W' =o[atTop] (fun k : ℕ => (2:ℝ)^k * (k:ℝ))

def WHTGoal : Prop := ∃ solve W, WHTProgram solve W ∧ WHTTimeBounds W

/-! Sanity checks of the definition `wht` (sizes 2 and 4). -/
example (x : Fin 2 → ℂ) : wht 1 x (0 : Fin 2) = x 0 + x 1 := by
  change ∑ l : Fin 2, (∏ i ∈ Finset.range 1,
    if (0:ℕ).testBit i && l.val.testBit i then (-1 : ℂ) else 1) * x l = _
  simp [Fin.sum_univ_two]
example (x : Fin 2 → ℂ) : wht 1 x (1 : Fin 2) = x 0 - x 1 := by
  change ∑ l : Fin 2, (∏ i ∈ Finset.range 1,
    if (1:ℕ).testBit i && l.val.testBit i then (-1 : ℂ) else 1) * x l = _
  simp [Fin.sum_univ_two, sub_eq_add_neg]
example (x : Fin 4 → ℂ) : wht 2 x (3 : Fin 4) = x 0 - x 1 - x 2 + x 3 := by
  change ∑ l : Fin 4, (∏ i ∈ Finset.range 2,
    if (3:ℕ).testBit i && l.val.testBit i then (-1 : ℂ) else 1) * x l = _
  simp +decide [Fin.sum_univ_four, Finset.prod_range_succ]
  ring

end Statement

open RAM RAM.Ty RAM.Bench Binary Matrix Finset Complex
universe U V

/-! ## 1. Pure mathematics: digit weights, `lum`, and Hadamard versus the kernel -/

/-- Product over the `j` low binary digits of `n`: a factor `e` for digit 0, `o` for digit 1. -/
def digitWeight (e o : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | j+1, n => (if n % 2 = 0 then e else o) * digitWeight e o j (n/2)

lemma digitWeight_range (e o : ℂ) (j n : ℕ) :
    digitWeight e o j n = ∏ i ∈ range j, if n / 2^i % 2 = 0 then e else o := by
  induction j generalizing n with
  | zero => simp [digitWeight]
  | succ j ih =>
    have e1 : ∀ i, n / 2 / 2^i = n / 2^(i+1) := fun i => by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [digitWeight, ih, prod_range_succ']
    simp only [e1, pow_zero, Nat.div_one]
    exact mul_comm _ _

lemma digitWeight_bits (e o : ℂ) (k : ℕ) (x : Bits k) :
    digitWeight e o k ((bits k).loc x) = ∏ i : Fin k, if x i = 0 then e else o := by
  rw [digitWeight_range,
    ← Fin.prod_univ_eq_prod_range (fun i => if (bits k).loc x / 2^i % 2 = 0 then e else o) k]
  refine prod_congr rfl fun i _ => ?_
  simp only [bits_div, ZMod.val_eq_zero]

/-- The table of digit weights, as a RAM array of scalars. -/
def weightTab (e o : ℂ) (j : ℕ) : T (a sc) := Tape.tab (2^j) (digitWeight e o j)

lemma tape_loc {α : Type*} {μ : Type*} (L : Layout α) (f : ℕ → μ) :
    L.tape (fun x => f (L.loc x)) = Tape.tab L.n f := by
  unfold Layout.tape Tape.tab
  congr 1
  funext j
  simp

lemma weightTab_bits (e o : ℂ) (k : ℕ) :
    weightTab e o k = (bits k).tape (fun y => ∏ i : Fin k, if y i = 0 then e else o) :=
  calc weightTab e o k
      = (bits k).tape (fun x => digitWeight e o k ((bits k).loc x)) :=
        (tape_loc (bits k) (digitWeight e o k)).symm
    _ = _ := congrArg (bits k).tape (funext fun y => digitWeight_bits e o k y)

lemma weight_pre (k : ℕ) (y : Bits k) :
    (∏ i : Fin k, if y i = 0 then (1 : ℂ) else I) = lum y := rfl

lemma weight_post (k : ℕ) (y : Bits k) :
    (∏ i : Fin k, if y i = 0 then (1 - I) else (1 + I)) = (1 - I)^k * lum y := by
  have h : I^2 = -1 := Complex.I_sq
  have step : ∀ i : Fin k, (if y i = 0 then (1 - I) else (1 + I)) = (1 - I) * tint (y i) := by
    intro i
    by_cases hy : y i = 0
    · simp [tint, hy]
    · simp only [tint, ite_eq_right hy]
      linear_combination h
  simp only [step, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, lum]

/-- Entrywise: `H = (1-i) * S * C * S` with `S = diag(1,i)`. -/
lemma littleH_eq (i j : F) : littleH i j = (1 - I) * (tint i * littleC i j * tint j) := by
  have h : I^2 = -1 := Complex.I_sq
  have hca : (1 - I) * ca = 1 := by unfold ca; linear_combination (-1/2 : ℂ) * h
  have hcb : (1 - I) * cb = -I := by unfold cb; linear_combination (1/2 : ℂ) * h
  have t0 : tint (0:F) = 1 := by simp [tint]
  have t1 : tint (1:F) = I := by simp [tint]
  have H00 : littleH 0 0 = 1 := by simp [littleH, sign]
  have H01 : littleH 0 1 = 1 := by simp [littleH, sign]
  have H10 : littleH 1 0 = 1 := by simp [littleH, sign]
  have H11 : littleH 1 1 = -1 := by simp [littleH, sign]
  have C00 : littleC 0 0 = ca := by simp [littleC]
  have C01 : littleC 0 1 = cb := by simp [littleC]
  have C10 : littleC 1 0 = cb := by simp [littleC]
  have C11 : littleC 1 1 = ca := by simp [littleC]
  rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl
  · rw [H00, C00, t0]; linear_combination (-1 : ℂ) * hca
  · rw [H01, C01, t0, t1]; linear_combination h - I * hcb
  · rw [H10, C10, t0, t1]; linear_combination h - I * hcb
  · rw [H11, C11, t1]; linear_combination (-1 : ℂ) * h - I^2 * hca

/-- `H^{⊗α} = (1-i)^{|α|} · diag(lum) · C^{⊗α} · diag(lum)`, entrywise. -/
lemma wal_eq_kernel {α : Type*} [Fintype α] (x y : Space α) :
    wal α x y = (1 - I)^(Fintype.card α) * (lum x * kernel α x y * lum y) := by
  simp only [wal, kernel, lum, digitProd_apply, littleH_eq, prod_mul_distrib, prod_const,
    card_univ]

/-- The Walsh-Hadamard transform is the kernel transform conjugated by `diag(lum)`. -/
lemma wal_ripple (k : ℕ) (v : Bits k → ℂ) (y : Bits k) :
    (wal (Fin k) *ᵥ v) y = ((1 - I)^k * lum y) * ripple k (fun z => lum z * v z) y := by
  simp only [ripple, Matrix.mulVec, dotProduct, wal_eq_kernel, Fintype.card_fin, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  ring

/-! ## 2. Programs -/

section Programs
variable {ι : Type U} {m : Bool}

/-- Doubling construction of the weight table: `2^k` entries in `O(2^k)` work.
Copy of the proof pattern of upstream `Bench.pylon` (PowerTables.lean). -/
lemma weightTable {b : Bench m ι} {k : ι → ℕ} (h : b.Nick k)
    (g : Small b.size fun i => 2^k i) {e o : ι → ℂ}
    (he : b.Moves (fun _ => 0) sc e) (ho : b.Moves (fun _ => 0) sc o) :
    b.Moves (fun i => 2^k i) (a sc) fun i => weightTab (e i) (o i) (k i) := by
  let V (i : ι) (j : ℕ) : T (a sc) := weightTab (e i) (o i) j
  have F := Instant.climbs b k V (t:=a sc)
  have HB : b.Moves (fun _ => 0) (a sc) fun i => V i 0 :=
    ((arrayNow (Nick.wc 1) (t:=sc) (fun _ _ => 1) Moves.one).weaken (Dom.const _ _)).congr
      fun i => by
        simp only [V,weightTab,pow_zero]
        exact tape_congr_sized fun j hj => by simp [digitWeight]
  have hm := tokenNow b k V
  let R (i : During k) := 2^i.j
  let D := b.climbs k (a sc) V
  have hu : Small D.size R := (g.reindex _).mono fun i =>
    Nat.pow_le_pow_right (by omega) i.hj.le
  have hh : D.Nick R := ⟨hm.len hu,hu⟩
  let Y (i : During k) := 2^(i.j+1)
  have hY : D.Nick Y :=
    (hh.mul (Nick.wc 2)).congr fun i => (pow_succ _ _).symm
  have G := Instant.scan D Y
  have hp := chop hY
  have hr := Moves.pick (t:=sc) (n:=fun i => R i.i) (k:=fun i : During Y => i.j/2)
    (fun i j => digitWeight (e i.i.i) (o i.i.i) i.i.j j)
    (hm.transfer G) (hp.div (Nick.wc 2)).close (fun i => by
      have hpp : i.j < Y i.i := i.hj
      simp only [R,Y,pow_succ] at *
      omega)
  have hk := repeatM h V HB (u:=fun _ j => 2^(j+1))
    (arrayNow hY (t:=sc) (fun i j => digitWeight (e i.i) (o i.i) (i.j+1) j)
      ((((hp.residue (Nick.wc 2)).close.branch
        ((he.transfer (G.next F)).mul hr) ((ho.transfer (G.next F)).mul hr))).congr fun i => by
          by_cases H : i.j % 2 = 0
          · rw [digitWeight, ite_eq_left H, ite_eq_left H]
          · rw [digitWeight, ite_eq_right H, ite_eq_right H]))
  exact hk.weaken ⟨4,fun i => by
    dsimp
    rw [unit_doubling]
    have hh : k i < 2^k i := Nat.lt_two_pow_self
    omega⟩

/-- Pointwise product of a scalar table and a data tape over the same layout,
in `O(length)` work, when both tapes and the length are available at constant cost. -/
theorem scale_tape {α : ι → Type V} {s : Ty} {x : ι → T s} {B : ι → ℕ}
    {L : ∀ i, Layout (α i)} {cl : Paint} {t v : ∀ i, α i → ℂ}
    (hn : Has m B s w x (fun i => (L i).n)) (hs : Small B fun i => (L i).n)
    (ht : Has m B s (a sc) x (fun i => (L i).tape (t i)))
    (hv : Has m B s (a (c cl)) x (fun i => (L i).tape (v i))) :
    Can m B s (a (c cl)) x (fun i => (L i).tape (fun j => t i j * v i j))
      (fun i => (L i).n) := by
  let Q := Σ i, α i
  let σ : Q → ι := Sigma.fst
  have g : Has m (fun d : Q => B d.1) (p s w) (c cl)
      (fun d => (x d.1,(L d.1).loc d.2)) (fun d => t d.1 d.2 * v d.1 d.2) :=
    Can.mul
      (Can.fetch (t:=sc) (L:=fun d : Q => L d.1) (v:=fun d : Q => t d.1) (i:=fun d : Q => d.2)
        (Can.first.then_do (ht.reindex σ)) Can.second)
      (Can.fetch (t:=c cl) (L:=fun d : Q => L d.1) (v:=fun d : Q => v d.1) (i:=fun d : Q => d.2)
        (Can.first.then_do (hv.reindex σ)) Can.second)
  have H := Can.layout (L:=L) (t:=c cl) (P:=fun _ => 0) (v:=fun i j => t i j * v i j) hn g hs
  simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at H
  exact H

/-- In any environment where `k` and the constant `I` are available at constant cost, the
two diagonal tables (`lum` and `(1-I)^k * lum`) can be built in `O(2^k)` work. -/
lemma lum_tables {s : Ty} {B : ι → ℕ} {x : ι → T s} {k : ι → ℕ}
    (hk : Knows m B s x k) (hks : Small B k) (hp : Small B fun i => 2^k i)
    (hI : Has m B s sc x (fun _ => I)) :
    Can m B s (a sc) x (fun i => (bits (k i)).tape (fun y => lum y)) (fun i => 2^k i) ∧
    Can m B s (a sc) x (fun i => (bits (k i)).tape (fun y => (1 - I)^k i * lum y))
      (fun i => 2^k i) := by
  let b : Bench m ι := ⟨B, s, x⟩
  have hN : b.Nick k := ⟨hk, hks⟩
  have hI' : b.Moves (fun _ => 0) sc (fun _ => I) := hI
  have T1 : b.Moves (fun i => 2^k i) (a sc) fun i => weightTab 1 I (k i) :=
    weightTable hN hp Moves.one hI'
  have T2 : b.Moves (fun i => 2^k i) (a sc) fun i => weightTab (1 - I) (1 + I) (k i) :=
    weightTable hN hp (Moves.one.sub hI') (Moves.one.add hI')
  have T1c : Can m B s (a sc) x (fun i => weightTab 1 I (k i)) (fun i => 2^k i) := T1
  have T2c : Can m B s (a sc) x (fun i => weightTab (1 - I) (1 + I) (k i)) (fun i => 2^k i) := T2
  constructor
  · refine Can.cong T1c (fun _ => rfl) (fun i => ?_)
    exact (weightTab_bits _ _ _).trans
      (congrArg (bits (k i)).tape (funext fun y => weight_pre (k i) y))
  · refine Can.cong T2c (fun _ => rfl) (fun i => ?_)
    exact (weightTab_bits _ _ _).trans
      (congrArg (bits (k i)).tape (funext fun y => weight_post (k i) y))

end Programs

/-- **Walsh-Hadamard engine in the `Can` framework.**  Same shape and same work bound as
upstream `hills_program`, with the kernel `ripple k` replaced by the Walsh matrix `wal (Fin k)`. -/
theorem wht_can (cl : Paint) (m : Bool) {ι : Type U} (k : ι → ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (wal (Fin (k i)) *ᵥ v i))
      (fun i => 2^k i*hills (k i)) := by
  let B (i : ι) : ℕ := 2^k i
  let W (i : ι) : ℕ := 2^k i*hills (k i)
  let x (i : ι) : T (simIn cl) := givenBits cl (k i) (v i)
  let L (i : ι) : Layout (Bits (k i)) := bits (k i)
  let u (i : ι) (y : Bits (k i)) : ℂ := lum y * v i y
  let r (i : ι) : Bits (k i) → ℂ := ripple (k i) (u i)
  have hd : Dom W B := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hills_pos _))
  have sB : Small B fun i => (L i).n := Small.self B
  have sp : Small B fun i => 2^k i := Small.self B
  have sk : Small B k := (Small.self B).mono fun i => Nat.lt_two_pow_self.le
  -- what the input environment `(k, I, tape v)` offers at constant cost
  have hk : Knows m B (simIn cl) x k := Can.first
  have hI : Has m B (simIn cl) sc x (fun _ => I) := Can.second.fst
  have hX : Has m B (simIn cl) (bundle cl) x fun i => (L i).tape (v i) := Can.second.snd
  have hl : Knows m B (simIn cl) x fun i => (L i).n := hX.len (Small.self B)
  -- step 1: pre-scale by lum
  have A1 : Can m B (simIn cl) (bundle cl) x (fun i => (L i).tape (u i)) B := by
    refine Can.bind (lum_tables hk sk sp hI).1 (g := ?_)
    let s1 := p (simIn cl) (a sc)
    let e1 (i : ι) : T s1 := (x i,(L i).tape (fun y => lum y))
    have f1 : Has m B s1 (simIn cl) e1 x := Can.first
    exact scale_tape (L:=L) (t:=fun (i : ι) (y : Bits (k i)) => lum y) (v:=v) (x:=e1)
      (f1.then_do hl) sB Can.second (f1.then_do hX)
  -- step 2: the upstream engine on the pre-scaled vector
  have A2 : Can m B (simIn cl) (bundle cl) x (fun i => (L i).tape (r i)) W := by
    refine Can.then_do ?_ (hills_program cl m k u)
    exact Can.pair Can.first ((Can.second.fst).pair (A1.weaken hd))
  -- step 3: post-scale by (1-I)^k * lum
  refine Can.bind A2 (g := ?_)
  let s2 := p (simIn cl) (bundle cl)
  let e2 (i : ι) : T s2 := (x i,(L i).tape (r i))
  change Can m B s2 (bundle cl) e2 _ W
  have f2 : Has m B s2 (simIn cl) e2 x := Can.first
  have T2 := (lum_tables (f2.then_do hk) sk sp (f2.then_do hI)).2
  refine Can.bind (T2.weaken hd) (g := ?_)
  let s3 := p s2 (a sc)
  let e3 (i : ι) : T s3 := (e2 i,(L i).tape (fun y => (1 - I)^k i * lum y))
  have f3 : Has m B s3 s2 e3 e2 := Can.first
  have A3 := scale_tape (L:=L) (t:=fun (i : ι) (y : Bits (k i)) => (1 - I)^k i * lum y)
    (v:=r) (x:=e3) (cl:=cl)
    (f3.then_do (f2.then_do hl)) sB Can.second (f3.then_do Can.second)
  refine Can.cong (A3.weaken hd) (fun _ => rfl) (fun i => ?_)
  exact congrArg (L i).tape (funext fun y => (wal_ripple (k i) (v i) y).symm)

/-! ## 3. Packaging into the explicit statement -/

section Explicit
open Filter Asymptotics

lemma whtExponent_eq : whtExponent = alpha := rfl

/-- Same content as `wht_can`, with the single program and its constants made explicit. -/
theorem wht_program_internal : ∃ (solve : Prog false whtInKind whtOutKind) (C d : ℕ),
    ∀ (k : ℕ) (v : Bits k → ℂ),
      (run solve (k, Complex.I, (bits k).tape v)).OK ((bits k).tape (wal (Fin k) *ᵥ v))
        (C*(2^k*hills k+1)) ((2^k+2)^d) := by
  let ι := Σ k : ℕ, (Bits k → ℂ)
  have H := wht_can Paint.left false (ι:=ι) (fun i => i.1) (fun i => i.2)
  obtain ⟨f,C,d,hf⟩ := Can.unfold_bound H
  exact ⟨f,C,d,fun k v => hf ⟨k,v⟩⟩

/-! ### bridge between `(bits k).tape` / `wal` and the explicit statement -/

lemma tape_of_fin (k : ℕ) (x : Fin (2^k) → ℂ) :
    (bits k).tape (fun y => x ((bits k).toIx y)) = (⟨2^k, x⟩ : Tape ℂ) := by
  show (⟨2^k, fun j : Fin (2^k) => x ((bits k).toIx ((bits k).atFin j))⟩ : Tape ℂ) = ⟨2^k, x⟩
  congr 1
  funext j
  exact congrArg x (Fin.ext (show ((bits k).toIx ((bits k).atFin j)).val = j.val from
    Layout.loc_atFin (bits k) j))

lemma wal_atFin (k : ℕ) (j l : Fin (2^k)) :
    wal (Fin k) ((bits k).atFin j) ((bits k).atFin l) =
      ∏ i ∈ range k, if j.val.testBit i && l.val.testBit i then (-1 : ℂ) else 1 := by
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => if j.val.testBit i && l.val.testBit i then (-1 : ℂ) else 1) k]
  simp only [wal, digitProd_apply, littleH]
  refine prod_congr rfl fun i _ => ?_
  have hj := bits_div k ((bits k).atFin j) i
  have hl := bits_div k ((bits k).atFin l) i
  have aj : (bits k).loc ((bits k).atFin j) = j.val := Layout.loc_atFin (bits k) j
  have al : (bits k).loc ((bits k).atFin l) = l.val := Layout.loc_atFin (bits k) l
  rw [aj] at hj
  rw [al] at hl
  have v0 : (0 : F).val = 0 := by decide
  have v1 : (1 : F).val = 1 := by decide
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hj, hl]
  rcases bit_cases ((bits k).atFin j i) with h1|h1 <;>
    rcases bit_cases ((bits k).atFin l i) with h2|h2 <;>
    simp [h1, h2, sign, v0, v1]

lemma wht_tape (k : ℕ) (x : Fin (2^k) → ℂ) :
    (bits k).tape (wal (Fin k) *ᵥ fun y => x ((bits k).toIx y)) =
      (⟨2^k, wht k x⟩ : Tape ℂ) := by
  show (⟨2^k, fun j : Fin (2^k) =>
    (wal (Fin k) *ᵥ fun y => x ((bits k).toIx y)) ((bits k).atFin j)⟩ : Tape ℂ) = ⟨2^k, wht k x⟩
  congr 1
  funext j
  let e : Bits k ≃ Fin (2^k) := (bits k).index
  simp only [Matrix.mulVec, dotProduct, wht]
  refine Fintype.sum_equiv e _ _ (fun z => ?_)
  have hz : (bits k).atFin (e z) = z := (bits k).index.symm_apply_apply z
  have h1 := wal_atFin k j (e z)
  rw [hz] at h1
  rw [h1]
  rfl

/-! ### the program -/

theorem wht_program_exists : ∃ (solve : Prog false whtInKind whtOutKind) (C : ℕ),
    WHTProgram solve (fun k => C*(2^k*hills k+1)) := by
  let ι := Σ k : ℕ, (Bits k → ℂ)
  have H := wht_can Paint.left false (ι:=ι) (fun i => i.1) (fun i => i.2)
  obtain ⟨f,C,d,hf⟩ := Can.unfold_bound H
  have hh : Small (fun k : ℕ => 2^k) (fun k => hills k) :=
    (Small.self _).mono fun k => (hills_le k).trans (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have hs : Small (fun k : ℕ => 2^k) (fun k => C*(2^k*hills k+1) + 10*(2^k+2)) :=
    ((Small.const _ C).mul (((Small.self _).mul hh).add (Small.const _ 1))).add
      ((Small.const _ 10).mul ((Small.self _).add (Small.const _ 2)))
  obtain ⟨d',hd'⟩ := hs
  refine ⟨f,C,⟨max d d',fun k => ⟨?_,fun x => ?_⟩⟩⟩
  · exact (hd' k).trans (Small.pow_mono_degree _ (le_max_right d d'))
  · let v : Bits k → ℂ := fun y => x ((bits k).toIx y)
    have h : (run f (givenBits Paint.left k v)).OK ((bits k).tape (wal (Fin k) *ᵥ v))
        (C*(2^k*hills k+1)) ((2^k+2)^d) := hf ⟨k,v⟩
    have e1 : givenBits Paint.left k v = (k, Complex.I, (⟨2^k,x⟩ : Tape ℂ)) := by
      unfold givenBits
      rw [tape_of_fin]
    rw [e1] at h
    intro result
    exact ⟨h.valid, h.bound.trans (Small.pow_mono_degree _ (le_max_left d d')), h.time,
      h.result.trans (wht_tape k x)⟩

/-! ### the work bound -/

lemma rpow_alpha_little :
    (fun k : ℕ => ((k:ℝ)+1)^alpha) =o[atTop] (fun k : ℕ => (k:ℝ)) := by
  rw [isLittleO_iff]
  intro cc hc
  have hy : 0 < 1 - alpha := sub_pos.mpr alpha_lt
  have ht : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hz := ((tendsto_rpow_neg_atTop hy).comp ht).eventually (gt_mem_nhds (half_pos hc))
  filter_upwards [hz, eventually_ge_atTop 1] with k hk h1
  have hk' : ((k:ℝ)+1)^(-(1-alpha)) < cc/2 := hk
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast h1
  have hpos : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hnn : (0:ℝ) ≤ ((k:ℝ)+1)^(-(1-alpha)) := by positivity
  have hsplit : ((k:ℝ)+1)^alpha = ((k:ℝ)+1) * ((k:ℝ)+1)^(-(1-alpha)) := by
    have hal : alpha = 1 + -(1-alpha) := by ring
    conv_lhs => rw [hal]
    rw [Real.rpow_add hpos, Real.rpow_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hsplit]
  nlinarith [mul_le_mul_of_nonneg_right (by linarith : (k:ℝ)+1 ≤ 2*k) hnn,
    mul_le_mul_of_nonneg_left hk'.le (by linarith : (0:ℝ) ≤ 2*k)]

theorem wht_time (C : ℕ) : WHTTimeBounds (fun k => C*(2^k*hills k+1)) := by
  have hO : (fun k : ℕ => ((C*(2^k*hills k+1) : ℕ) : ℝ)) =O[atTop]
      (fun k : ℕ => (2:ℝ)^k * ((k:ℝ)+1)^alpha) := by
    refine IsBigO.of_bound (3*C) (Eventually.of_forall fun k => ?_)
    have h1 : (1:ℝ) ≤ ((k:ℝ)+1)^alpha := Real.one_le_rpow (by simp) alpha_pos.le
    have h2 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have h3 := hills_real k
    have hB : (1:ℝ) ≤ (2:ℝ)^k * ((k:ℝ)+1)^alpha := one_le_mul_of_one_le_of_one_le h2 h1
    have hA : (2:ℝ)^k * (hills k:ℝ) ≤ 2 * ((2:ℝ)^k * ((k:ℝ)+1)^alpha) := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (2:ℝ)^k)
      linarith
    have hC : (0:ℝ) ≤ (C:ℝ) := Nat.cast_nonneg C
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (by linarith :
      (2:ℝ)^k * (hills k:ℝ) + 1 ≤ 3 * ((2:ℝ)^k * ((k:ℝ)+1)^alpha)) hC]
  exact ⟨hO, hO.trans_isLittleO ((isBigO_refl _ _).mul_isLittleO rpow_alpha_little)⟩

/-- **Walsh-Hadamard transform of length `N = 2^k` in `O(N (log N)^alpha) = o(N log N)`
operations**, in the exact RAM model of the upstream DFT theorem. -/
theorem wht_main : WHTGoal := by
  obtain ⟨s,C,h⟩ := wht_program_exists
  exact ⟨s,_,h,wht_time C⟩

end Explicit

end
end WHT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RAM.hills_program
#print axioms OAI.PowerSaving.WHT.wht_can
#print axioms OAI.PowerSaving.WHT.wht_program_internal
#print axioms OAI.PowerSaving.WHT.wht_main
#check @OAI.PowerSaving.WHT.wht_can
#check @OAI.PowerSaving.WHT.wht_main
#print OAI.PowerSaving.WHT.WHTGoal
