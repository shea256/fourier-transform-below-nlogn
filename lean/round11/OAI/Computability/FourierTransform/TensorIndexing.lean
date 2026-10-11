import OAI.Computability.FourierTransform.FourierWords

namespace OAI

/-! Tensor slot multiplication. Natural-number prefix indexing, most
significant radix first. -/
namespace PowerSaving
noncomputable section

namespace Grove
open Slant Stroke Reel Spectral Matrix Finset Binary

abbrev Axes := ℕ → ℕ

/-- volume of the first j axes -/
def extent (r : Axes) : ℕ → ℕ
  | 0 => 1
  | j+1 => extent r j*r j

/-- Hypothesis in uses of a tuple index (omit entirely any singleton axes). -/
def Splits (r : Axes) (l : ℕ) := ∀ t<l, 2≤r t

namespace Splits
variable {r : Axes} {l : ℕ}

lemma cut (h : Splits r l) {j : ℕ} (g : j ≤ l) :
    Splits r j :=
  fun t ht => h t (ht.trans_le g)

lemma here (h : Splits r (l+1)) :
    0<r l := Nat.lt_of_lt_of_le (by norm_num) (h l (by omega))

lemma extent_pow (h : Splits r l) :
    2^l ≤ extent r l := by
  induction l with
  | zero => rfl
  | succ l ih => exact (pow_succ ..).le.trans (Nat.mul_le_mul
      (ih (h.cut (by omega))) (h l (by omega)))

lemma extent_pos (h : Splits r l) :
    0<extent r l :=
  Nat.lt_of_lt_of_le (by positivity) h.extent_pow

lemma extent_le {j : ℕ} (h : Splits r l) (hj : j≤l) :
    extent r j ≤ extent r l := by
  induction l with
  | zero =>
    obtain rfl : j=0 := by omega
    rfl
  | succ l ih =>
    by_cases hk : j=l+1
    · rw [hk]
    · refine le_trans (ih (h.cut (by omega)) (by omega)) ?_
      exact Nat.le_mul_of_pos_right _ h.here

lemma axes_le (h : Splits r l) :
    l < extent r l :=
  Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) h.extent_pow

lemma tree_bound (h : Splits r l) :
    ∑ j ∈ range (l+1), extent r j < 2*extent r l := by
  induction l with
  | zero => simp [extent]
  | succ l ih =>
    rw [sum_range_succ]
    have hh := ih (h.cut (by omega))
    have hg : 2 * extent r l ≤ extent r (l+1) := by
      rw [extent,mul_comm]
      exact Nat.mul_le_mul_left _ (h l (by omega))
    omega

lemma div_lt (h : Splits r (l+1)) {i} (hi : i<extent r (l+1)) :
    i / r l < extent r l :=
  (Nat.div_lt_iff_lt_mul h.here).mpr hi

lemma mod_lt (h : Splits r (l+1)) (i : ℕ) :
    i%r l < r l := Nat.mod_lt _ h.here

lemma join_lt (_h : Splits r (l+1)) {a b} (ha : a < extent r l) (hb : b < r l) :
    a*r l+b < extent r (l+1) := by
  have hg := Nat.mul_le_mul_right (r l) (show a+1 ≤ extent r l from ha)
  rw [add_mul,one_mul] at hg
  rw [extent]
  omega

end Splits

lemma joined (i r : ℕ) : i/r*r+i%r=i := by rw [mul_comm]; exact Nat.div_add_mod i r
lemma chops (i j r : ℕ) (hj : j<r) :
    (i*r+j)/r=i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hj,zero_add]
lemma chips (i j r : ℕ) (hj : j<r) :
    (i*r+j)%r=j := by
  simp [add_comm, Nat.mod_eq_of_lt hj]

/-- natural-address matrices (only read in extent) -/
abbrev Wood := ℕ → ℕ → ℂ

def knot (r : ℕ) (X Y : Wood) : Wood := fun i j =>
  ∑ k ∈ range r, X i k*Y k j

def graft (r : ℕ) (X : Wood) (v : Line) : Line := fun i =>
  ∑ k ∈ range r, X i k*v k

def white : Wood := fun i j => if j=i then 1 else 0

def frame (n : ℕ) (X : Wood) : RootMat n := fun i j => X i.val j.val

lemma front_graft (n : ℕ) (X : Wood) (x : Line) :
    front n (graft n X x) = frame n X *ᵥ front n x := by
  ext i
  exact (Fin.sum_univ_eq_sum_range _ _).symm

lemma graft_knot (r : ℕ) (X Y : Wood) (v : Line) :
    graft r (knot r X Y) v=graft r X (graft r Y v) := by
  ext i
  simp only [graft,knot,mul_sum,sum_mul]
  rw [sum_comm]
  simp only [mul_assoc]

lemma graft_white (r : ℕ) (v : Line) (i : ℕ) (hi : i<r) :
    graft r white v i = v i := by simp [white,graft,ite_mul,hi]

lemma graft_congr (r : ℕ) (X : Wood) (v w : Line) (h : ∀ i<r, v i=w i) :
    graft r X v=graft r X w := by
  ext i
  exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

def canopy (r : Axes) (X : ℕ → Wood) : ℕ → Wood
  | 0 => fun _ _ => 1
  | j+1 => fun i k => canopy r X j (i/r j) (k/r j) * X j (i%r j) (k%r j)

lemma canopy_knot (r : Axes) (X Y : ℕ → Wood) (l : ℕ) (h : Splits r l) :
    knot (extent r l) (canopy r X l) (canopy r Y l) =
    canopy r (fun i => knot (r i) (X i) (Y i)) l := by
  induction l with
  | zero => ext i j; simp [knot,extent,canopy]
  | succ l ih =>
    let U := canopy r X l
    let V := canopy r Y l
    rw [funext (show ∀ i, canopy r (fun i => knot (r i) (X i) (Y i)) (l+1) i = _
        from fun i => funext fun k => show canopy _ _ _ i k =
        knot _ U V (i/r l) (k/r l) * _ from by
          rw [ih (h.cut (by omega))]; rfl)]
    ext i j
    simp only [extent, canopy, knot]
    rw [sum_mult]
    simp only [U,V,sum_mul,mul_sum]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl ?_
    intro a ha
    refine sum_congr rfl ?_
    intro b hb
    rw [chops _ _ _ (mem_range.mp hb),chips _ _ _ (mem_range.mp hb)]
    ring

lemma canopy_white (r : Axes) (l : ℕ) (h : Splits r l) :
    ∀ i<extent r l, ∀ j<extent r l,
      canopy r (fun _ => white) l i j=white i j := by
  induction l with
  | zero =>
    intro i hi j hj
    change i<1 at hi; change j<1 at hj
    have h : i=j := by omega
    simp [h,white,canopy]
  | succ l ih =>
    intro i hi j hj
    simp only [canopy]; rw [ih (h.cut (by omega)) _ (h.div_lt hi) _ (h.div_lt hj)]
    unfold white
    have H : j/r l=i/r l → j%r l=i%r l → j=i := fun H J =>
      (joined j _).symm.trans (by rw [H,J,joined])
    split_ifs <;> simp_all

-- synchronization for a reel at every axis
def leafM (u : Stroke) : Wood :=
  fun i j => if j=u.ix i then u.dye i else 0

def leafC (u : Stroke) : Wood :=
  fun i j =>
    if u.partner i=i then white i j
    else (if j=i then ca else 0)+(if j=u.partner i then cb else 0)

lemma graft_leafM {n : ℕ} {u : Stroke} (h : u.Sound n) (v : Line) :
    ∀ i<n, graft n (leafM u) v i=u.applyM v i := by
  intro i hi; simp [graft,leafM,Stroke.applyM,ite_mul,h.bdix i hi]
lemma graft_leafC {n : ℕ} {u : Stroke} (h : u.Sound n) (v : Line) :
    ∀ i<n, graft n (leafC u) v i=u.applyC v i := by
  intro i hi
  by_cases g : u.partner i=i <;>
    simp [graft,leafC,white,Stroke.applyC,g,ite_mul,h.bdp i hi,hi,add_mul,sum_add_distrib]

def trunk (n : ℕ) (p : Reel) : ℕ → Wood
  | 0 => white
  | t+1 =>
    let u := p.atBeat t
    knot n (leafC u) (knot n (leafM u) (trunk n p t))

lemma graft_trunk (n : ℕ) (p : Reel) (h : p.Sound n) (t : ℕ) (ht : t≤p.beats) (v : Line) :
    ∀ i<n, graft n (trunk n p t) v i=p.reach v t i := by
  induction t with
  | zero => exact graft_white n v
  | succ t ih =>
    let u := p.atBeat t
    let g := graft n (leafM u) (graft n (trunk n p t) v)
    have hh := h t (by omega)
    have hg (i : ℕ) (hi : i<n) : g i=u.applyM (p.reach v t) i := by
      unfold g; rw [graft_leafM hh _ _ hi]; unfold Stroke.applyM
      rw [ih (by omega) _ (hh.bdix i hi)]
    intro i hi
    rw [trunk]
    rw [graft_knot,graft_knot,graft_leafC hh _ i hi]
    change u.applyC g i=u.applyC _ i
    unfold Stroke.applyC; rw [hg i hi,hg _ (hh.bdp i hi)]

def forest (r : Axes) (l : ℕ) (p : ℕ → Reel) (x : Line) : ℕ → Line
  | 0 => x
  | t+1 =>
    let M := canopy r (fun i => leafM ((p i).atBeat t)) l
    let C := canopy r (fun i => leafC ((p i).atBeat t)) l
    graft (extent r l) C (graft (extent r l) M (forest r l p x t))

lemma graft_forest (r : Axes) (l : ℕ) (p : ℕ → Reel) (h : Splits r l)
    (x : Line) (t : ℕ) :
    ∀ i<extent r l, graft (extent r l) (canopy r (fun j => trunk (r j) (p j) t) l) x i =
      forest r l p x t i := by
  induction t with
  | zero =>
    intro i hi
    change graft _ (canopy _ (fun _ => white) _) _ i = _
    rw [show graft _ (canopy _ (fun _ => white) _) _ i = graft (extent r l) white x i from
        sum_congr rfl fun j hj => by rw [canopy_white r l h i hi j (mem_range.mp hj)],
      graft_white _ _ i hi]
    rfl
  | succ t ih =>
    intro i _
    simp only [forest,trunk]
    rw [← canopy_knot _ _ _ _ h,← canopy_knot _ _ _ _ h,graft_knot,graft_knot]
    rw [graft_congr _ _ _ _ ih]

lemma trunk_creates {n : ℕ} {X : Wood} {p : Reel} (h : p.Sound n)
    (g : Creates p n (frame n X)) :
    ∀ i<n, ∀ j<n, trunk n p p.beats i j=X i j := by
  intro i hi j hj
  let v : Line := fun s => if s=j then 1 else 0
  have hh := graft_trunk n p h p.beats le_rfl v i hi
  have hg := congr_fun ((g v).trans (front_graft n X v).symm) (⟨i,hi⟩ : Fin n)
  change p.reach v p.beats i = graft n X v i at hg
  have ev (A : Wood) : graft n A v i=A i j := by simp [v,graft,mul_ite,hj]
  exact ((ev _).symm.trans hh).trans (hg.trans (ev X))

lemma canopy_congr (r : Axes) (l : ℕ) (h : Splits r l)
    (X Y : ℕ →Wood) (g : ∀ j<l, ∀ a<r j, ∀ b<r j, X j a b=Y j a b) :
    ∀ i<extent r l, ∀ j<extent r l,
      canopy r X l i j=canopy r Y l i j := by
  induction l with
  | zero => intros; rfl
  | succ l ih =>
    intro i hi k hk
    simp only [canopy]; rw [ih (h.cut (by omega)) (fun j hj => g j (by omega)) _ (h.div_lt hi) _
      (h.div_lt hk),g l (by omega) _ (h.mod_lt i) _ (h.mod_lt k)]

theorem forest_completes (r : Axes) (l : ℕ) (p : ℕ → Reel) (h : Splits r l) (b : ℕ)
    (hs : ∀ j<l, (p j).Sound (r j)) (hb : ∀ j<l, (p j).beats=b)
    (X : ℕ → Wood) (hx : ∀ j<l, Creates (p j) (r j) (frame (r j) (X j)))
    (x : Line) (i : ℕ) (hi : i<extent r l) :
    forest r l p x b i = graft (extent r l) (canopy r X l) x i := by
  rw [← graft_forest r l p h x b i hi]
  have hh (j : ℕ) (hj : j<l) :
      ∀ a<r j, ∀ c<r j, trunk (r j) (p j) b a c=X j a c := by
    rw [← hb j hj]; exact trunk_creates (hs j hj) (hx j hj)
  refine sum_congr rfl ?_
  intro c hc
  rw [canopy_congr r l h _ X hh i hi c (mem_range.mp hc)]

end Grove
end
end PowerSaving

end OAI
