import OAI.Computability.FourierTransform.ColumnAddresses

namespace OAI

/-! Using a finite certificate. Amplified role arrays with leftover bits. -/
namespace PowerSaving.RAM
open Ty Binary Finset
noncomputable section

abbrev Beach (α ρ : Type*) (r f : ℕ) := ρ × Grid α r f
abbrev Grain (α ρ : Type*) (r f : ℕ) := Beach α ρ r f → ℂ

def fleet {α ρ : Type*} (X : Layout α) (R : Layout ρ) (r f : ℕ) :=
  R.pair (book X r f)

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

def ferry (r f : ℕ) (u : Move α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => u.go f (fun i j => v (i,x.2.1,j)) x.1 x.2.2

/-- Total certificate action. -/
def coastline (r f : ℕ) (p : PWord α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => walk f p (fun i j => v (i,x.2.1,j)) x.1 x.2.2

theorem coast_cons (r f : ℕ) (u : Move α ρ) (p : PWord α ρ) (v : Grain α ρ r f) :
    coastline r f (u::p) v = coastline r f p (ferry r f u v) := rfl

end

universe U V
variable {ι : Type U}

/-- Gear and ready input full role tape. -/
structure Rig {α ρ : Type*} (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s)
    (cl : Paint) (X : Layout α) (R : Layout ρ) (r : ℕ) (v : ∀ i, Grain α ρ r (f i)) : Prop where
  gear : Gear m B f s x
  imag : Has m B s sc x fun _ => Complex.I
  items : Has m B s (a (c cl)) x fun i => (fleet X R r (f i)).tape (v i)

namespace Rig
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
variable (h : Rig m B f s x cl X R r v)
include h

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma gather {κ : Type V} (j : κ → ι) (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    Rig m (fun k => B (j k)) (fun k => f (j k)) t y cl X R r (fun k => v (j k)) :=
  ⟨h.gear.descend j y g,
    g.then_do (h.imag.reindex j), g.then_do (h.items.reindex j)⟩

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma large : Small B fun i => (fleet X R r (f i)).n :=
  (Small.const B R.n).mul (h.gear.grid_small X r)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma size : Knows m B s x fun i => (fleet X R r (f i)).n :=
  (Can.wc R.n).times (h.gear.grid_size X r) (Small.const B R.n) (h.gear.grid_small X r)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma addrs (u : ∀ i, Beach α ρ r (f i))
    (hg : Knows m B s x fun i => (fleet X R r (f i)).loc (u i)) :
    Knows m B s x (fun i => R.loc (u i).1) ∧
      Knows m B s x (fun i => (book X r (f i)).loc (u i).2) :=
  ⟨Can.addr_high (u:=u) (L:=fun _ => R) (R:=fun i => book X r (f i)) hg
    (h.gear.grid_size X r) h.large,
   Can.addr_low (u:=u) (L:=fun _ => R) (R:=fun i => book X r (f i)) hg
    (h.gear.grid_size X r) h.large⟩

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma read (u : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => R.loc (u i).1)
    (hb : Knows m B s x fun i => (book X r (f i)).loc (u i).2) :
    Has m B s (c cl) x (fun i => v i (u i)) :=
  Can.fetch (t:=c cl) (L:=fun i => fleet X R r (f i)) (v:=v) (i:=u)
    h.items
    (Can.addr_join (L:=fun _ => R) (R:=fun i => book X r (f i)) (u:=u) ha hb
      (h.gear.grid_size X r) (Small.const B R.n) (h.gear.grid_small X r))

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma chart (v : ∀ i, Grain α ρ r (f i))
    (g : Has m (fun i : Σ i, Beach α ρ r (f i) => B i.1) (p s w) (c cl)
      (fun d => (x d.1,(fleet X R r (f d.1)).loc d.2)) (fun d => v d.1 d.2)) :
    Can m B s (a (c cl)) x (fun i => (fleet X R r (f i)).tape (v i))
      (fun i => (fleet X R r (f i)).n) := by
  have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
    (L:=fun i => fleet X R r (f i)) (v:=v) h.size g h.large
  simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using ht

lemma ferry_point (M : Matrix ρ ρ ℚ) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.localM M) (v i) (q i) := by
  obtain ⟨hl,hk⟩ := h.addrs q g
  -- fixed number of roles; can load each in each iteration
  let z (j : ρ) i := (M (q i).1 j : ℂ) * v i (j,(q i).2)
  change Can m B s (c cl) x (fun i => ∑ j, z j i) _
  apply Can.sum_cconst
  intro j
  have hx : Has m B s sc x (fun i => (M (q i).1 j : ℂ)) := by
    apply Can.cases_code (q:=fun i => (q i).1) R hl
    intro l
    convert (Can.rat (B:=fun i : {i // (q i).1=l} => B i.1) (s:=s)
      (x:=fun i => x i.1) (m:=m) (W:=fun _ => 0) (M l j)) using 1
    funext i; rw [i.2]
  exact hx.mul (h.read (fun i => (j,(q i).2)) (Can.wc (R.loc j)) hk)

lemma ferry_shift (l : ρ) (z : Space α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.shift l z) (v i) (q i) := by
  obtain ⟨hl,hk⟩ := h.addrs q g
  have hb := h.read q hl hk
  let t i : Beach α ρ r (f i) := ((q i).1,(q i).2.1,fun j => (q i).2.2 j+z)
  have hh := h.read t hl (h.gear.shifted X r z _ hk)
  apply Can.cases_code (q:=fun i => (q i).1) R hl
  intro p
  by_cases he : p=l
  · refine (hh.reindex (fun i : {i // (q i).1=p} => i.1)).cong (fun _ => rfl)
      (fun i => ?_)
    simp [t,ferry,Move.go,roleAct,i.2,he,act_shift]
  · refine (hb.reindex (fun i : {i // (q i).1=p} => i.1)).cong (fun _ => rfl)
      (fun i => ?_)
    simp [ferry,Move.go,roleAct,i.2,he]
    exact congr_arg (fun p => v i.val (p,(q i.val).2)) i.2

lemma point_cost (M : Matrix ρ ρ ℚ) :
    Can m B s (a (c cl)) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.localM M) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  have hg := h.gather (fun d : S => d.1)
    (fun d => ((x d.1, (fleet X R r (f d.1)).loc d.2):T (p s w))) (t:=p s w) Can.first
  exact hg.ferry_point M (fun d => d.2) Can.second

lemma shift_cost (l : ρ) (z : Space α) :
    Can m B s (a (c cl)) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.shift l z) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  have hg := h.gather (fun d : S => d.1)
    (fun d => ((x d.1, (fleet X R r (f d.1)).loc d.2):T (p s w))) (t:=p s w) Can.first
  exact hg.ferry_shift l z (fun d => d.2) Can.second

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
/-- Fixed scalar matrices of C etc. -/
lemma little (i j : F) :
    Has m B s sc x fun _ => littleC i j := by
  have h2 : Has m B s sc x (fun _ => (2:ℂ)) := by
    simpa using Can.cNat (m:=m) (B:=B) (W:=fun _ => 0) (s:=s) (x:=x) 2
  have hh := h2.inv (by simp)
  unfold littleC ca cb
  split
  · simp only [div_eq_mul_inv]; exact (Can.one.add h.imag).mul hh
  · simp only [div_eq_mul_inv]; exact (Can.one.sub h.imag).mul hh

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma leftOvers (a b : Bits r) :
    Has m B s sc x fun _ => kernel (Fin r) a b :=
  Can.prod_cconst (v:=fun i _ => littleC (a i) (b i)) (fun _ => h.little _ _)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
/-- r remaining bits before main work. -/
lemma dots_cost :
    Can m B s (a (c cl)) x
      (fun i => (fleet X R r (f i)).tape (fun d =>
        chords r (f i) (fun j => v i (d.1,j)) d.2))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  let env (d : S) : T (p s w) := (x d.1,(fleet X R r (f d.1)).loc d.2)
  let hc := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
  obtain ⟨ha,hb⟩ := hc.addrs (fun d => d.2) Can.second
  obtain ⟨hl,hk⟩ := hc.gear.grid_fetch X r (v:=fun d => d.2.2) hb
  let B1 (d:S) := B d.1
  change Can m B1 (p s w) (c cl) env
    (fun d => ∑ j, kernel (Fin r) d.2.2.1 j * v d.1 (d.2.1,j,d.2.2.2)) _
  apply Can.sum_cconst
  intro j
  let u (d : S) : Beach α ρ r (f d.1) := (d.2.1,j,d.2.2.2)
  have hv := hc.read u ha
    (hc.gear.grid_combine X r (v:=fun d => (u d).2)
      (Can.wc ((bits r).loc j)) hk)
  have he : Has m B1 (p s w) sc env
      (fun d => kernel (Fin r) d.2.2.1 j) := by
    apply Can.cases_code (q:=fun d => d.2.2.1) (bits r) hl
    intro l
    exact ((hc.leftOvers l j).reindex (fun d : {d:S // d.2.2.1=l} => d.1)).cong
      (fun _ => rfl) (fun i => by rw [i.2])
  exact he.mul hv

end Rig
end
end PowerSaving.RAM

end OAI
