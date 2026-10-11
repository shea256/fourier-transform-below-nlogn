import OAI.Computability.FourierTransform.AddressTables

namespace OAI

/-! Constant (i.e. independent of f) work for transposed-column addresses. The number
of bits per COLUMN is fixed. Groups of f bits have prepared powers and XOR table. -/
namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section

universe U V
variable {ι : Type U}

/-- "Ready", i.e. can be computed in constant work, not free. -/
abbrev Has (m : Bool) (B : ι → ℕ) (s t : Ty) (x : ι → T s) (y : ι → T t) : Prop :=
  Can m B s t x y (fun _ => 0)
abbrev Knows (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (y : ι → ℕ) : Prop :=
  Has m B s w x y

/-- Particular indexing programs are proved uniformly over all f through this *finite*
  syntax interface. -/
structure Gear (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s) : Prop where
  power : Knows m B s x (fun i => 2^f i)
  given : Knows m B s x f
  table : Has m B s (a w) x (fun i => xorTab (f i))
  bound : Small B fun i => 2^f i

namespace Gear
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
variable (g : Gear m B f s x)
include g

lemma descend {κ : Type V} (j : κ → ι) (y : κ → T t)
    (h : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    Gear m (fun k => B (j k)) (fun k => f (j k)) t y :=
  ⟨h.then_do (g.power.reindex j),h.then_do (g.given.reindex j),
    h.then_do (g.table.reindex j), g.bound.reindex j⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

-- size of fixed body (layout on α is fixed)
omit [Fintype α] [DecidableEq α] in
lemma body_size (X : Layout α) :
    Knows m B s x (fun i => (bodyOrder X (f i)).n) :=
  g.power.wpow_fixed X.n g.bound
omit [Fintype α] [DecidableEq α] in
lemma body_small (X : Layout α) :
    Small B fun i => (bodyOrder X (f i)).n :=
  g.bound.pow X.n

omit [Fintype α] [DecidableEq α] in
lemma grid_size (X : Layout α) (r : ℕ) :
    Knows m B s x (fun i => (book X r (f i)).n) :=
  Can.times (Can.wc (2^r)) (g.body_size X) (Small.const ..) (g.body_small X)

omit [Fintype α] [DecidableEq α] in
lemma grid_small (X : Layout α) (r : ℕ) :
    Small B fun i => (book X r (f i)).n :=
  (Small.const B (2^r)).mul (g.body_small X)

omit [Fintype α] [DecidableEq α] in
lemma body_get (X : Layout α) (v : ∀ i, Sky α (f i)) (j : α)
    (h : Knows m B s x fun i => (bodyOrder X (f i)).loc (v i)) :
    Knows m B s x (fun i => (bits (f i)).loc (fun l => v i l j)) := by
  have hb := h.dvdW (g.power.wpow_fixed (X.loc j) g.bound)
    (Small.loc (x:=v) (L:=fun i => bodyOrder X (f i)) (g.body_small X))
  have hu : Small B (fun i => (bodyOrder X (f i)).loc (v i) / (2^f i)^X.loc j) :=
    (Small.loc (x:=v) (L:=fun i => bodyOrder X (f i)) (g.body_small X)).div
  refine (hb.modW g.power hu).cong (fun _ => rfl) ?_
  intro i
  exact Layout.digits_entry X (bits (f i)) (rows α _ (v i)) j

omit [DecidableEq α] in
lemma body_set (X : Layout α) (v : ∀ i, Sky α (f i))
    (h : ∀ j : α, Knows m B s x fun i => (bits (f i)).loc (fun l => v i l j)) :
    Knows m B s x (fun i => (bodyOrder X (f i)).loc (v i)) := by
  have hf (j : α) : Small B fun i => (bits (f i)).loc (fun l => v i l j) :=
    Small.loc (x:=fun i l => v i l j) (L:=fun i => bits (f i)) g.bound
  have hh := Can.sum_wconst (fun j => (h j).times
    (g.power.wpow_fixed (X.loc j) g.bound)
    (hf j) (g.bound.pow (X.loc j))) (fun j => (hf j).mul (g.bound.pow _))
  refine hh.cong (fun _ => rfl) ?_
  intro i
  exact (Layout.digits_code X (bits (f i)) (fun j l => v i l j)).symm

variable (X : Layout α) (r : ℕ)

omit [Fintype α] [DecidableEq α] in
lemma grid_fetch {v : ∀ i, Grid α r (f i)}
    (h : Knows m B s x fun i => (book X r (f i)).loc (v i)) :
    Knows m B s x (fun i => (bits r).loc (v i).1) ∧
    Knows m B s x (fun i => (bodyOrder X (f i)).loc (v i).2) :=
  ⟨Can.addr_high (L:=fun _ => bits r) (R:=fun i => bodyOrder X (f i)) (u:=v)
      h (g.body_size X) (g.grid_small X r),
   Can.addr_low (L:=fun _ => bits r) (R:=fun i => bodyOrder X (f i)) (u:=v)
      h (g.body_size X) (g.grid_small X r)⟩

omit [Fintype α] [DecidableEq α] in
lemma grid_combine {v : ∀ i, Grid α r (f i)}
    (a : Knows m B s x (fun i => (bits r).loc (v i).1))
    (b : Knows m B s x (fun i => (bodyOrder X (f i)).loc (v i).2)) :
    Knows m B s x (fun i => (book X r (f i)).loc (v i)) :=
  Can.addr_join (L:=fun _ => bits r) (R:=fun i => bodyOrder X (f i)) (u:=v)
    a b (g.body_size X) (Small.const B (2^r)) (g.body_small X)

lemma addr_xor (v : ∀ i, Bits (f i) × Bits (f i))
    (h : Knows m B s x (fun i => (bits (f i)).loc (v i).1))
    (k : Knows m B s x (fun i => (bits (f i)).loc (v i).2)) :
    Knows m B s x (fun i => (bits (f i)).loc ((v i).1+(v i).2)) :=
  Can.xor_lookup v g.table h k g.power g.bound

omit [DecidableEq α] in
/-- Address translated by z (across f columns). -/
lemma shifted (z : Space α) (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    Knows m B s x (fun i => (book X r (f i)).loc ((v i).1,
      fun j => (v i).2 j + z)) := by
  obtain ⟨hg, hh⟩ := g.grid_fetch X r (v:=v) h
  let K (i : ι) : Grid α r (f i) := ((v i).1, fun j => (v i).2 j + z)
  apply g.grid_combine X r (v:=K) hg (g.body_set X (fun i => (K i).2) _)
  intro j
  have hv := g.body_get X (fun i => (v i).2) j hh
  rcases bit_cases (z j) with hj|hj
  · refine hv.cong (fun _ => rfl) (fun i => ?_)
    simp [K,hj]
  · let q i : Bits (f i) × Bits (f i) := (fun l => (v i).2 l j, fun _ => 1)
    have hf : Knows m B s x (fun i => (bits (f i)).loc (q i).2) :=
      (g.power.minus (Can.wc 1) g.bound).cong (fun _ => rfl) (fun i => by
        change 2^f i-1=(bits _).loc (fun _ => 1)
        rw [← bits_lit]
        simp)
    refine (g.addr_xor q hv hf).cong (fun _ => rfl) (fun i => ?_)
    apply congr_arg (bits (f i)).loc
    ext k; simp [q,K,hj]

/-- Program can go back and forth between grid and (fiber,within-fiber). -/
lemma from_grid (j : α) (X' : Layout (Minus j)) (z : Space α)
    (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    let u i := peelBook j z r (f i) (v i)
    Knows m B s x (fun i => (book X' r (f i)).loc (u i).1) ∧
    Knows m B s x (fun i => (bits (f i)).loc (u i).2) := by
  intro u
  obtain ⟨hg, hh⟩ := g.grid_fetch X r (v:=v) h
  have ht (l : α) := g.body_get X (fun i => (v i).2) l hh
  refine ⟨g.grid_combine X' r (v:=fun i => (u i).1) hg
    (g.body_set X' (fun i => (u i).1.2) ?_), ht j⟩
  intro l
  rcases bit_cases (z l.val) with hl|hl
  · refine (ht l.val).cong (fun _ => rfl) (fun i => ?_)
    simp [u,peelBook,skySplit,peel,hl]
  · let q (i : ι) : Bits (f i) × Bits (f i) :=
      (fun k => (v i).2 k l.val, fun k => (v i).2 k j)
    refine (g.addr_xor q (ht l.val) (ht j)).cong (fun _ => rfl) (fun i => ?_)
    apply congr_arg (bits (f i)).loc
    ext k
    simp [u,q,peelBook,skySplit,peel,hl]

lemma to_grid (j : α) (X' : Layout (Minus j)) (z : Space α)
    (u : ∀ i, Grid (Minus j) r (f i) × Bits (f i))
    (h : Knows m B s x (fun i => (book X' r (f i)).loc (u i).1))
    (k : Knows m B s x (fun i => (bits (f i)).loc (u i).2)) :
    let v i := (peelBook j z r (f i)).symm (u i)
    Knows m B s x (fun i => (book X r (f i)).loc (v i)) := by
  intro v
  obtain ⟨hg, hh⟩ := g.grid_fetch X' r (v:=fun i => (u i).1) h
  refine g.grid_combine X r (v:=v) hg (g.body_set X (fun i => (v i).2) ?_)
  intro l
  by_cases hl : l=j
  · subst l; simpa [v,peelBook,skySplit,peel]
  · let t : Minus j := ⟨l,hl⟩
    have ht := g.body_get X' (fun i => (u i).1.2) t hh
    rcases bit_cases (z l) with he|he
    · refine ht.cong (fun _ => rfl) (fun i => ?_)
      simp [v,t,peelBook,skySplit,peel,hl,he]
    · let q (i : ι) : Bits (f i) × Bits (f i) :=
        (fun k => (u i).1.2 k t, (u i).2)
      refine (g.addr_xor q ht k).cong (fun _ => rfl) (fun i => ?_)
      apply congr_arg (bits (f i)).loc; ext b
      simp [v,t,q,peelBook,skySplit,peel,hl,he]

end Gear
end
end PowerSaving.RAM

end OAI
