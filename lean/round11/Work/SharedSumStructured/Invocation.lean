import Work.SharedSumStructured.Labels

/-!
# (key: shared-sum-structured) One invocation of a two-stage network with an ARBITRARY helper circuit

`Circuit H T Sl C` is the abstract certificate of one invocation:

* `T`  inputs (triples) with unit vectors `tv t`; the banks are `x_t` (label `<t>`, then full)
        and `y_t` (label 0, then `t^⊥`);
* `Sl` helper slots: LIVE, DIRTY roles (arbitrary contents, restored at the end);
* `C`  scratch copies ("retained totals" / centres): zero on entry;
* matrices `V` (slots += inputs), `L`/`Linv` (the addition circuit on the slots), `Jp` (pieces:
  targets += slots), `Cc` (copies += slots), `Jr` (targets += copies) with
  `(Jr * Cc + Jp) * L * V = 1`;
* single-factor labels of the slots at the three moments they are read (`φ4`: loading,
  `φ5`: after the circuit, `φ7`: as a piece), with the climbs between them, and the gate
  conditions (equal labels wherever a matrix entry is nonzero);
* `circ`: the circuit itself as a path from `φ4` to `φ5`, for every frame map (so that it can be
  lifted to both stages), for `L` and for the transposed inverse.

`invocation_fwd` / `invocation_bwd` are the "dirty helper" words
`y -= J L s;  s += V x;  L;  copies;  y += J(..);  L⁻¹;  s -= V x` and its transposed inverse:
`y += x` resp. `x -= y` on the banks, slots restored, whenever the copies start at zero.
Every helper slot costs exactly its nominal dimension (`h`), every copy the dimension of its
label, once.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace SS
open Binary Matrix Finset RAM
noncomputable section

/-! ## rectangular action of a rational matrix -/
section Ap
variable {A B C : Type*} [Fintype B] [Fintype C]

def ap (M : Matrix A B ℚ) (u : B → ℂ) : A → ℂ := fun i => ∑ j, (M i j : ℂ) * u j

lemma ap_add (M : Matrix A B ℚ) (u w : B → ℂ) : ap M (u + w) = ap M u + ap M w := by
  funext i; simp [ap, mul_add, sum_add_distrib]
lemma ap_neg (M : Matrix A B ℚ) (u : B → ℂ) : ap M (-u) = - ap M u := by
  funext i; simp [ap]
lemma ap_zero (M : Matrix A B ℚ) : ap M (0 : B → ℂ) = 0 := by
  funext i; simp [ap]
lemma ap_madd (M N : Matrix A B ℚ) (u : B → ℂ) : ap (M + N) u = ap M u + ap N u := by
  funext i; simp [ap, add_mul, sum_add_distrib]
lemma ap_mneg (M : Matrix A B ℚ) (u : B → ℂ) : ap (-M) u = - ap M u := by
  funext i; simp [ap]
lemma ap_mul (M : Matrix A B ℚ) (N : Matrix B C ℚ) (u : C → ℂ) :
    ap (M * N) u = ap M (ap N u) := by
  funext i
  simp only [ap, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
lemma ap_one [DecidableEq B] (u : B → ℂ) : ap (1 : Matrix B B ℚ) u = u := by
  funext i
  simp only [ap, Matrix.one_apply]
  exact sum_ind_right i u
lemma actPoint_eq_ap [DecidableEq B] (M : Matrix B B ℚ) : actPoint M = ap M := rfl
lemma ne_of_negT (M : Matrix A B ℚ) {a : A} {b : B} (h : (-Mᵀ) b a ≠ 0) : M a b ≠ 0 :=
  fun h0 => h (by simp [h0])

end Ap

/-! ## a block shear on an arbitrary role type -/
section Shear
variable {ρ A B : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype A] [Fintype B]

/-- `role (ia a) += ∑_b M a b * role (ib b)`. -/
def shearM (ia : A → ρ) (ib : B → ρ) (M : Matrix A B ℚ) : Matrix ρ ρ ℚ :=
  fun i j => (if i = j then 1 else 0) + ∑ a, ∑ b, if i = ia a ∧ j = ib b then M a b else 0

def addBlk (ia : A → ρ) (u : A → ℂ) (z : ρ → ℂ) : ρ → ℂ :=
  fun i => z i + ∑ a, if i = ia a then u a else 0

lemma actPoint_shearM (ia : A → ρ) (ib : B → ρ) (hib : Function.Injective ib)
    (M : Matrix A B ℚ) (z : ρ → ℂ) :
    actPoint (shearM ia ib M) z = addBlk ia (ap M (z ∘ ib)) z := by
  funext i
  unfold actPoint shearM addBlk
  simp only [Rat.cast_add, add_mul, sum_add_distrib]
  rw [sum_ind_right i z]
  congr 1
  simp only [Rat.cast_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : i = ia a
  · subst h
    simp only [true_and, if_true, ap, Function.comp_apply]
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    rw [sum_eq_single (ib b)]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · simp [h]

lemma shearM_offdiag {ia : A → ρ} {ib : B → ρ} {M : Matrix A B ℚ} {i j : ρ} (hij : i ≠ j)
    (h : shearM ia ib M i j ≠ 0) : ∃ a b, i = ia a ∧ j = ib b ∧ M a b ≠ 0 := by
  unfold shearM at h
  simp only [hij, if_false, zero_add] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  by_cases hc : i = ia a ∧ j = ib b
  · rw [if_pos hc] at hb
    exact ⟨a, b, hc.1, hc.2, hb⟩
  · rw [if_neg hc] at hb
    exact absurd rfl hb

lemma addBlk_same (ia : A → ρ) (hia : Function.Injective ia) (u : A → ℂ) (z : ρ → ℂ) :
    addBlk ia u z ∘ ia = z ∘ ia + u := by
  funext a
  simp only [Function.comp_apply, addBlk, Pi.add_apply]
  congr 1
  rw [sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg (fun h => hb (hia h).symm)]
  · simp

lemma addBlk_other (ia : A → ρ) (ib : B → ρ) (hd : ∀ a b, ib b ≠ ia a) (u : A → ℂ)
    (z : ρ → ℂ) : addBlk ia u z ∘ ib = z ∘ ib := by
  funext b
  simp [addBlk, hd]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- a shear gate is legal when every nonzero entry joins two roles with the same frame. -/
lemma gate_shear {s : ρ → Fr α} (ia : A → ρ) (ib : B → ρ) (hib : Function.Injective ib)
    (M : Matrix A B ℚ) (cond : ∀ a b, M a b ≠ 0 → s (ia a) = s (ib b)) :
    GPath s s (fun z => addBlk ia (ap M (z ∘ ib)) z) 0 := by
  have h := GPath.gate (s := s) (shearM ia ib M) (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · obtain ⟨a, b, rfl, rfl, hM⟩ := shearM_offdiag e hij
      rw [cond a b hM])
  exact h.cast (funext fun z => actPoint_shearM ia ib hib M z) rfl

end Shear

/-! ## the roles of one invocation -/
section Box
variable (T Sl C : Type)

/-- banks `x`, `y`; helper slots; scratch copies. -/
abbrev Box := (T ⊕ T) ⊕ (Sl ⊕ C)

variable {T Sl C}

def bX (t : T) : Box T Sl C := .inl (.inl t)
def bY (t : T) : Box T Sl C := .inl (.inr t)
def bS (q : Sl) : Box T Sl C := .inr (.inl q)
def bC (c : C) : Box T Sl C := .inr (.inr c)

lemma bX_inj : Function.Injective (bX : T → Box T Sl C) := fun _ _ h => by
  simpa [bX] using h
lemma bY_inj : Function.Injective (bY : T → Box T Sl C) := fun _ _ h => by
  simpa [bY] using h
lemma bS_inj : Function.Injective (bS : Sl → Box T Sl C) := fun _ _ h => by
  simpa [bS] using h
lemma bC_inj : Function.Injective (bC : C → Box T Sl C) := fun _ _ h => by
  simpa [bC] using h

def stamp {β : Type*} (x y : T → β) (s : Sl → β) (c : C → β) : Box T Sl C → β :=
  Sum.elim (Sum.elim x y) (Sum.elim s c)

/-- apply a map to the slot block only. -/
def onS (φ : (Sl → ℂ) → (Sl → ℂ)) (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  stamp (z ∘ bX) (z ∘ bY) (φ (z ∘ bS)) (z ∘ bC)

@[simp] lemma onS_X (φ : (Sl → ℂ) → (Sl → ℂ)) (z : Box T Sl C → ℂ) : onS φ z ∘ bX = z ∘ bX := rfl
@[simp] lemma onS_Y (φ : (Sl → ℂ) → (Sl → ℂ)) (z : Box T Sl C → ℂ) : onS φ z ∘ bY = z ∘ bY := rfl
@[simp] lemma onS_S (φ : (Sl → ℂ) → (Sl → ℂ)) (z : Box T Sl C → ℂ) : onS φ z ∘ bS = φ (z ∘ bS) := rfl
@[simp] lemma onS_C (φ : (Sl → ℂ) → (Sl → ℂ)) (z : Box T Sl C → ℂ) : onS φ z ∘ bC = z ∘ bC := rfl

variable [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

@[simp] lemma aX_X (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bX u z ∘ bX = z ∘ bX + u :=
  addBlk_same bX bX_inj u z
@[simp] lemma aX_Y (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bX u z ∘ bY = z ∘ bY :=
  addBlk_other bX bY (fun a b h => by simp [bX, bY] at h) u z
@[simp] lemma aX_S (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bX u z ∘ bS = z ∘ bS :=
  addBlk_other bX bS (fun a b h => by simp [bX, bS] at h) u z
@[simp] lemma aX_C (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bX u z ∘ bC = z ∘ bC :=
  addBlk_other bX bC (fun a b h => by simp [bX, bC] at h) u z
@[simp] lemma aY_X (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bY u z ∘ bX = z ∘ bX :=
  addBlk_other bY bX (fun a b h => by simp [bX, bY] at h) u z
@[simp] lemma aY_Y (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bY u z ∘ bY = z ∘ bY + u :=
  addBlk_same bY bY_inj u z
@[simp] lemma aY_S (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bY u z ∘ bS = z ∘ bS :=
  addBlk_other bY bS (fun a b h => by simp [bY, bS] at h) u z
@[simp] lemma aY_C (u : T → ℂ) (z : Box T Sl C → ℂ) : addBlk bY u z ∘ bC = z ∘ bC :=
  addBlk_other bY bC (fun a b h => by simp [bY, bC] at h) u z
@[simp] lemma aS_X (u : Sl → ℂ) (z : Box T Sl C → ℂ) : addBlk bS u z ∘ bX = z ∘ bX :=
  addBlk_other bS bX (fun a b h => by simp [bX, bS] at h) u z
@[simp] lemma aS_Y (u : Sl → ℂ) (z : Box T Sl C → ℂ) : addBlk bS u z ∘ bY = z ∘ bY :=
  addBlk_other bS bY (fun a b h => by simp [bY, bS] at h) u z
@[simp] lemma aS_S (u : Sl → ℂ) (z : Box T Sl C → ℂ) : addBlk bS u z ∘ bS = z ∘ bS + u :=
  addBlk_same bS bS_inj u z
@[simp] lemma aS_C (u : Sl → ℂ) (z : Box T Sl C → ℂ) : addBlk bS u z ∘ bC = z ∘ bC :=
  addBlk_other bS bC (fun a b h => by simp [bS, bC] at h) u z
@[simp] lemma aC_X (u : C → ℂ) (z : Box T Sl C → ℂ) : addBlk bC u z ∘ bX = z ∘ bX :=
  addBlk_other bC bX (fun a b h => by simp [bX, bC] at h) u z
@[simp] lemma aC_Y (u : C → ℂ) (z : Box T Sl C → ℂ) : addBlk bC u z ∘ bY = z ∘ bY :=
  addBlk_other bC bY (fun a b h => by simp [bY, bC] at h) u z
@[simp] lemma aC_S (u : C → ℂ) (z : Box T Sl C → ℂ) : addBlk bC u z ∘ bS = z ∘ bS :=
  addBlk_other bC bS (fun a b h => by simp [bS, bC] at h) u z
@[simp] lemma aC_C (u : C → ℂ) (z : Box T Sl C → ℂ) : addBlk bC u z ∘ bC = z ∘ bC + u :=
  addBlk_same bC bC_inj u z

/-- the slots as an embedded sub-network. -/
def eS : Sl ↪ Box T Sl C := ⟨bS, bS_inj⟩

lemma notcov_X (t : T) : (bX t : Box T Sl C) ∉ covered (eS (T:=T) (Sl:=Sl) (C:=C)) := by
  rw [cover_iff]; rintro ⟨j, hj⟩; simp [eS, bS, bX] at hj
lemma notcov_Y (t : T) : (bY t : Box T Sl C) ∉ covered (eS (T:=T) (Sl:=Sl) (C:=C)) := by
  rw [cover_iff]; rintro ⟨j, hj⟩; simp [eS, bS, bY] at hj
lemma notcov_C (c : C) : (bC c : Box T Sl C) ∉ covered (eS (T:=T) (Sl:=Sl) (C:=C)) := by
  rw [cover_iff]; rintro ⟨j, hj⟩; simp [eS, bS, bC] at hj

lemma wide_onS (M : Matrix Sl Sl ℚ) (z : Box T Sl C → ℂ) :
    actPoint (wide eS M) z = onS (actPoint M) z := by
  funext i
  rcases i with ((t|t)|(q|c))
  · exact wide_out eS M z (notcov_X t)
  · exact wide_out eS M z (notcov_Y t)
  · exact wide_in eS M q z
  · exact wide_out eS M z (notcov_C c)

lemma wide_offdiag (M : Matrix Sl Sl ℚ) {i j : Box T Sl C} (hij : i ≠ j)
    (h : wide eS M i j ≠ 0) : ∃ q q' : Sl, i = bS q ∧ j = bS q' := by
  unfold wide at h
  by_cases h1 : i ∈ covered (eS (T:=T) (Sl:=Sl) (C:=C))
  · by_cases h2 : j ∈ covered (eS (T:=T) (Sl:=Sl) (C:=C))
    · obtain ⟨q, hq⟩ := (cover_iff ..).mp h1
      obtain ⟨q', hq'⟩ := (cover_iff ..).mp h2
      exact ⟨q, q', hq.symm, hq'.symm⟩
    · simp [h1, h2] at h
  · simp [h1, hij] at h

end Box

/-! ## the abstract certificate of one invocation -/

/-- See the file header. -/
structure Circuit (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  tv : T → Space H
  L : Matrix Sl Sl ℚ
  Linv : Matrix Sl Sl ℚ
  V : Matrix Sl T ℚ
  Jp : Matrix T Sl ℚ
  Jr : Matrix T C ℚ
  Cc : Matrix C Sl ℚ
  φ4 : Sl → Lbl H
  φ5 : Sl → Lbl H
  φ7 : Sl → Lbl H
  cen : C → Lbl H
  hLL : L * Linv = 1
  hLL' : Linv * L = 1
  hid : (Jr * Cc + Jp) * L * V = 1
  cx : ∀ t, Climbs (lineL (tv t)) fullL
  cy : ∀ t, Climbs zeroL (perpL (tv t))
  c04 : ∀ q, Climbs zeroL (φ4 q)
  c57 : ∀ q, Climbs (φ5 q) (φ7 q)
  c7F : ∀ q, Climbs (φ7 q) fullL
  cc : ∀ c, Climbs zeroL (cen c)
  sV : ∀ q t, V q t ≠ 0 → φ4 q = lineL (tv t)
  sC : ∀ c q, Cc c q ≠ 0 → cen c = φ5 q
  sJ : ∀ t q, Jp t q ≠ 0 → φ7 q = perpL (tv t)
  circ : ∀ {α : Type} [Fintype α] [DecidableEq α] (Fm : FMap H α),
    GPath (fun q => Fm.lab (φ4 q)) (fun q => Fm.lab (φ5 q)) (actPoint L) 0 ∧
    GPath (fun q => Fm.lab (φ4 q)) (fun q => Fm.lab (φ5 q)) (actPoint Linvᵀ) 0

section Invocation
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- frames of the roles of an invocation, from single-factor labels. -/
def st (Fm : FMap H α) (x y : T → Lbl H) (s : Sl → Lbl H) (c : C → Lbl H) :
    Box T Sl C → Fr α := fun b => Fm.lab (stamp x y s c b)

lemma st_climb (Fm : FMap H α) {x x' y y' : T → Lbl H} {s s' : Sl → Lbl H} {c c' : C → Lbl H}
    (hx : ∀ t, Climbs (x t) (x' t)) (hy : ∀ t, Climbs (y t) (y' t))
    (hs : ∀ q, Climbs (s q) (s' q)) (hc : ∀ k, Climbs (c k) (c' k)) :
    GPath (st Fm x y s c) (st Fm x' y' s' c') id 0 := by
  apply GPath.climb_all
  rintro ((t|t)|(q|k))
  · exact Fm.reach (hx t)
  · exact Fm.reach (hy t)
  · exact Fm.reach (hs q)
  · exact Fm.reach (hc k)

/-- the copies descend from their labels to zero: one loss per unit of nominal dimension. -/
lemma st_descend (Fm : FMap H α) (x y : T → Lbl H) (s : Sl → Lbl H) (c : C → Lbl H)
    (hc : ∀ k, Climbs zeroL (c k)) :
    GPath (st Fm x y s c) (st Fm x y s (fun _ => zeroL)) id (∑ k, (c k).d) := by
  have H := GPath.move_all (st Fm x y s c) (st Fm x y s (fun _ => zeroL))
    (stamp (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun k => (c k).d)) (by
      rintro ((t|t)|(q|k))
      · exact Or.inl ⟨0, Reach.refl _, rfl, rfl⟩
      · exact Or.inl ⟨0, Reach.refl _, rfl, rfl⟩
      · exact Or.inl ⟨0, Reach.refl _, rfl, rfl⟩
      · obtain ⟨n, hr, hd⟩ := Fm.reach (hc k)
        refine Or.inr ⟨n, hr, hd, ?_⟩
        simp only [FMap.lab, zeroL] at hd
        change (c k).d = n
        omega)
  refine H.cast rfl ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [stamp]

lemma st_gate (Fm : FMap H α) {x y : T → Lbl H} {s : Sl → Lbl H} {c : C → Lbl H}
    {A B : Type} [Fintype A] [Fintype B] (ia : A → Box T Sl C) (ib : B → Box T Sl C)
    (hib : Function.Injective ib) (M : Matrix A B ℚ)
    (cond : ∀ a b, M a b ≠ 0 → stamp x y s c (ia a) = stamp x y s c (ib b)) :
    GPath (st Fm x y s c) (st Fm x y s c) (fun z => addBlk ia (ap M (z ∘ ib)) z) 0 :=
  gate_shear ia ib hib M (fun a b h => by simp only [st]; rw [cond a b h])

lemma st_wide (Fm : FMap H α) {x y : T → Lbl H} {s : Sl → Lbl H} {c : C → Lbl H}
    (M : Matrix Sl Sl ℚ) (hs : ∀ q q', s q = s q') :
    GPath (st Fm x y s c) (st Fm x y s c) (onS (actPoint M)) 0 := by
  have h := GPath.gate (s := st Fm x y s c) (wide eS M) (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · obtain ⟨q, q', rfl, rfl⟩ := wide_offdiag M e hij
      change (Fm.lab (s q)).M = (Fm.lab (s q')).M
      rw [hs q q'])
  exact h.cast (funext fun z => wide_onS M z) rfl

variable (K : Circuit H T Sl C)

/-- the circuit phase on the roles of the invocation. -/
lemma st_circ (Fm : FMap H α) (x y : T → Lbl H) (c : C → Lbl H) :
    GPath (st Fm x y K.φ4 c) (st Fm x y K.φ5 c) (onS (actPoint K.L)) 0 ∧
    GPath (st Fm x y K.φ4 c) (st Fm x y K.φ5 c) (onS (actPoint K.Linvᵀ)) 0 := by
  have hout : ∀ (φ : (Sl → ℂ) → (Sl → ℂ)) (z : Box T Sl C → ℂ) (i : Box T Sl C),
      i ∉ covered (eS (T:=T) (Sl:=Sl) (C:=C)) → onS φ z i = z i := by
    intro φ z i hi
    rcases i with ((t|t)|(q|k))
    · rfl
    · rfl
    · exact absurd ((cover_iff ..).mpr ⟨q, rfl⟩) hi
    · rfl
  have he : ∀ i : Box T Sl C, i ∉ covered (eS (T:=T) (Sl:=Sl) (C:=C)) →
      st Fm x y K.φ4 c i = st Fm x y K.φ5 c i := by
    intro i hi
    rcases i with ((t|t)|(q|k))
    · rfl
    · rfl
    · exact absurd ((cover_iff ..).mpr ⟨q, rfl⟩) hi
    · rfl
  exact ⟨GPath.lift eS (K.circ Fm).1 (fun z => rfl) (hout _) he,
    GPath.lift eS (K.circ Fm).2 (fun z => rfl) (hout _) he⟩

/-- scalar map of the forward invocation (all gates, in chronological order). -/
def Circuit.fwd (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  let z1 := addBlk bY (ap (-((K.Jr * K.Cc + K.Jp) * K.L)) (z ∘ bS)) z
  let z2 := addBlk bS (ap K.V (z1 ∘ bX)) z1
  let z3 := onS (actPoint K.L) z2
  let z4 := addBlk bC (ap K.Cc (z3 ∘ bS)) z3
  let z5 := addBlk bY (ap K.Jr (z4 ∘ bC)) z4
  let z6 := addBlk bY (ap K.Jp (z5 ∘ bS)) z5
  let z7 := onS (actPoint K.Linv) z6
  addBlk bS (ap (-K.V) (z7 ∘ bX)) z7

/-- scalar map of the backward invocation (transposed inverse gates, same order). -/
def Circuit.bwd (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  let z1 := addBlk bS (ap (((K.Jr * K.Cc + K.Jp) * K.L)ᵀ) (z ∘ bY)) z
  let z2 := addBlk bX (ap (-K.Vᵀ) (z1 ∘ bS)) z1
  let z3 := onS (actPoint K.Linvᵀ) z2
  let z4 := addBlk bC (ap K.Jrᵀ (z3 ∘ bY)) z3
  let z5 := addBlk bS (ap (-K.Ccᵀ) (z4 ∘ bC)) z4
  let z6 := addBlk bS (ap (-K.Jpᵀ) (z5 ∘ bY)) z5
  let z7 := onS (actPoint K.Lᵀ) z6
  addBlk bX (ap K.Vᵀ (z7 ∘ bS)) z7

/-- **Forward invocation.**  Banks: `x` from its line to the full label, `y` from zero to
`t^⊥`; slots from zero to full; copies from their label DOWN to zero (the only losses). -/
theorem invocation_fwd (Fm : FMap H α) :
    GPath (st Fm (fun t => lineL (K.tv t)) (fun _ => zeroL) (fun _ => zeroL) K.cen)
      (st Fm (fun _ => fullL) (fun t => perpL (K.tv t)) (fun _ => fullL) (fun _ => zeroL))
      K.fwd (∑ k, (K.cen k).d) := by
  -- f0..f3 as one gate: y -= (J L) s, everything at zero
  have g1 := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := fun _ => zeroL) (c := K.cen) (bY : T → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    (-((K.Jr * K.Cc + K.Jp) * K.L)) (fun a b _ => rfl)
  -- slots climb to their loading labels
  have c4 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun t => lineL (K.tv t))
    (y := fun _ => zeroL) (y' := fun _ => zeroL) (s := fun _ => zeroL) (s' := K.φ4)
    (c := K.cen) (c' := K.cen) (fun _ => .refl _) (fun _ => .refl _) K.c04 (fun _ => .refl _)
  have g4 := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := K.φ4) (c := K.cen) (bS : Sl → Box T Sl C) (bX : T → Box T Sl C) bX_inj
    K.V (fun a b h => K.sV a b h)
  have g5 := (st_circ K Fm (fun t => lineL (K.tv t)) (fun _ => zeroL) K.cen).1
  have g6a := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := K.φ5) (c := K.cen) (bC : C → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    K.Cc (fun a b h => K.sC a b h)
  have d6 := st_descend Fm (fun t => lineL (K.tv t)) (fun _ => zeroL) K.φ5 K.cen K.cc
  have g6b := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := K.φ5) (c := fun _ => zeroL) (bY : T → Box T Sl C) (bC : C → Box T Sl C) bC_inj
    K.Jr (fun a b _ => rfl)
  have c7 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun t => lineL (K.tv t))
    (y := fun _ => zeroL) (y' := fun t => perpL (K.tv t)) (s := K.φ5) (s' := K.φ7)
    (c := fun (_ : C) => zeroL) (c' := fun _ => zeroL) (fun _ => .refl _) K.cy K.c57
    (fun _ => .refl _)
  have g7 := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun t => perpL (K.tv t))
    (s := K.φ7) (c := fun _ => zeroL) (bY : T → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    K.Jp (fun a b h => (K.sJ a b h).symm)
  have c8 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun _ => fullL)
    (y := fun t => perpL (K.tv t)) (y' := fun t => perpL (K.tv t)) (s := K.φ7)
    (s' := fun _ => fullL) (c := fun (_ : C) => zeroL) (c' := fun _ => zeroL) K.cx
    (fun _ => .refl _) K.c7F (fun _ => .refl _)
  have g8 := st_wide Fm (x := fun _ => fullL) (y := fun t => perpL (K.tv t))
    (s := fun _ => fullL) (c := fun (_ : C) => zeroL) K.Linv (fun _ _ => rfl)
  have g9 := st_gate Fm (x := fun _ => fullL) (y := fun t => perpL (K.tv t))
    (s := fun _ => fullL) (c := fun _ => zeroL) (bS : Sl → Box T Sl C) (bX : T → Box T Sl C)
    bX_inj (-K.V) (fun a b _ => rfl)
  have tot := ((((((((((g1.trans c4).trans g4).trans g5).trans g6a).trans d6).trans g6b).trans
    c7).trans g7).trans c8).trans g8).trans g9
  exact tot.cast rfl (by omega)

/-- **Backward invocation** (transposed inverse gates on the same labels): the copies start at
zero and CLIMB to their labels, so there is no loss. -/
theorem invocation_bwd (Fm : FMap H α) :
    GPath (st Fm (fun t => lineL (K.tv t)) (fun _ => zeroL) (fun _ => zeroL) (fun _ => zeroL))
      (st Fm (fun _ => fullL) (fun t => perpL (K.tv t)) (fun _ => fullL) K.cen)
      K.bwd 0 := by
  have g1 := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := fun _ => zeroL) (c := fun _ => zeroL) (bS : Sl → Box T Sl C) (bY : T → Box T Sl C)
    bY_inj (((K.Jr * K.Cc + K.Jp) * K.L)ᵀ) (fun a b _ => rfl)
  have c4 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun t => lineL (K.tv t))
    (y := fun _ => zeroL) (y' := fun _ => zeroL) (s := fun _ => zeroL) (s' := K.φ4)
    (c := fun (_ : C) => zeroL) (c' := fun _ => zeroL) (fun _ => .refl _) (fun _ => .refl _) K.c04
    (fun _ => .refl _)
  have g4 := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := K.φ4) (c := fun _ => zeroL) (bX : T → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    (-K.Vᵀ) (fun a b h => (K.sV b a (ne_of_negT K.V h)).symm)
  have g5 := (st_circ K Fm (fun t => lineL (K.tv t)) (fun _ => zeroL) (fun _ => zeroL)).2
  have g6a := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := K.φ5) (c := fun _ => zeroL) (bC : C → Box T Sl C) (bY : T → Box T Sl C) bY_inj
    K.Jrᵀ (fun a b _ => rfl)
  have c6 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun t => lineL (K.tv t))
    (y := fun _ => zeroL) (y' := fun _ => zeroL) (s := K.φ5) (s' := K.φ5)
    (c := fun _ => zeroL) (c' := K.cen) (fun _ => .refl _) (fun _ => .refl _)
    (fun _ => .refl _) K.cc
  have g6b := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun _ => zeroL)
    (s := K.φ5) (c := K.cen) (bS : Sl → Box T Sl C) (bC : C → Box T Sl C) bC_inj
    (-K.Ccᵀ) (fun a b h => (K.sC b a (ne_of_negT K.Cc h)).symm)
  have c7 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun t => lineL (K.tv t))
    (y := fun _ => zeroL) (y' := fun t => perpL (K.tv t)) (s := K.φ5) (s' := K.φ7)
    (c := K.cen) (c' := K.cen) (fun _ => .refl _) K.cy K.c57 (fun _ => .refl _)
  have g7 := st_gate Fm (x := fun t => lineL (K.tv t)) (y := fun t => perpL (K.tv t))
    (s := K.φ7) (c := K.cen) (bS : Sl → Box T Sl C) (bY : T → Box T Sl C) bY_inj
    (-K.Jpᵀ) (fun a b h => K.sJ b a (ne_of_negT K.Jp h))
  have c8 := st_climb Fm (x := fun t => lineL (K.tv t)) (x' := fun _ => fullL)
    (y := fun t => perpL (K.tv t)) (y' := fun t => perpL (K.tv t)) (s := K.φ7)
    (s' := fun _ => fullL) (c := K.cen) (c' := K.cen) K.cx (fun _ => .refl _) K.c7F
    (fun _ => .refl _)
  have g8 := st_wide Fm (x := fun _ => fullL) (y := fun t => perpL (K.tv t))
    (s := fun _ => fullL) (c := K.cen) K.Lᵀ (fun _ _ => rfl)
  have g9 := st_gate Fm (x := fun _ => fullL) (y := fun t => perpL (K.tv t))
    (s := fun _ => fullL) (c := K.cen) (bX : T → Box T Sl C) (bS : Sl → Box T Sl C)
    bS_inj K.Vᵀ (fun a b _ => rfl)
  have tot := ((((((((((g1.trans c4).trans g4).trans g5).trans g6a).trans c6).trans g6b).trans
    c7).trans g7).trans c8).trans g8).trans g9
  exact tot.cast rfl (by omega)

/-- with zero copies the forward invocation is the shear `y += x`; slots are restored. -/
theorem Circuit.fwd_live (z : Box T Sl C → ℂ) (hc : z ∘ bC = 0) :
    K.fwd z ∘ bX = z ∘ bX ∧ K.fwd z ∘ bY = z ∘ bY + z ∘ bX ∧ K.fwd z ∘ bS = z ∘ bS := by
  have hL : ∀ u : Sl → ℂ, ap K.Linv (ap K.L u) = u := fun u => by
    rw [← ap_mul, K.hLL', ap_one]
  have hx : ap K.Jr (ap K.Cc (ap K.L (ap K.V (z ∘ bX)))) + ap K.Jp (ap K.L (ap K.V (z ∘ bX)))
      = z ∘ bX := by
    have h := congrArg (fun M => ap M (z ∘ bX)) K.hid
    simp only [ap_mul, ap_madd, ap_one] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Circuit.fwd, aS_X, onS_X, aY_X, aC_X]
  · simp only [Circuit.fwd, aS_Y, onS_Y, aY_Y, aC_Y, aY_X, aS_X, aY_S, aS_S, onS_S, aC_S,
      aC_C, aY_C, aS_C, onS_C, hc, actPoint_eq_ap, ap_add, ap_mneg, ap_mul, ap_madd, zero_add]
    funext t
    have ht := congrFun hx t
    simp only [Pi.add_apply, Pi.neg_apply] at ht ⊢
    linear_combination ht
  · simp only [Circuit.fwd, aS_S, onS_S, aY_S, aC_S, aS_X, onS_X, aY_X, aC_X, actPoint_eq_ap,
      hL, ap_mneg]
    funext q
    simp only [Pi.add_apply, Pi.neg_apply]
    ring

/-- with zero copies the backward invocation is the shear `x -= y`; slots are restored. -/
theorem Circuit.bwd_live (z : Box T Sl C → ℂ) (hc : z ∘ bC = 0) :
    K.bwd z ∘ bX = z ∘ bX - z ∘ bY ∧ K.bwd z ∘ bY = z ∘ bY ∧ K.bwd z ∘ bS = z ∘ bS := by
  have h1 : ∀ u : T → ℂ, ap K.Linvᵀ (ap (((K.Jr * K.Cc + K.Jp) * K.L)ᵀ) u)
      = ap K.Ccᵀ (ap K.Jrᵀ u) + ap K.Jpᵀ u := fun u => by
    rw [← ap_mul, ← Matrix.transpose_mul, Matrix.mul_assoc, K.hLL, Matrix.mul_one,
      Matrix.transpose_add, Matrix.transpose_mul, ap_madd, ap_mul]
  have h3 : ∀ u : Sl → ℂ, ap K.Lᵀ (ap K.Linvᵀ u) = u := fun u => by
    rw [← ap_mul, ← Matrix.transpose_mul, K.hLL', Matrix.transpose_one, ap_one]
  have h4 : ∀ u : T → ℂ, ap K.Vᵀ (ap (((K.Jr * K.Cc + K.Jp) * K.L)ᵀ) u) = u := fun u => by
    rw [← ap_mul, ← Matrix.transpose_mul, K.hid, Matrix.transpose_one, ap_one]
  have key : ap K.Lᵀ (ap K.Linvᵀ (z ∘ bS + ap (((K.Jr * K.Cc + K.Jp) * K.L)ᵀ) (z ∘ bY))
      + ap (-K.Ccᵀ) (z ∘ bC + ap K.Jrᵀ (z ∘ bY)) + ap (-K.Jpᵀ) (z ∘ bY)) = z ∘ bS := by
    have e1 : ap K.Linvᵀ (z ∘ bS + ap (((K.Jr * K.Cc + K.Jp) * K.L)ᵀ) (z ∘ bY))
        = ap K.Linvᵀ (z ∘ bS) + (ap K.Ccᵀ (ap K.Jrᵀ (z ∘ bY)) + ap K.Jpᵀ (z ∘ bY)) := by
      rw [ap_add, h1]
    rw [hc, zero_add, e1, ap_mneg, ap_mneg]
    have e : ap K.Linvᵀ (z ∘ bS) + (ap K.Ccᵀ (ap K.Jrᵀ (z ∘ bY)) + ap K.Jpᵀ (z ∘ bY))
        + -ap K.Ccᵀ (ap K.Jrᵀ (z ∘ bY)) + -ap K.Jpᵀ (z ∘ bY) = ap K.Linvᵀ (z ∘ bS) := by abel
    rw [e, h3]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Circuit.bwd, aX_X, onS_X, aS_X, aC_X, aX_S, onS_S, aS_S, aC_S, aX_Y, onS_Y,
      aS_Y, aC_Y, aX_C, onS_C, aS_C, aC_C, actPoint_eq_ap, key]
    rw [ap_add, ap_mneg, ap_mneg, h4]
    funext t
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
    ring
  · simp only [Circuit.bwd, aX_Y, onS_Y, aS_Y, aC_Y]
  · simp only [Circuit.bwd, aX_X, onS_X, aS_X, aC_X, aX_S, onS_S, aS_S, aC_S, aX_Y, onS_Y,
      aS_Y, aC_Y, aX_C, onS_C, aS_C, aC_C, actPoint_eq_ap, key]

end Invocation
end
end SS
end PowerSaving
end OAI
