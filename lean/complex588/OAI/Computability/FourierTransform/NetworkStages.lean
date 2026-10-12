import OAI.Computability.FourierTransform.NetworkInvocation
import OAI.Computability.FourierTransform.FrameLifting

namespace OAI

namespace PowerSaving.Cluster
open Binary Finset Matrix

abbrev Key := J → Trip
abbrev Other (j : J) := {i : J // i≠j} → Trip
abbrev Across := Key ⊕ Key
abbrev AllAux := Σ j:J, Other j × Aux

def nrRoles : ℕ := 2*4060^3 + 3*4060^2*(4060^2+33)
def tower : ℕ := 2^50
def mcol : ℕ := 32^3
def bankSave : ℕ := 2*4060^2*(4060 - 3*32*33)

abbrev Spare := Fin (tower - nrRoles)
abbrev Role := Across ⊕ (AllAux ⊕ Spare)
instance keyDec : DecidableEq Key := inferInstance
instance otherDec (j : J) : DecidableEq (Other j) := inferInstance
instance auxDec : DecidableEq AllAux := inferInstance
instance roleDec : DecidableEq Role := inferInstance
instance keyType : Fintype Key := inferInstance
instance otherType (j : J) : Fintype (Other j) := inferInstance
instance auxType : Fintype AllAux := inferInstance
instance roleType : Fintype Role := inferInstance

abbrev gx (d : Key) : Role := .inl (.inl d)
abbrev gy (d : Key) : Role := .inl (.inr d)
abbrev gu (j : J) (o : Other j) (a : Aux) : Role := .inr (.inl ⟨j,o,a⟩)

lemma card_key : Fintype.card Key = 4060^3 := by
  change Fintype.card (J → Trip) = _
  rw [ Fintype.card_fun,num_trip]; simp
lemma card_other (j : J) : Fintype.card (Other j)=4060^2 := by
  change Fintype.card ({i : J // i ≠ j} → Trip) = _
  rw [Fintype.card_fun,num_trip]
  have hh : Fintype.card {i : J // i≠j}=2 := by
    fin_cases j <;> decide
  rw [hh]
lemma card_aux : Fintype.card Aux=4060^2+33 := by
  change Fintype.card ((Trip × Trip) ⊕ (Unit ⊕ H)) = _
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_prod,num_trip]
  simp [H]
lemma card_block : Fintype.card Blocks = mcol := by simp [Blocks, H, J, mcol]
lemma card_allAux : Fintype.card AllAux = 3*4060^2*(4060^2+33) := by
  change Fintype.card (Σ j, Other j × Aux) = _
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod,card_aux,card_other]
  simp [J]
lemma card_role : Fintype.card Role = tower := by
  change Fintype.card ((Key ⊕ Key) ⊕ (AllAux ⊕ Fin (tower - nrRoles))) = _
  simp only [Fintype.card_sum, card_key, card_allAux, Fintype.card_fin]
  norm_num [tower,nrRoles]

def locate (j : J) (o : Other j) (t : Trip) (i : J) : Trip :=
  if h : i=j then t else o ⟨i,h⟩

def omitJ (j : J) (d : Key) : Other j := fun i => d i
@[simp] lemma locate_self (j : J) (o : Other j) (t) : locate j o t j = t := by
  simp [locate]
@[simp] lemma omit_locate (j : J) (o : Other j) (t) : omitJ j (locate j o t) = o := by
  funext i; simp [omitJ, locate, i.property]
@[simp] lemma locate_omit (j : J) (d : Key) : locate j (omitJ j d) (d j) = d := by
  funext i; by_cases i=j <;> simp [locate, omitJ, *]
lemma loc_inj {j : J} {p q : Other j} {i k} (h : locate j p i = locate j q k) :
    p=q ∧ i=k := by
  constructor
  · simpa using congr_arg (omitJ j) h
  · simpa using congr_fun h j

def world (j : J) (p : Other j) : Box → Role
  | .inl (.inl i) => gx (locate j p i)
  | .inl (.inr i) => gy (locate j p i)
  | .inr a => gu j p a

lemma world_inj (j : J) (p q : Other j) (x y : Box) (h : world j p x = world j q y) :
    p=q ∧ x=y := by
  rcases x with ((x|x)|x) <;> rcases y with ((y|y)|y) <;>
    simp only [world, gx, gy, gu, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq] at *
  all_goals first | exact loc_inj h | contradiction | simpa using h

def position (j : J) (p : Other j) : Box ↪ Role :=
  ⟨world j p,fun {_ _} h => (world_inj _ _ _ _ _ h).2⟩

lemma pos_dis (j : J) (p q : Other j) (h : p≠q) (r : Role)
    : r ∈ covered (position j p) → r ∉ covered (position j q) := by
  simp only [cover_iff, not_exists]
  rintro ⟨u, hu⟩ v hv
  exact h (world_inj j p q u v (hu.trans hv.symm)).1

lemma pos_x (j : J) (d : Key) : gx d ∈ covered (position j (omitJ j d)) := by
  rw [cover_iff]
  exact ⟨bx (d j), congr_arg gx (locate_omit ..)⟩
lemma pos_y (j : J) (d : Key) : gy d ∈ covered (position j (omitJ j d)) := by
  rw [cover_iff]
  exact ⟨byy (d j), congr_arg gy (locate_omit ..)⟩
lemma pos_aux (j : J) (d : Other j) (a : Aux) :
    gu j d a ∈ covered (position j d) := by rw [cover_iff]; exact ⟨.inr a,rfl⟩

/-- Global basis and its restriction. -/
def axes (j : J) (d : Other j) : StartAxes := fun i =>
  if h : i=j then OBase.canonical H else tripBase (d ⟨i,h⟩)

def bases : Role → OBase Blocks
  | .inl (.inl d) | .inl (.inr d) => OBase.tensor fun i => tripBase (d i)
  | .inr (.inl ⟨j,d,a⟩) => basisBox j (axes j d) (.inr a)
  | .inr (.inr _) => OBase.canonical Blocks

lemma bases_local (j : J) (d : Other j) :
    bases ∘ position j d = basisBox j (axes j d) := by
  have h (i : Trip) :
      (fun l => tripBase (locate j d i l)) = Function.update (axes j d) j (tripBase i) := by
    funext l; by_cases l=j <;> simp [locate, axes, Function.update, *]
  funext z
  rcases z with ((t|t)|a)
  · exact congr_arg OBase.tensor (h t)
  · exact congr_arg OBase.tensor (h t)
  · rfl

-- Border X has t free axes; Y the same mask with zero address removed.
def region (t : ℕ) : Mask := univ.filter fun x => ∀ i:J, t ≤ i.val → x i=0
def pole : Blocks := fun _ => 0
def rim (t : ℕ) : Mask := region t \ {pole}
def border (t : ℕ) : Role → Mask
  | .inl (.inl _) => region t
  | .inl (.inr _) => rim t
  | .inr (.inl ⟨j,_,_⟩) => if j.val<t then univ else ∅
  | .inr (.inr _) => ∅

lemma in_reg (x) (t : ℕ) : x∈region t ↔ (∀ i:J, t ≤ i.val → x i=0) := by simp [region]

lemma region_begin (j : J) : region j.val = xstart j 0 := by
  ext x
  rw [in_xstart,in_reg]
  constructor
  · intro h; exact ⟨fun i hi => h _ (by exact hi.le),h j le_rfl⟩
  · rintro ⟨h,g⟩ i hi
    rcases eq_or_lt_of_le hi with he|he
    · have eq : j=i := Fin.ext he; subst i; exact g
    · exact h i he
lemma region_end (j : J) : region (j.val+1) = big j := by
  ext x; rw [in_big,in_reg]; rfl

lemma rim_begin (j : J) : rim j.val = ystart j 0 := by
  ext x
  simp only [rim,region_begin,mem_sdiff,mem_singleton,in_ystart,in_xstart]
  constructor
  · rintro ⟨⟨f,g⟩,h⟩; refine ⟨f,?_,g⟩
    intro hi; apply h; funext i
    rcases lt_trichotomy i j with hx|hx|hx
    · apply hi i hx
    · subst i; exact g
    · apply f i hx
  · rintro ⟨f,h,g⟩; refine ⟨⟨f,g⟩,?_⟩
    intro hh; subst x; exact h (fun _ _ => rfl)
lemma rim_end (j : J) : rim (j.val+1) = ystep j 0 := by
  ext x
  simp only [rim,region_end,mem_sdiff,mem_singleton,in_ystep,in_big]
  constructor
  · rintro ⟨f,h⟩; refine ⟨f,?_⟩
    by_contra! hg
    apply h; funext i
    rcases lt_trichotomy i j with hx|hx|hx
    · apply hg.1 i hx
    · subst i; exact hg.2
    · apply f i hx
  · rintro ⟨f,h⟩; refine ⟨f,?_⟩
    intro hh
    subst x
    obtain h|h:=h
    · exact h (fun _ _ => rfl)
    · exact h rfl

lemma border_bp (j : J) (p : Other j) :
    border j.val ∘ position j p = bp j := by
  funext x
  rcases x with ((x|y)|(s|c))
  · exact region_begin j
  · exact rim_begin j
  · change border j.val (world j p (.inr (.inl s))) = _
    simp [border, world, bp, stamp, gu]
  · change border j.val (world j p (.inr (.inr c))) = _
    simp [border, world, bp, stamp, gu]
lemma border_end (j : J) (p : Other j) :
    border (j.val+1) ∘ position j p = bend j := by
  funext x
  rcases x with ((x|y)|(s|c))
  · exact region_end j
  · exact rim_end j
  · change border (j.val + 1) (world j p (.inr (.inl s))) = _
    simp [border, world, bend, stamp, gu]
  · change border (j.val + 1) (world j p (.inr (.inr c))) = _
    simp [border, world, bend, stamp, gu]

noncomputable section

def stageOp (rev : Bool) (x : Role→ℂ) : Role→ℂ
  | .inl (.inl i) => if rev then x (gx i)-x (gy i) else x (gx i)
  | .inl (.inr i) => if rev then x (gy i) else x (gy i)+x (gx i)
  | .inr a => x (.inr a)

def stageLoss := 4060^2*(33*32)

lemma stage (rev : Bool) (j : J) :
    Path bases (border j.val) (border (j.val+1)) (stageOp rev) stageLoss := by
  let d : Other j → ℕ := fun _ => 33*32
  have hd : stageLoss=∑ i, d i := by
    dsimp only [d]
    rw [sum_const,card_univ,card_other]
    simp [stageLoss]
  rw [hd]
  let h := fun _ : Other j => if rev then backward else forward
  apply Path.parallel (position j) (pos_dis j) bases (h:=h)
  · intro i
    rw [bases_local,border_bp,border_end]
    cases rev
    · exact (invocation j (axes j i)).1
    · exact (invocation j (axes j i)).2
  · intro i x
    funext r
    rcases r with ((r|r)|(r|r)) <;> cases rev <;> rfl
  · rintro x ((k|k)|r) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨bx (k j), congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨byy (k j), congr_arg gy (locate_omit ..)⟩
    · rfl
  · rintro ((k|k)|(⟨i,p,a⟩|r)) hr
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨bx (k j), congr_arg gx (locate_omit ..)⟩
    · exfalso; specialize hr (omitJ j k); apply hr; rw [cover_iff]; exact ⟨byy (k j), congr_arg gy (locate_omit ..)⟩
    · by_cases ig : i=j
      · subst i; exfalso; specialize hr p; apply hr; rw [cover_iff]; exact ⟨.inr a,rfl⟩
      · change (if i.val < j.val then univ else ∅) =
          (if i.val < j.val + 1 then univ else ∅)
        have h : i.val≠j.val := fun h => ig (Fin.ext h)
        simp only [show (i.val < j.val+1) ↔ (i.val < j.val) from (by omega)]
    · rfl

end
end PowerSaving.Cluster

end OAI
