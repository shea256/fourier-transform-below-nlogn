import OAI.Computability.FourierTransform.DirectionalWords

namespace OAI

namespace PowerSaving.Cluster
open Finset Binary
/-! Binary network with 32 coordinates. Triple indicators omit two fixed pivots.
Unused ordered side pairs can also have storage assigned. -/

abbrev H := Fin 32
abbrev J := Fin 3
abbrev Blocks := J → H
abbrev Mask := Finset Blocks
def freeSet : Finset H := univ \ {0,1}
def tripSet := freeSet.powersetCard 3
abbrev Trip := ↑tripSet

lemma piv : (0:H) ≠ 1 := by decide

lemma trip_card (x : Trip) : x.val.card = 3 :=
  (Finset.mem_powersetCard.mp x.property).2

lemma trip_sub (x : Trip) : x.val ⊆ freeSet :=
  (Finset.mem_powersetCard.mp x.property).1

lemma num_trip : Fintype.card Trip = 4060 := by
  rw [Fintype.card_coe tripSet, tripSet, Finset.card_powersetCard]
  have hf : freeSet.card = 30 := by
    rw [freeSet, card_sdiff_of_subset (subset_univ _)]
    simp
  rw [hf, Nat.choose_eq_descFactorial_div_factorial]
  decide

def meet (x y : Trip) := (x.val ∩ y.val).card
def neighbor (x y : Trip) := meet x y = 0 ∨ meet x y = 2
instance (x y : Trip) : Decidable (neighbor x y) := by unfold neighbor; infer_instance

lemma meet_comm (x y : Trip) : meet x y = meet y x := by simp [meet, inter_comm]
lemma meet_self (x : Trip) : meet x x=3 := by simp [meet, trip_card]
lemma meet_le (x y : Trip) (h : x≠y) : meet x y ≤ 2 := by
  unfold meet
  have hi := card_le_card (inter_subset_left (s₁:=x.val) (s₂:=y.val))
  by_contra he
  have hh : (x.val ∩ y.val).card = 3 := by have := trip_card x; omega
  have hx : x.val ∩ y.val = x.val :=
    eq_of_subset_of_card_le inter_subset_left (by simp [hh,trip_card])
  have hy : x.val ∩ y.val = y.val :=
    eq_of_subset_of_card_le inter_subset_right (by simp [hh,trip_card])
  exact h (Subtype.ext (hx.symm.trans hy))

lemma neighbor_comm (x y : Trip) : neighbor x y ↔ neighbor y x := by
  simp only [neighbor, meet_comm x y]

def tip (x : Trip) : Space H := fun i => if i∈x.val then 1 else 0

/-- Also useful for scalar rows. -/
theorem meet_ind {R : Type*} [Semiring R] (x y : Trip) :
    ∑ i : H, ((if i ∈ x.val then (1:R) else 0)*(if i ∈ y.val then 1 else 0))
    = (meet x y:R) := by
  calc
    _ = ∑ i ∈ (univ:Finset H), (if i∈x.val∩y.val then (1:R) else 0) := by
      apply sum_congr rfl
      intro i hi
      by_cases hx : i∈x.val <;> by_cases hy : i∈y.val <;> simp [*]
    _ = ∑ i ∈ x.val∩y.val, (1:R) := by
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext; simp
    _ = _ := by simp [meet]

@[simp] theorem tip_unit (x : Trip) : dot (tip x) (tip x)=1 := by
  unfold dot tip
  rw [meet_ind, meet_self]
  decide

@[simp] theorem tip_zero (x : Trip) : tip x 0 = 0 := by
  have h : 0∉x.val := by intro hh; have := trip_sub x hh; simp [freeSet] at this
  simp [tip,h]
@[simp] theorem tip_one (x : Trip) : tip x 1 = 0 := by
  have h : 1∉x.val := by intro hh; have := trip_sub x hh; simp [freeSet] at this
  simp [tip,h]

theorem tip_orth (x y : Trip) (h : neighbor x y) :
    dot (tip x) (tip y)=0 := by
  unfold dot tip
  rw [meet_ind]
  obtain he|he := h <;> rw [he] <;> decide

def tripBase (x : Trip) : OBase H :=
  OBase.adapt (OBase.canonical H) 0 (tip x) (tip_unit x)
    (by simp [OBase.canonical])

@[simp] theorem tripBase_main (x : Trip) : (tripBase x).v 0 = tip x :=
  OBase.adapt_pivot _ _ _ _ _
@[simp] theorem tripBase_unused (x : Trip) : (tripBase x).v 1 = eu 1 :=
  OBase.adapt_other _ _ _ _ piv _ _ (by simp [OBase.canonical])

def pairBase (x y : Trip) : OBase H :=
  if h : neighbor x y then
    OBase.adapt (tripBase x) 1 (tip y) (tip_unit y) (by simp)
  else OBase.canonical H

@[simp] lemma pairBase_left (x y : Trip) (h : neighbor x y) :
    (pairBase x y).v 0 = tip x := by
  unfold pairBase; rw [dite_eq_left h]
  rw [OBase.adapt_other, tripBase_main]
  · exact piv.symm
  · simp [dot_symm (tip y), tip_orth x y h]

@[simp] lemma pairBase_right (x y : Trip) (h : neighbor x y) :
    (pairBase x y).v 1 = tip y := by
  unfold pairBase; rw [dite_eq_left h,OBase.adapt_pivot]

section Masks

/-- Rectangles: free past if e=true, fixed zero otherwise; select S in the current axis;
 future fixed zero. -/
def sets (j : J) (e : Bool) (s : Finset H) (i : J) : Finset H :=
  if i=j then s else if i<j ∧ e=true then univ else {0}

def rect (j : J) (e : Bool) (s : Finset H) : Mask :=
  Fintype.piFinset (sets j e s)

def future (j : J) (x : Blocks) := ∀ i : J, j < i → x i=0
def previous (j : J) (x : Blocks) := ∀ i : J, i<j → x i=0

lemma mem_rect (j : J) (e : Bool) (s : Finset H) (x) :
    x ∈ rect j e s ↔ future j x ∧ (e=false → previous j x) ∧ x j∈s := by
  rw [rect, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun hg i hi => ?_, by simpa [sets] using h j⟩
    · simpa [sets, ne_of_gt hi, not_lt.mpr hi.le] using h i
    · simpa [sets, hg, ne_of_lt hi] using h i
  · rintro ⟨hf,hg,hs⟩ i
    unfold sets
    rcases lt_trichotomy i j with h|h|h
    · cases e
      · simp [ne_of_lt h, hg rfl i h]
      · simp [ne_of_lt h,h]
    · subst i; simp [hs]
    · simp [ne_of_gt h, not_lt.mpr h.le, hf i h]

-- Label abbreviations (at fixed j)
def big (j : J) : Mask := rect j true univ
def belt (j : J) : Mask := big j \ rect j false univ
def xstart (j : J) (slot : H) : Mask := rect j true {slot}
def ystart (j : J) (slot : H) : Mask := xstart j slot \ rect j false {slot}
/-- Big minus P tensor the complement of the slot. -/
def xstep (j : J) (slot : H) : Mask := big j \ rect j false (univ \ {slot})
def ystep (j : J) (slot : H) : Mask := big j \ rect j false {slot}

theorem in_big (j : J) (x) : x ∈ big j ↔ future j x := by simp [big, mem_rect]
theorem in_belt (j : J) (x) : x ∈ belt j ↔ future j x ∧ ¬previous j x := by
  simp [belt, in_big, mem_rect]; tauto
theorem in_xstart (j : J) (slot : H) (x) :
    x∈xstart j slot ↔ future j x ∧ x j=slot := by simp [xstart,mem_rect]
theorem in_ystart (j : J) (slot : H) (x) :
    x∈ystart j slot ↔ future j x ∧ ¬previous j x ∧ x j=slot := by
  simp [ystart,in_xstart,mem_rect]; tauto
theorem in_xstep (j : J) (slot : H) (x) :
    x∈xstep j slot ↔ future j x ∧ (¬previous j x ∨ x j=slot) := by
  simp [xstep, in_big,mem_rect]; tauto
theorem in_ystep (j : J) (slot : H) (x) :
    x∈ystep j slot ↔ future j x ∧ (¬previous j x ∨ x j≠slot) := by
  simp [ystep, in_big,mem_rect]; tauto

lemma rect_le_big (j : J) (e : Bool) (s : Finset H) :
    rect j e s ⊆ big j :=
  fun k h => (in_big j k).2 ((mem_rect ..).1 h).1

lemma belt_drop (j : J) :
    (big j \ belt j).card = 32 := by
  have hs := rect_le_big j false univ
  have eq : big j \ belt j = rect j false univ := by
    ext k
    simp only [belt, mem_sdiff]
    have h : k ∈ rect j false univ → k∈big j := fun hh => hs hh
    tauto
  rw [eq, rect, Fintype.card_piFinset]
  rw [Finset.prod_eq_single j]
  · simp [sets]
  all_goals
    first | intro i _ hi; simp [sets, hi] | simp

/-- Compare frames by comparing the current base projectors. -/
lemma rect_proj {b d : J → OBase H} {j : J} {s t : Finset H}
    (hi : ∀ i, i ≠ j → b i = d i)
    (hh : (b j).mat s = (d j).mat t) (e : Bool) :
    (OBase.tensor b).mat (rect j e s) = (OBase.tensor d).mat (rect j e t) := by
  unfold rect
  rw [OBase.mat_rect,OBase.mat_rect]
  apply congrArg (fun f : J → Matrix H H F => digitProd f)
  funext k
  by_cases h : k=j
  · subst k; simpa [sets] using hh
  · simp [sets, h, hi k h]

lemma singleton_proj {b d : OBase H} {i k : H} (h : b.v i=d.v k) :
    b.mat {i}=d.mat {k} := by
  ext j l
  simp [OBase.mat, h]

lemma big_proj {b d : J → OBase H} {j : J} (hi : ∀ i, i ≠ j → b i = d i) :
    (OBase.tensor b).mat (big j) = (OBase.tensor d).mat (big j) :=
  rect_proj hi (by simp) _

lemma belt_proj {b d : J → OBase H} {j : J} (hi : ∀ i, i ≠ j → b i = d i) :
    (OBase.tensor b).mat (belt j) = (OBase.tensor d).mat (belt j) := by
  unfold belt
  rw [OBase.mat_sub _ _ _ (rect_le_big ..), OBase.mat_sub _ _ _ (rect_le_big ..),
    big_proj hi, rect_proj (s:=univ) (t:=univ) hi (by simp)]

lemma ystart_proj {b d : J → OBase H} {j : J} (hi : ∀ i, i ≠ j → b i = d i)
    {e f : H} (hh : (b j).v e=(d j).v f) :
    (OBase.tensor b).mat (ystart j e) = (OBase.tensor d).mat (ystart j f) := by
  have hs (e : H) : rect j false {e} ⊆ rect j true {e} := by
    intro k hk
    simp only [mem_rect] at *
    exact ⟨hk.1,(by simp),hk.2.2⟩
  have ht := rect_proj hi (singleton_proj hh)
  unfold ystart xstart
  rw [OBase.mat_sub _ _ _ (hs e), OBase.mat_sub _ _ _ (hs f), ht, ht]

lemma xstep_proj {b d : J → OBase H} {j : J} (hi : ∀ i, i ≠ j → b i = d i)
    {e f : H} (hh : (b j).v e=(d j).v f) :
    (OBase.tensor b).mat (xstep j e) = (OBase.tensor d).mat (xstep j f) := by
  unfold xstep
  rw [OBase.mat_sub _ _ _ (rect_le_big ..), OBase.mat_sub _ _ _ (rect_le_big ..), big_proj hi]
  congr 1
  apply rect_proj hi
  rw [OBase.mat_sub _ _ _ (subset_univ _), OBase.mat_sub _ _ _ (subset_univ _),
    singleton_proj hh]; simp

lemma ystep_proj {b d : J → OBase H} {j : J} (hi : ∀ i, i ≠ j → b i = d i)
    {e f : H} (hh : (b j).v e=(d j).v f) :
    (OBase.tensor b).mat (ystep j e) = (OBase.tensor d).mat (ystep j f) := by
  unfold ystep
  rw [OBase.mat_sub _ _ _ (rect_le_big ..), OBase.mat_sub _ _ _ (rect_le_big ..),
     big_proj hi, rect_proj hi (singleton_proj hh)]

end Masks

end PowerSaving.Cluster

end OAI
