import OAI.Computability.FourierTransform.TensorIndexing
import OAI.Computability.FourierTransform.Cost

namespace OAI

/-! Sector partitions of arbitrary sequences of pair slots. -/
namespace PowerSaving.Grove
open Slant Finset
noncomputable section

/-- helper for Nat ranged permutations -/
structure Reloc (n : ℕ) (q : ℕ → ℕ) : Prop where
  bd : ∀ j<n, q j<n
  inj : ∀ i<n, ∀ j<n, q i=q j → i=j

def seek (n : ℕ) (q : ℕ → ℕ) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, j<n ∧ q j=i then Classical.choose h else 0

namespace Reloc
variable {n : ℕ} {q : ℕ→ℕ}

lemma onto (h : Reloc n q) : ∀ j<n, ∃ i<n, q i=j := by
  let f : Fin n → Fin n := fun i => ⟨q i.val,h.bd _ i.isLt⟩
  have g : Function.Injective f := by
    intro i j hij
    exact Fin.ext (h.inj _ i.isLt _ j.isLt (Fin.mk.inj hij))
  intro j hj
  obtain ⟨i,hi⟩ := (Finite.surjective_of_injective g) ⟨j,hj⟩
  exact ⟨i.val,i.isLt,Fin.mk.inj hi⟩

lemma seeks (h : Reloc n q) {i : ℕ} (hi : i<n) :
    seek n q i < n ∧ q (seek n q i) = i := by
  classical
  unfold seek; simp only [dite_eq_left (h.onto i hi)]
  exact Classical.choose_spec (h.onto i hi)

lemma seeks_at (h : Reloc n q) {i : ℕ} (hi : i<n) :
    seek n q (q i) = i :=
  let g := h.seeks (h.bd _ hi); h.inj _ g.1 i hi g.2

lemma sum {A : Type*} [AddCommMonoid A] (h : Reloc n q) (f : ℕ → A) :
    ∑ i ∈ range n, f (q i) = ∑ i ∈ range n, f i :=
  sum_bij (fun i _ => q i) (fun i hi => mem_range.mpr (h.bd i (mem_range.mp hi)))
    (fun a ha b hb hab => h.inj a (mem_range.mp ha) b (mem_range.mp hb) hab)
    (fun i hi => by
      obtain ⟨j,hj,g⟩ := h.onto i (mem_range.mp hi); exact ⟨j,mem_range.mpr hj,g⟩)
    (fun _ _ => rfl)

lemma sow {A : Type*} (h : Reloc n q) (f : ℕ → A) (z : A) :
    Tape.sow n n z (fun i => (q i,f i)) = Tape.tab n (fun i => f (seek n q i)) := by
  apply Tape.ext_look (by simp) z
  intro i hi
  have hi' : i<n := by simpa using hi
  rw [Tape.look_tab, ite_eq_left hi']
  have g := h.seeks hi'
  refine Tape.sow_look_written hi' g.1 g.2 ?_
  intro s hs hk hsi
  have hh := h.inj _ hk _ g.1 (Eq.trans hsi g.2.symm)
  omega

end Reloc

structure Shard where
  start : ℕ
  width : ℕ
  height : ℕ
  seat : ℕ
deriving DecidableEq

namespace Shard

def tip (s : Shard) := s.start+s.width
def addr (s : Shard) := s.start+s.seat

structure Mark (s : Shard) (n l : ℕ) : Prop where
  endsBy : s.tip ≤ n
  size : s.width=2^s.height
  tall : s.height ≤ l
  place : s.seat < s.width

namespace Mark
variable {s : Shard} {n l : ℕ}
lemma small (h : Mark s n l) : s.addr < s.tip :=
  Nat.add_lt_add_left h.place _
lemma positive (h : Mark s n l) : 0<s.width := by rw [h.size]; positivity
lemma starts (h : Mark s n l) : s.start < s.tip :=
  Nat.lt_add_of_pos_right h.positive
end Mark

def same (s t : Shard) : Prop :=
  s.start=t.start ∧ s.width=t.width ∧ s.height=t.height

def fits (s t : Shard) : Prop :=
  same s t ∨ s.tip ≤ t.start ∨ t.tip ≤ s.start

structure Quilt (n l : ℕ) (f : ℕ → Shard) : Prop where
  mark : ∀ i<n, (f i).Mark n l
  seam : ∀ i<n, ∀ j<n, (f i).fits (f j)
  fiber : ∀ i<n, ∀ j<n, (f i).addr=(f j).addr → i=j

/-- Metadata on packed indices; never computed by inversion, only used for proofs. -/
def patch (n : ℕ) (f : ℕ → Shard) (j : ℕ) :=
  f (seek n (fun i => (f i).addr) j)

namespace Quilt
variable {n l : ℕ} {f : ℕ → Shard}

lemma reloc (h : Quilt n l f) : Reloc n fun i => (f i).addr :=
  ⟨fun i hi => ((h.mark i hi).small).trans_le (h.mark i hi).endsBy,h.fiber⟩

lemma aligns (h : Quilt n l f) {i j : ℕ} (hi : i<n) (hj : j<n)
    (H : (f i).start < (f j).tip) (G : (f j).start < (f i).tip) :
    (f i).same (f j) :=
  (h.seam i hi j hj).resolve_right fun hh => hh.elim (not_le.mpr G) (not_le.mpr H)

lemma matches_of_eq (h : Quilt n l f) {i j : ℕ} (hi : i<n) (hj : j<n)
    (H : (f i).start=(f j).start) :
    (f i).same (f j) :=
  h.aligns hi hj (by rw [H]; exact (h.mark j hj).starts)
    (by rw [← H]; exact (h.mark i hi).starts)

lemma patch_addr (h : Quilt n l f) {i : ℕ} (hi : i<n) :
    (patch n f i).addr=i := (h.reloc.seeks hi).2

lemma patch_mark (h : Quilt n l f) {i : ℕ} (hi : i<n) :
    (patch n f i).Mark n l := h.mark _ (h.reloc.seeks hi).1

lemma patch_at (h : Quilt n l f) {i : ℕ} (hi : i<n) :
    patch n f (f i).addr=f i := by unfold patch; rw [h.reloc.seeks_at hi]

lemma patch_seam (h : Quilt n l f) {i j : ℕ} (hi : i<n) (hj : j<n) :
    (patch n f i).fits (patch n f j) :=
  h.seam _ (h.reloc.seeks hi).1 _ (h.reloc.seeks hj).1

lemma patch_align (h : Quilt n l f) {i j : ℕ} (hi : i<n) (H : (f i).start ≤ j)
    (G : j < (f i).tip) : (patch n f j).same (f i) ∧ (patch n f j).seat=j-(f i).start := by
  have hj : j<n := G.trans_le (h.mark i hi).endsBy
  let F := seek n (fun i => (f i).addr) j
  have hF : F<n := (h.reloc.seeks hj).1
  have h1 : (f F).addr=j := h.patch_addr hj
  have h2 : j<(f F).tip := h1 ▸ (h.mark F hF).small
  have h3 : (f F).start ≤ j := by rw [← h1,addr]; omega
  have hh := h.aligns hF hi (lt_of_le_of_lt h3 G) (lt_of_le_of_lt H h2)
  refine ⟨hh,?_⟩
  have hs := hh.1
  unfold addr at h1
  change (f F).seat = _
  omega
end Quilt

/-- composition of sector metadata under extension of an axis. -/
def fringe (r : ℕ) (s t : Shard) : Shard :=
  ⟨s.start*r + s.width*t.start, s.width*t.width, s.height+t.height,
    s.seat*t.width + t.seat⟩

lemma fr_tip (r : ℕ) (s t : Shard) : (fringe r s t).tip = s.start*r+s.width*t.tip := by
  change _+_+(s.width*t.width)=_+s.width*(t.start+t.width)
  ring

lemma tip_steps (s t : Shard) (r j : ℕ) (h : Mark t r j) :
    (fringe r s t).tip ≤ s.tip*r := by
  rw [fr_tip,show s.tip=s.start+s.width from rfl, add_mul]
  simpa only [mul_comm r] using (Nat.add_le_add_left
    (Nat.mul_le_mul_left s.width h.endsBy) (s.start*r))

lemma Mark.fringe {s t : Shard} {n i r j : ℕ} (h : Mark s n i) (g : Mark t r j) :
    Mark (fringe r s t) (n*r) (i+j) := by
  refine ⟨(tip_steps s t r j g).trans (Nat.mul_le_mul_right r h.endsBy),
    ?_,Nat.add_le_add h.tall g.tall,?_⟩
  · change s.width*t.width=_
    change s.width*t.width=2^(s.height+t.height)
    rw [pow_add,h.size,g.size]
  · change s.seat*t.width + t.seat < s.width*t.width
    calc
      _ < s.seat*t.width+t.width := Nat.add_lt_add_left g.place _
      _ ≤ _ := by simpa only [add_mul,one_mul] using Nat.mul_le_mul_right t.width (show s.seat+1 ≤ s.width from h.place)

lemma fr_same {s t s' t' : Shard} (r : ℕ) (hs : s.same s') (ht : t.same t') :
    (fringe r s t).same (fringe r s' t') := by
  unfold same fringe at *; dsimp
  rw [hs.1,hs.2.1,hs.2.2,ht.1,ht.2.1,ht.2.2]; simp

lemma fr_before {s t s' t' : Shard} (r j : ℕ) (hs : s.tip ≤ s'.start) (hg : Mark t r j) :
    (fringe r s t).tip ≤ (fringe r s' t').start :=
  le_trans ((tip_steps s t r j hg).trans (Nat.mul_le_mul_right r hs)) (Nat.le_add_right ..)

lemma fr_within {s t s' t' : Shard} (r : ℕ) (hs : s.same s') (ht : t.tip ≤ t'.start) :
    (fringe r s t).tip ≤ (fringe r s' t').start := by
  rw [fr_tip]; change _ ≤ s'.start*r + s'.width*t'.start
  rw [hs.1,hs.2.1]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _

lemma same_sym {s t : Shard} (h : s.same t) : t.same s :=
  ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩

lemma fr_fits {s t s' t' : Shard} (r j : ℕ) (hg : Mark t r j) (hg' : Mark t' r j)
    (hs : s.fits s') (ht : t.fits t') :
    (fringe r s t).fits (fringe r s' t') := by
  rcases hs with H|H|H
  · rcases ht with G|G|G
    · exact Or.inl (fr_same r H G)
    · exact Or.inr (Or.inl (fr_within r H G))
    · exact Or.inr (Or.inr (fr_within r (same_sym H) G))
  · exact Or.inr (Or.inl (fr_before r j H hg))
  · exact Or.inr (Or.inr (fr_before r j H hg'))

lemma fr_unique {s t s' t' : Shard} (r j : ℕ) (hg : Mark t r j) (hg' : Mark t' r j)
    {n i : ℕ} (_ha : Mark s n i) (_ha' : Mark s' n i) (hs : s.fits s') (ht : t.fits t')
    (H : (fringe r s t).start < (fringe r s' t').tip)
    (G : (fringe r s' t').start < (fringe r s t).tip) :
    s.same s' ∧ t.same t' := by
  rcases hs with h|h|h
  · rcases ht with g|g|g
    · exact ⟨h,g⟩
    · exact absurd (fr_within r h g) (not_le.mpr G)
    · exact absurd (fr_within r (same_sym h) g) (not_le.mpr H)
  · exact absurd (fr_before r j h hg) (not_le.mpr G)
  · exact absurd (fr_before r j h hg') (not_le.mpr H)

def attach (r : ℕ) (u v : ℕ → Shard) : ℕ → Shard := fun i =>
  fringe r (u (i/r)) (v (i%r))

lemma Quilt.attach {m n i j : ℕ} {f g : ℕ→Shard} (h : Quilt m i f) (k : Quilt n j g)
    (hn : 0<n) :
    Quilt (m*n) (i+j) (Shard.attach n f g) := by
  have top (s : ℕ) (hs : s < m*n) : s/n < m := (Nat.div_lt_iff_lt_mul hn).mpr hs
  have lo (s : ℕ) : s%n<n := Nat.mod_lt s hn
  have hh (s : ℕ) (hs : s < m*n) :
      (Shard.attach n f g s).Mark (m*n) (i+j) :=
    (h.mark _ (top s hs)).fringe (k.mark _ (lo s))
  refine ⟨hh,?_,?_⟩
  · intro a ha b hb
    exact fr_fits n j (k.mark _ (lo a)) (k.mark _ (lo b))
      (h.seam _ (top a ha) _ (top b hb)) (k.seam _ (lo a) _ (lo b))
  · intro a ha b hb hab
    let T := Shard.attach n f g
    change (T a).addr=(T b).addr at hab
    have h1 : (T a).start < (T b).tip :=
      lt_of_le_of_lt (Nat.le_add_right (T a).start (T a).seat)
        (Eq.subst (motive:=fun z => z < (T b).tip) hab.symm (hh b hb).small)
    have h2 : (T b).start < (T a).tip :=
      lt_of_le_of_lt (Nat.le_add_right (T b).start (T b).seat)
        (Eq.subst (motive:=fun z => z < (T a).tip) hab (hh a ha).small)
    obtain ⟨ht,hg⟩ := fr_unique n j (k.mark _ (lo a)) (k.mark _ (lo b))
      (h.mark _ (top a ha)) (h.mark _ (top b hb)) (h.seam _ (top a ha) _ (top b hb))
      (k.seam _ (lo a) _ (lo b)) h1 h2
    have ht' : (T a).same (T b) := fr_same n ht hg
    unfold addr at hab; rw [ht'.1] at hab
    have H := Nat.add_left_cancel hab
    change (f (a/n)).seat*(g (a%n)).width+(g (a%n)).seat =
      (f (b/n)).seat*(g (b%n)).width+(g (b%n)).seat at H
    have diy (b : ℕ) := (k.mark _ (lo b)).place
    have hD := congr_arg (· / (g (a%n)).width) H
    have hM := congr_arg (· % (g (a%n)).width) H
    rw [chops _ _ _ (diy a),hg.2.1,chops _ _ _ (diy b)] at hD
    rw [chips _ _ _ (diy a),hg.2.1,chips _ _ _ (diy b)] at hM
    have IH := h.fiber _ (top a ha) _ (top b hb) (congr_arg₂ Nat.add ht.1 hD)
    have IL := k.fiber _ (lo a) _ (lo b) (congr_arg₂ Nat.add hg.1 hM)
    exact (joined a n).symm.trans (by rw [IH,IL,joined])

end Shard

/- Shards from a local slot. -/
namespace Hem
open Slant Stroke Shard

variable (u : Stroke)
def crown (i : ℕ) := min i (u.partner i)
def thickness (i : ℕ) := if i=u.partner i then 1 else 2
def up (i : ℕ) := if i=u.partner i then 0 else 1
def trim (i : ℕ) := if i=crown u i then thickness u i else 0
def tier (i : ℕ) := if i=crown u i then 0 else 1
def sums (i : ℕ) := ∑ a ∈ range i, trim u a

def hem (i : ℕ) : Shard :=
  ⟨sums u (crown u i), thickness u i, up u i, tier u i⟩

variable {u}

lemma crown_partner {n i : ℕ} (h : u.Sound n) : crown u (u.partner i)=crown u i := by
  unfold crown; rw [h.pair]; omega

lemma thickness_partner {n i : ℕ} (h : u.Sound n) :
    thickness u (u.partner i)=thickness u i := by
  simp [thickness,h.pair,eq_comm]

lemma crown_closed {n i : ℕ} (h : u.Sound n) : crown u (crown u i)=crown u i := by
  rcases le_or_gt i (u.partner i) with g|g
  · have H : crown u i=i := min_eq_left g; rw [H,H]
  · have H : crown u i=u.partner i := min_eq_right g.le
    exact (congr_arg (crown u) H).trans (crown_partner h)

lemma crown_class {n i j : ℕ} (h : u.Sound n) (g : crown u i=crown u j) :
    j=i ∨ j=u.partner i := by
  rcases min_choice i (u.partner i) with H|H <;> rcases min_choice j (u.partner j) with G|G
  · unfold crown at g; exact Or.inl (by omega)
  · unfold crown at g
    have h' : u.partner j=i := by omega
    exact Or.inr ((h.pair _).symm.trans (congr_arg u.partner h'))
  · unfold crown at g; exact Or.inr (by omega)
  · unfold crown at g
    have h' : u.partner j=u.partner i := by omega
    exact Or.inl ((h.pair _).symm.trans ((congr_arg u.partner h').trans (h.pair i)))

lemma thick_tip {n i : ℕ} (h : u.Sound n) :
    trim u (crown u i)=thickness u i := by
  rw [trim,ite_eq_left (crown_closed h).symm]
  rcases (crown_class h (crown_closed h).symm) with k|k
  · rw [k]
  · rw [k,thickness_partner h]

lemma tier_lt (u : Stroke) (i : ℕ) : tier u i < thickness u i := by
  by_cases h : i=u.partner i
  · simp only [tier,crown,thickness,← h,min_self,↓reduceIte]
    omega
  · unfold tier thickness; split_ifs <;> omega

lemma sum_trim {n : ℕ} (h : u.Sound n) :
    sums u n=n := by
  let H := u.partner
  have step (i : ℕ) : trim u i + trim u (u.partner i) = 2 := by
    unfold trim; rw [thickness_partner h,crown_partner h]
    unfold crown thickness
    split_ifs <;> omega
  have hh : Reloc n H :=
    ⟨h.bdp,fun i _ j _ g => (h.pair i).symm.trans ((congr_arg H g).trans (h.pair j))⟩
  have HG : sums u n+sums u n=n*2 := calc
    _ = sums u n + ∑ j ∈ range n, trim u (H j) := congr_arg (sums u n+·) (hh.sum _).symm
    _ = n*2 := by
      unfold sums; rw [← sum_add_distrib]
      dsimp only [H]; simp [step]
  omega

lemma tip_hem {n i : ℕ} (h : u.Sound n) :
    (hem u i).tip=sums u (crown u i+1) := by
  change sums _ _+_ = ∑ a ∈ _, _
  rw [sum_range_succ,thick_tip h]; rfl

lemma sums_mono (u : Stroke) : Monotone (sums u) := by
  apply monotone_nat_of_le_succ
  intro i; unfold sums; rw [sum_range_succ]; omega

lemma marked {n i : ℕ} (h : u.Sound n) (hi : i<n) : (hem u i).Mark n 1 := by
  refine ⟨?_,?_,?_,tier_lt u i⟩
  · rw [tip_hem h]
    exact le_trans (sums_mono u
      (show crown u i+1≤n from by unfold crown; omega)) (sum_trim h).le
  · change thickness u i=2^up u i; unfold thickness up; split_ifs <;> rfl
  · change up u i ≤ 1; unfold up; split <;> omega

lemma same_class {n i j : ℕ} (h : u.Sound n) (g : crown u i=crown u j) :
    (hem u i).same (hem u j) := by
  rcases crown_class h g with rfl|rfl
  · exact ⟨rfl,rfl,rfl⟩
  · refine ⟨congr_arg (sums u) g, (thickness_partner h).symm,?_⟩
    simp [hem,up,h.pair,eq_comm]

lemma hem_before {n i j : ℕ} (h : u.Sound n) (g : crown u i<crown u j) :
    (hem u i).tip≤(hem u j).start := by
  rw [tip_hem h]; exact sums_mono u g

lemma class_of_start {n i j : ℕ} (h : u.Sound n) (hi : i<n) (hj : j<n)
    (g : (hem u i).start=(hem u j).start) :
    crown u i=crown u j := by
  rcases lt_trichotomy (crown u i) (crown u j) with k|k|k
  · have := (marked h hi).starts; have := hem_before h k; omega
  · exact k
  · have := (marked h hj).starts; have := hem_before h k; omega

lemma tier_partner_ne {n i : ℕ} (h : u.Sound n) (g : u.partner i ≠ i) :
    tier u (u.partner i) ≠ tier u i := by
  unfold tier; rw [crown_partner h]; unfold crown; split_ifs <;> omega

lemma quilt {n : ℕ} (h : u.Sound n) : Quilt n 1 (hem u) := by
  refine ⟨fun _ hi => marked h hi,?_,?_⟩
  · intro i hi j hj
    rcases lt_trichotomy (crown u i) (crown u j) with k|k|k
    · exact Or.inr (Or.inl (hem_before h k))
    · exact Or.inl (same_class h k)
    · exact Or.inr (Or.inr (hem_before h k))
  · intro i hi j hj g
    rcases lt_trichotomy (crown u i) (crown u j) with k|k|k
    · have hh := hem_before h k
      have hu := (marked h hi).small
      unfold addr at hu g; omega
    · unfold addr at g; rw [(same_class h k).1] at g
      have hh : tier u i=tier u j := Nat.add_left_cancel g
      rcases crown_class h k with rfl|rfl
      · rfl
      · by_contra hz; exact (tier_partner_ne h (Ne.symm hz)) hh.symm
    · have hh := hem_before h k
      have hu := (marked h hj).small
      unfold addr at hu g; omega

end Hem

/- Global sectorization. -/
open Shard Hem

def seed : Shard := ⟨0,1,0,0⟩
def mosaic (r : Axes) (u : ℕ → Stroke) : ℕ → ℕ → Shard
  | 0 => fun _ => seed
  | l+1 => attach (r l) (mosaic r u l) (hem (u l))

lemma seed_quilt : Shard.Quilt 1 0 fun _ => seed := by
  refine ⟨fun i _ => ⟨by decide,by decide,le_rfl,by decide⟩,
    fun _ _ _ _ => Or.inl ⟨rfl,rfl,rfl⟩,fun i hi j hj _ => by omega⟩

lemma mosaic_quilt (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) :
    Quilt (extent r l) l (mosaic r u l) := by
  induction l with
  | zero => exact seed_quilt
  | succ l ih =>
    exact (ih (h.cut (by omega)) (fun i hi => g i (by omega))).attach
      (Hem.quilt (g l (by omega))) h.here

end
end PowerSaving.Grove

end OAI
