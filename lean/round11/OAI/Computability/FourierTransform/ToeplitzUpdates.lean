import OAI.Computability.FourierTransform.CirculantUpdates
import OAI.Computability.FourierTransform.ToeplitzIdentities

namespace OAI

/-! Addition of a Toeplitz block by routing through a large enough circulant. -/
namespace PowerSaving.Slant
open Reel Stroke Zone Spectral Finset
noncomputable section

def trail (u a : Zone) (t : ℂ) : Reel :=
  flash (a.slim u.wide) u (fun _ => t)

def slice (a v : Zone) (t : ℂ) : Reel :=
  flash v (a.slim v.wide) (fun _ => t)

def pad (s : ℕ) (t : ℂ) (x : Line) : Line :=
  fun i => if i<s then t*x i else 0

def trim (t : ℂ) (x : Line) : Line := fun i => t*x i

lemma Reads.chain {m n l : ℕ} {f g : Line→Line}
    (h : Reads m n f) (hh : Reads n l g) : Reads m l (g ∘ f) :=
  fun x y hx => hh _ _ (h x y hx)

lemma reads_pad (s n : ℕ) (t : ℂ) : Reads s n (pad s t) := by
  intro x y hx i _
  by_cases h : i<s
  · simp only [pad, ite_eq_left h]
    rw [hx i h]
  · simp [pad, h]

lemma reads_trim (n v : ℕ) (t : ℂ) (hp : v ≤ n) : Reads n v (trim t) :=
  fun _ _ h i hi => congr_arg (t*·) (h i (hi.trans_le hp))

lemma additive_trim (n : ℕ) (t : ℂ) : AdditiveOn n (trim t) :=
  fun x y i _ => mul_add t (x i) (y i)

lemma pad_neg (s : ℕ) (t : ℂ) : pad s (-t) = minusFn (pad s t) := by
  ext x i
  by_cases i<s <;> simp [pad,minusFn, *]

lemma trim_neg (t : ℂ) : trim (-t) = minusFn (trim t) := by
  ext x i
  simp [trim,minusFn]

lemma broader_pad {u a : Zone} {r : Reel} (h : u.wide ≤ a.wide) (t : ℂ)
    (hh : Spill r u (a.slim u.wide) (fun x i => t*x i)) :
    Spill r u a (pad u.wide t) := by
  constructor
  · intro x i hi
    by_cases hq : i<u.wide
    · simp only [pad,ite_eq_left hq]
      exact hh.adds x i hq
    · simp only [pad,ite_eq_right hq,add_zero]
      change r.go x (a.lo+i)=_
      exact hh.keeps x _ (by simp [Zone.has,Zone.slim,hq])
  · intro x i hi
    exact hh.keeps x i fun hg => hi (slim_has a h hg)

lemma broader_trim {u a : Zone} {r : Reel} (t : ℂ)
    (hh : Spill r (a.slim u.wide) u (fun x i => t*x i)) :
    Spill r a u (trim t) := ⟨hh.adds,hh.keeps⟩

section
variable {u a : Zone} (t : ℂ) (h : u.wide ≤ a.wide) (hs : u.Sep a)
include h hs

lemma sound_trail {n : ℕ} (hu : u.Fits n) (ha : a.Fits n) :
    (trail u a t).Sound n :=
  sound_flash (ha.slim h) hu rfl (hs.slim_right h).symm _

lemma sound_slice {n : ℕ} (hu : u.Fits n) (ha : a.Fits n) :
    (slice a u t).Sound n :=
  sound_flash hu (ha.slim h) rfl (hs.slim_right h) _

lemma spill_trail : Spill (trail u a t) u a (pad u.wide t) := by
  unfold trail
  exact broader_pad h _ (spill_flash (u:=a.slim u.wide) (v:=u) rfl (hs.slim_right h).symm
    (fun _ => t))

lemma spill_slice : Spill (slice a u t) a u (trim t) := by
  unfold slice
  exact broader_trim _ (spill_flash (u:=u) (v:=a.slim u.wide) rfl (hs.slim_right h)
    (fun _ => t))

end

def duct (d : ℕ) (r : ℂ) (u a b : Zone) (h : Line) : Reel :=
  cameo (trail u a 1) (eddy d r a b h) (trail u a (-1))
    (eddy d r a b (fun i => -h i))

def well (d : ℕ) (r : ℂ) (u v a b : Zone) (h : Line) : Reel :=
  cameo (duct d r u a b h) (slice b v 1)
    (duct d r u a b (fun i => -h i)) (slice b v (-1))

lemma beats_cameo (a b c d : Reel) :
    (cameo a b c d).beats=a.beats+b.beats+c.beats+d.beats := rfl
lemma beats_duct (d : ℕ) (r : ℂ) (u a b : Zone) (h : Line) :
    (duct d r u a b h).beats=40*d+108 := by
  unfold duct; rw [beats_cameo]; simp_rw [trail,beats_flash,beats_eddy]; omega
lemma beats_well (d : ℕ) (r : ℂ) (u v a b : Zone) (h : Line) :
    (well d r u v a b h).beats=80*d+268 := by
  unfold well; rw [beats_cameo]; simp_rw [beats_duct,slice,beats_flash]; omega

section
variable {d n : ℕ} (r : ℂ) {u a b : Zone} (h : Line)
  (hu : u.wide ≤ a.wide)
  (ha : a.wide=2^d) (hb : b.wide=2^d)
  (hua : u.Sep a) (hab : a.Sep b)

include hu ha hb hua hab

lemma sound_duct (pu : u.Fits n) (pa : a.Fits n) (pb : b.Fits n) :
    (duct d r u a b h).Sound n :=
  sound_cameo _ _ _ _ n (sound_trail _ hu hua pu pa)
    (sound_eddy _ _ ha hb hab pa pb)
    (sound_trail _ hu hua pu pa) (sound_eddy _ _ ha hb hab pa pb)

lemma spill_duct (hr : IsPrimitiveRoot r (2^d)) (hub : u.Sep b) :
    Spill (duct d r u a b h) u b (cyclic (2^d) h ∘ pad u.wide 1) := by
  apply spill_cameo (spill_trail 1 hu hua) (spill_eddy r h ha hb hab hr)
  · rw [← pad_neg]; exact spill_trail _ hu hua
  · rw [← cyclic_neg]; exact spill_eddy r _ ha hb hab hr
  · exact reads_pad _ _ _
  · rw [ha,hb]; exact cyclic_reads _ h
  · rw [hb]; exact cyclic_add _ h
  · exact hub
  · exact hua
  · exact hab

variable {v : Zone} (hv : v.wide ≤ b.wide) (hvb : v.Sep b)
include hv hvb

lemma sound_well (pu : u.Fits n) (pv : v.Fits n) (pa : a.Fits n) (pb : b.Fits n) :
    (well d r u v a b h).Sound n :=
  sound_cameo _ _ _ _ n
    (sound_duct _ _ hu ha hb hua hab pu pa pb) (sound_slice _ hv hvb pv pb)
    (sound_duct _ _ hu ha hb hua hab pu pa pb) (sound_slice _ hv hvb pv pb)

lemma spill_well (hr : IsPrimitiveRoot r (2^d)) (hub : u.Sep b) (huv : u.Sep v) :
    Spill (well d r u v a b h) u v (trim 1 ∘ (cyclic (2^d) h ∘ pad u.wide 1)) := by
  apply spill_cameo (spill_duct _ h hu ha hb hua hab hr hub) (spill_slice 1 hv hvb)
  · have hz : minusFn (cyclic (2^d) h ∘ pad u.wide 1) =
        cyclic (2^d) (fun i => -h i) ∘ pad u.wide 1 := by
      rw [cyclic_neg]
      rfl
    rw [hz]; exact spill_duct _ _ hu ha hb hua hab hr hub
  · rw [← trim_neg]; exact spill_slice _ hv hvb
  · rw [hb]
    exact (reads_pad u.wide _ 1).chain (cyclic_reads _ h)
  · exact reads_trim _ _ _ hv
  · exact additive_trim _ _
  · exact huv
  · exact hub
  · exact hvb.symm

end

-- logical lower Toeplitz between offsets l (source), m (target), in different physical chunks.
def spout (e l m : ℕ) (h : Line) (x : Line) : Line :=
  fun i => ∑ j ∈ range e, rise h (m+i) (l+j)*x j

/-- 2*b slots. k < b for positive or zero displacement. Leave non-required displacements
0 for convenience -- coefficients beyond the supplied span need not be evaluated. -/
def skirt (b e s l m : ℕ) (h : Line) : Line :=
  fun k =>
    if k<b then
      if k<s then rise h (m+k) l else 0
    else
      if 0<s ∧ 2*b-k<e then rise h m (l+(2*b-k)) else 0

lemma skirt_spec (b e s l m : ℕ) (h : Line) (ha : e ≤ b) (hb : s ≤ b) (i j : ℕ)
    (hi : i<s) (hj : j<e) :
    skirt b e s l m h (predAt (2*b) i j)=rise h (m+i) (l+j) := by
  rcases lt_or_ge i j with hp|hp
  · simp only [predAt,ite_eq_right (show ¬j ≤ i by omega),
      skirt,ite_eq_right (show ¬i+2*b-j<b by omega),ite_eq_left (show 0<s ∧ 2*b-(i+2*b-j)<e
      from ⟨by omega,by omega⟩)]
    rw [show m+i=i+m by omega, show l+j=i+(l+(2*b-(i+2*b-j))) by omega, rise_both]
  · simp only [predAt,ite_eq_left hp,
      skirt,ite_eq_left (show i-j<b by omega),ite_eq_left (show i-j<s by omega)]
    rw [show m+i=j+(m+(i-j)) by omega, show l+j=j+l by omega, rise_both]

lemma trim_spout (b e s l m : ℕ) (h : Line) (ha : e ≤ b) (hb : s ≤ b)
    (x : Line) (i : ℕ) (hi : i<s) :
    trim 1 (cyclic (2*b) (skirt b e s l m h) (pad e 1 x)) i=spout e l m h x i := by
  unfold trim cyclic spout
  rw [one_mul]
  let f (j : ℕ) := skirt b e s l m h (predAt (2*b) i j)*pad e 1 x j
  change (∑ j ∈ range (2*b), f j)=_
  have H (j : ℕ) : f (e+j)=0 := by simp [f,pad]
  conv_lhs => rw [show 2*b=e+(2*b-e) by omega, sum_range_add]
  simp only [H,sum_const_zero,add_zero]
  refine sum_congr rfl ?_
  intro j hj
  replace hj := mem_range.mp hj
  simp only [f,skirt_spec b e s l m h ha hb i j hi hj,pad,ite_eq_left hj,one_mul]

lemma reads_spout (e l m s : ℕ) (h : Line) : Reads e s (spout e l m h) := by
  intro x y hp i hi
  exact sum_congr rfl fun j hj => congr_arg (_*·) (hp j (mem_range.mp hj))
lemma additive_spout (e l m s : ℕ) (h : Line) :
    AdditiveOn s (spout e l m h) := by
  intro x y i _
  simp [spout,sum_add_distrib,mul_add]
lemma spout_neg (e l m : ℕ) (h : Line) :
    spout e l m (fun i => -h i) = minusFn (spout e l m h) := by
  have H (i j : ℕ) : rise (fun a => -h a) i j = -rise h i j := by
    by_cases j ≤ i <;> simp [rise, *]
  ext x i
  simp [spout,H,minusFn]

def bore (k : ℕ) (r : ℂ) (u v a b : Zone) (l m : ℕ) (h : Line) : Reel :=
  well (k+1) r u v a b (skirt (2^k) u.wide v.wide l m h)

lemma beats_bore (k : ℕ) (r : ℂ) (u v a b : Zone) (l m : ℕ) (h : Line) :
    (bore k r u v a b l m h).beats=80*k+348 := by
  rw [bore,beats_well]; omega

section
variable {k n : ℕ} (r : ℂ) {u v a b : Zone} (l m : ℕ) (h : Line)
  (hu : u.wide ≤ 2^k) (hv : v.wide ≤ 2^k)
  (ha : a.wide=2^(k+1)) (hb : b.wide=2^(k+1))
  (hua : u.Sep a) (hab : a.Sep b) (hvb : v.Sep b)

include hu hv ha hb hua hab hvb

lemma sound_bore (pu : u.Fits n) (pv : v.Fits n) (pa : a.Fits n) (pb : b.Fits n) :
    (bore k r u v a b l m h).Sound n :=
  sound_well r _ (by rw [ha,pow_succ]; omega) ha hb hua hab
    (by rw [hb,pow_succ]; omega) hvb pu pv pa pb

lemma spill_bore (hr : IsPrimitiveRoot r (2^(k+1))) (hub : u.Sep b) (huv : u.Sep v) :
    Spill (bore k r u v a b l m h) u v (spout u.wide l m h) := by
  unfold bore
  refine (spill_well r _ (by rw [ha,pow_succ]; omega) ha hb hua hab
    (by rw [hb,pow_succ]; omega) hvb hr hub huv).congr ?_
  intro x i hi
  simp only [Function.comp_apply,pow_succ']
  exact trim_spout _ _ _ _ _ _ hu hv x i hi

end
end
end PowerSaving.Slant

end OAI
