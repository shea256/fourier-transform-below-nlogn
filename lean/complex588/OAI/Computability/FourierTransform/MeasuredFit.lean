import OAI.Computability.FourierTransform.ChunkCompiler

namespace OAI

namespace PowerSaving.Slant
open Reel Stroke Zone Spectral Finset
noncomputable section

def far (b j : ℕ) := if j<8 then 8*b else 0

def trestle (b j : ℕ) : Zone := ⟨far b j, b⟩
def barrier (b j : ℕ) : Zone := ⟨far b j + b, 2*b⟩
def lockBay (b j : ℕ) : Zone := ⟨far b j + 3*b,2*b⟩

structure Wharf (p : ℕ) (u v z l m : Zone) : Prop where
  fitsU : u.Fits p
  fitsV : v.Fits p
  fitsZ : z.Fits p
  fitsL : l.Fits p
  fitsM : m.Fits p
  uz : u.Sep z
  ul : u.Sep l
  um : u.Sep m
  lm : l.Sep m
  zl : z.Sep l
  zm : z.Sep m
  uv : u.Sep v
  zv : z.Sep v
  vm : v.Sep m

lemma wharf (b j w s : ℕ) (hj : j<16) :
    Wharf (16*b+w) (quay b j) (jetty (16*b) w b s)
      (trestle b j) (barrier b j) (lockBay b j) := by
  let o := far b j
  have h := quay_fits 16 b j w hj
  have ho : o+8*b ≤ 16*b := by unfold o far; split <;> omega
  have bed (v t : ℕ) (hv : o ≤ v) (ht : v+t ≤ o+8*b) :
      (quay b j).Sep ⟨v,t⟩ := by
    rcases lt_or_ge j 8 with g|g
    · apply sep_of
      change j*b+b ≤ v
      have H := Nat.mul_le_mul_right b g
      change (j+1)*b ≤ _ at H; rw [add_mul,one_mul] at H
      simp only [o,far,ite_eq_left g] at hv
      omega
    · apply Zone.Sep.symm; apply sep_of
      change v+t ≤ j*b
      have H := Nat.mul_le_mul_right b g
      simp only [o,far,ite_eq_right (by omega : ¬j<8)] at ht; omega
  change Wharf (16*b+w) _ _ ⟨o,b⟩ ⟨o+b,2*b⟩ ⟨o+3*b,2*b⟩
  refine ⟨h,jetty_fits (16*b) w b s,
    fits_of _ _ (by change o+b ≤ _; omega),fits_of _ _ (by change o+b+2*b ≤ _; omega),
    fits_of _ _ (by change o+3*b+2*b ≤ _; omega),bed _ _ le_rfl (by omega),bed _ _ (by omega)
    (by omega),bed _ _ (by omega) (by omega),
    sep_of _ _ (by change o+b+2*b ≤ o+3*b; omega), sep_of _ _ le_rfl,
    sep_of _ _ (by change o+b ≤ o+3*b; omega),quay_sep 16 w b s j hj, ?_, ?_⟩
  · apply sep_of
    change o+b ≤ 16*b+_
    omega
  · apply Zone.Sep.symm; apply sep_of
    change o+3*b+2*b ≤ 16*b+_
    omega

def cliff (k : ℕ) (r : ℂ) (u v z l m : Zone) (b e y : ℕ) (h g : Line) : Reel :=
  cameo (bore k r u z l m b e g) (bore k r z v l m e y h)
    (bore k r u z l m b e (fun i => -g i)) (bore k r z v l m e y (fun i => -h i))

structure Slips (k : ℕ) (u v z l m : Zone) : Prop where
  uw : u.wide ≤ 2^k
  vw : v.wide ≤ 2^k
  zw : z.wide ≤ 2^k
  lw : l.wide=2^(k+1)
  mw : m.wide=2^(k+1)

lemma slips (k j w s : ℕ) :
    let b := 2^k
    Slips k (quay b j) (jetty (16*b) w b s) (trestle b j)
      (barrier b j) (lockBay b j) := by
  intro b
  refine ⟨le_rfl,min_le_left _ _,le_rfl,(pow_succ' _ _).symm,(pow_succ' _ _).symm⟩

section
variable {u v z l m : Zone} {k n : ℕ} (r : ℂ) (b e y : ℕ) (h g : Line)
  (H : Slips k u v z l m) (hf : Wharf n u v z l m)

include H hf

lemma sound_cliff :
    (cliff k r u v z l m b e y h g).Sound n := by
  have ha (g : Line) := sound_bore r b e g H.uw H.zw H.lw H.mw hf.ul hf.lm hf.zm
    hf.fitsU hf.fitsZ hf.fitsL hf.fitsM
  have hb (g : Line) := sound_bore r e y g H.zw H.vw H.lw H.mw hf.zl hf.lm hf.vm
    hf.fitsZ hf.fitsV hf.fitsL hf.fitsM
  exact sound_cameo _ _ _ _ n (ha _) (hb _) (ha _) (hb _)

lemma spill_cliff (hr : IsPrimitiveRoot r (2^(k+1))) :
    Spill (cliff k r u v z l m b e y h g) u v
      (spout z.wide e y h ∘ spout u.wide b e g) := by
  have ha (g : Line) := spill_bore r b e g H.uw H.zw H.lw H.mw hf.ul hf.lm hf.zm
    hr hf.um hf.uz
  have hb (h : Line) := spill_bore r e y h H.zw H.vw H.lw H.mw hf.zl hf.lm hf.vm
    hr hf.zm hf.zv
  apply spill_cameo (ha g) (hb h)
  · rw [← spout_neg]; exact ha _
  · rw [← spout_neg]; exact hb _
  · exact reads_spout _ b e _ g
  · exact reads_spout _ e y _ h
  · exact additive_spout _ e y _ h
  · exact hf.uv
  · exact hf.uz
  · exact hf.zv

end

def gravel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) : Reel :=
  let b := 2^k
  let p := 16*b
  cliff k r (quay b j) (jetty p w b s) (trestle b j) (barrier b j)
    (lockBay b j) (j*b) (c*b) (p+s*b) h g

def reef (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) : Reel :=
  riprap (gravel k r w h g) 16

lemma beats_gravel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) :
    (gravel k r w h g s c j).beats=4*(80*k+348) := by
  unfold gravel cliff
  dsimp only
  simp only [beats_cameo,beats_bore]; omega
lemma beats_reef (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) :
    (reef k r w h g).beats=16*(16*(16*(4*(80*k+348)))) :=
  beats_riprap _ _ _ (fun _ _ _ _ _ _ => beats_gravel k _ _ _ _ _ _ _)

lemma sound_gravel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) (hj : j<16) :
    (gravel k r w h g s c j).Sound (16*2^k+w) :=
  sound_cliff r (j*_ ) (c*_) (16*2^k+s*_) h g (slips k j w s) (wharf (2^k) j w s hj)
lemma sound_reef (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) :
    (reef k r w h g).Sound (16*2^k+w) :=
  sound_riprap _ _ _ (fun _ _ _ _ j hj => sound_gravel k _ _ _ _ _ _ j hj)

lemma spill_gravel (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (s c j : ℕ) (hj : j<16)
    (hr : IsPrimitiveRoot r (2^(k+1))) :
    Spill (gravel k r w h g s c j) (quay (2^k) j)
      (jetty (16*2^k) w (2^k) s) (wave (16*2^k) (2^k) s c j h g) :=
  spill_cliff r (j*2^k) (c*2^k) (16*2^k+s*2^k) h g (slips k j w s)
    (wharf (2^k) j w s hj) hr
lemma spill_reef (k : ℕ) (r : ℂ) (w : ℕ) (h g : Line) (hw : w ≤ 16*2^k)
    (hr : IsPrimitiveRoot r (2^(k+1))) :
    Spill (reef k r w h g) (initial (16*2^k)) (coast (16*2^k) w) (surf (16*2^k) h g) :=
  spill_riprap _ 16 _ w h g (by positivity) hw
    (fun s _ c _ j hj => spill_gravel k r w h g s c j hj hr)

-- b=1 small cross
def speck (p w : ℕ) (h g : Line) (s c j : ℕ) : Reel :=
  if s<w then flash (jetty p w 1 s) (quay 1 j) (fun _ => rise h (p+s) c*rise g c j)
  else wait 26

def sand (p w : ℕ) (h g : Line) : Reel := riprap (speck p w h g) p

lemma beats_speck (p w : ℕ) (h g : Line) (s c j : ℕ) :
    (speck p w h g s c j).beats=26 := by unfold speck; split; exact beats_flash _ _ _; rfl
lemma beats_sand (p w : ℕ) (h g : Line) : (sand p w h g).beats=p*(p*(p*26)) :=
  beats_riprap _ _ _ fun _ _ _ _ _ _ => beats_speck _ _ _ _ _ _ _

lemma quay_jet (p w j s : ℕ) (hj : j<p) :
    (jetty p w 1 s).Sep (quay 1 j) := by
  simpa only [mul_one] using (quay_sep p w 1 s j hj).symm
lemma sound_speck (p w : ℕ) (h g : Line) (s c j : ℕ) (hj : j<p) :
    (speck p w h g s c j).Sound (p+w) := by
  unfold speck; split
  · rename_i hs
    refine sound_flash (jetty_fits p w 1 s) ?_ ?_ (quay_jet p w j s hj) _
    · simpa only [mul_one] using quay_fits p 1 j w hj
    · change min 1 (w-s*1) = 1; omega
  · exact sound_wait 26 _
lemma sound_sand (p w : ℕ) (h g : Line) : (sand p w h g).Sound (p+w) :=
  sound_riprap _ _ _ fun _ _ _ _ j hj => sound_speck _ _ _ _ _ _ j hj

lemma spill_speck (p w : ℕ) (h g : Line) (s c j : ℕ) (hj : j<p) :
    Spill (speck p w h g s c j) (quay 1 j) (jetty p w 1 s) (wave p 1 s c j h g) := by
  unfold speck
  split
  · rename_i hs
    have hh : (jetty p w 1 s).wide = (quay 1 j).wide := by
      change min 1 (w-s*1)=1; omega
    refine (spill_flash hh (quay_jet p w j s hj) _).congr ?_
    intro x i hi
    rw [hh] at hi
    change i<1 at hi
    have h0 : i=0 := by omega
    simp only [wave,Function.comp_apply,h0,spout,sum_range_one,mul_one,add_zero,mul_assoc]
  · rename_i hs
    constructor
    · intro x i hi
      change i < min 1 (w-s*1) at hi; omega
    · intro x i hi; rw [go_wait]
lemma spill_sand (p w : ℕ) (h g : Line) (hw : w ≤ p) :
    Spill (sand p w h g) (initial p) (coast p w) (surf p h g) := by
  have hh s (_ : s<p) c (_ : c<p) j (hj : j<p) :
      Spill (speck p w h g s c j) (quay 1 j) (jetty (p*1) w 1 s) (wave (p*1) 1 s c j h g) :=
    by simpa only [mul_one] using spill_speck p w h g s c j hj
  unfold sand
  simpa only [mul_one] using
    spill_riprap (speck p w h g) p 1 w h g (by omega) (by omega) hh

end
end PowerSaving.Slant

end OAI
