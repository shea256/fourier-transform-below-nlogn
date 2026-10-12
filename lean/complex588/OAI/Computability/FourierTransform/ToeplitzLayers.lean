import OAI.Computability.FourierTransform.MeasuredFit

namespace OAI

/-! Dyadic exact-width layers for lower triangular Toeplitz. -/
namespace PowerSaving.Slant
open Reel Stroke Zone Spectral Finset
noncomputable section

def reachSize (e : ℕ) : ℕ :=
  if e<4 then let p := 2^e; p*(p*(p*26))
  else 16*(16*(16*(4*(80*(e-4)+348))))

def bridgeSpan (e w : ℕ) (h g r : Line) : Reel :=
  if e<4 then sand (2^e) w h g else reef (e-4) (r (e-4+1)) w h g

def Springs (e : ℕ) (r : Line) : Prop :=
  ∀ i ≤ e, IsPrimitiveRoot (r i) (2^i)

lemma beats_span (e w : ℕ) (h g r : Line) :
    (bridgeSpan e w h g r).beats = reachSize e := by
  unfold bridgeSpan reachSize; split
  · exact beats_sand _ _ _ _
  · exact beats_reef _ _ _ _ _

lemma desc_num (e : ℕ) (h : ¬ e<4) : 2^e=16*(2:ℕ)^(e-4) := by
  have hk : (2:ℕ)^e=2^(4+(e-4)) := by rw [show 4+(e-4)=e by omega]
  rw [hk,pow_add]; norm_num

lemma sound_span (e w : ℕ) (h g r : Line) :
    (bridgeSpan e w h g r).Sound (2^e+w) := by
  unfold bridgeSpan
  split
  · exact sound_sand _ _ _ _
  · rename_i hk
    rw [desc_num e hk]
    exact sound_reef _ _ _ _ _

lemma spill_span (e w : ℕ) (h g r : Line) (hw : w ≤ 2^e) (hr : Springs (e+1) r) :
    Spill (bridgeSpan e w h g r) (initial (2^e)) (coast (2^e) w) (surf (2^e) h g) := by
  unfold bridgeSpan; split
  · exact spill_sand (2^e) w h g hw
  · rename_i hk
    rw [desc_num e hk] at *
    exact spill_reef _ _ _ _ _ hw (hr _ (by omega))

lemma reach_le (e : ℕ) :
    reachSize e ≤ 10000000*(e+1) := by
  unfold reachSize; split
  · rename_i h
    interval_cases e <;> norm_num
  · omega

def chorus : ℕ → ℕ
  | 0 => 1
  | e+1 => chorus e + reachSize e

def hoop (e v : ℕ) (h g r : Line) (a b : Reel) : Reel :=
  let n := 2^e
  (parallel (min n v) a b).stack
    (if n<v then bridgeSpan e (v-n) h g r else wait (reachSize e))

def harp (h g r : Line) : ℕ → ℕ → Reel
  | 0,v => swatch v (fun _ => h 0)
  | e+1,v => hoop e v h g r (harp h g r e (min (2^e) v)) (harp h g r e (v-2^e))

lemma beats_hoop (e v : ℕ) (h g r : Line) (a b : Reel) :
    (hoop e v h g r a b).beats=a.beats+reachSize e := by
  unfold hoop; dsimp only
  split
  · exact congr_arg (a.beats+·) (beats_span _ _ _ _ _)
  · rfl

lemma beats_harp (h g r : Line) (e v : ℕ) :
    (harp h g r e v).beats=chorus e := by
  induction e generalizing v with
  | zero => rfl
  | succ e ih =>
    rw [harp,beats_hoop,ih,chorus]

lemma chorus_le (e : ℕ) :
    chorus e ≤ 10000000*(e+1)^2 := by
  induction e with
  | zero => simp [chorus]
  | succ e ih =>
    rw [chorus]
    have := reach_le e
    nlinarith

lemma sound_hoop (e v : ℕ) (h g r : Line) (a b : Reel) (hl : a.beats=b.beats)
    (ha : a.Sound (min (2^e) v)) (hb : b.Sound (v-2^e)) :
    (hoop e v h g r a b).Sound v := by
  have hs := ha.parallel hb hl
  have hp : min (2^e) v + (v-2^e)=v := by omega
  rw [hp] at hs
  unfold hoop; dsimp only
  apply hs.stack
  split
  · have H := sound_span e (v-2^e) h g r
    rwa [show 2^e+(v-2^e)=v by omega] at H
  · exact sound_wait _ _

lemma branch_smaller (e v : ℕ) (hv : v ≤ 2^(e+1)) : v-2^e ≤ 2^e := by
  rw [pow_succ,mul_two] at hv; omega

lemma sound_harp (h g r : Line) (e v : ℕ) (hv : v ≤ 2^e) :
    (harp h g r e v).Sound v := by
  induction e generalizing v with
  | zero => exact sound_swatch _ _
  | succ e ih =>
    rw [harp]
    apply sound_hoop
    · rw [beats_harp,beats_harp]
    · exact ih _ (min_le_left ..)
    · exact ih _ (branch_smaller e v hv)

lemma spill_after (v w : ℕ) (a b c : Reel) (h : Line) (hz : h 0 ≠ 0)
    (ha : a.Sound v) (hl : a.beats=b.beats)
    (fa : Flows a v (stencil v h)) (fb : Flows b w (stencil w h))
    (hh : Spill c (initial v) (coast v w) (surf v h (recoil h))) :
    Flows ((parallel v a b).stack c) (v+w) (stencil (v+w) h) := by
  intro x i hi
  let y := (parallel v a b).go x
  have A (j : ℕ) (hj : j<v) : y j=stencil v h x j :=
    (parallel_left v a b ha x j hj).trans (fa x j hj)
  have H := stencil_congr v (recoil h) (x:=(initial v).peek y) (y:=stencil v h x)
    (fun j hj => by simpa only [initial,Zone.peek,Stroke.drift,zero_add] using A j hj)
  rw [go_stack]
  change c.go y i=_
  rcases lt_or_ge i v with hp|hp
  · have hn : ¬ (coast v w).has i := by
      intro hh
      have gg : v ≤ i := hh.1; omega
    rw [hh.keeps y i hn,A i hp,stencil_left _ _ _ _ _ hp]
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hp
    have hj : j<w := by omega
    have hs := hh.adds y j hj
    change c.go y (v+j) = y (v+j)+stencil _ h _ _ at hs
    rw [hs,H,stencil_right]
    have hz' := stencil_congr v h (x:=stencil v (recoil h) (stencil v h x))
      (y:=x) (recoil_back v h x hz)
    have hh' : y (v+j)=stencil w h (drift v x) j := by
      change drift v ((parallel v a b).go x) j=_
      rw [parallel_right v a b hl, fb (drift v x) j hj]
    rw [hz',hh']
    exact add_comm _ _

lemma flows_hoop (e v : ℕ) (h r : Line) (hz : h 0 ≠ 0)
    (a b : Reel) (hl : a.beats=b.beats) (hv : v ≤ 2^(e+1))
    (ha : a.Sound (min (2^e) v))
    (fa : Flows a (min (2^e) v) (stencil (min (2^e) v) h))
    (fb : Flows b (v-2^e) (stencil (v-2^e) h)) (hr : Springs (e+1) r) :
    Flows (hoop e v h (recoil h) r a b) v (stencil v h) := by
  unfold hoop; dsimp only
  split
  · rename_i hk
    have hg : min (2^e) v=2^e := by omega
    rw [hg] at ha fa ⊢
    have ht := spill_after (2^e) (v-2^e) a b _ h hz ha hl fa fb
      (spill_span e _ h (recoil h) r (branch_smaller e v hv) hr)
    rwa [show 2^e+(v-2^e)=v by omega] at ht
  · have hg : min (2^e) v=v := by omega
    rw [hg] at ha fa ⊢
    intro x i hi
    rw [go_stack, go_wait, parallel_left v a b ha x i hi]
    exact fa x i hi

lemma flows_harp (h r : Line) (e v : ℕ) (hv : v ≤ 2^e) (hz : h 0 ≠ 0)
    (hr : Springs e r) :
    Flows (harp h (recoil h) r e v) v (stencil v h) := by
  induction e generalizing v with
  | zero =>
    intro x i hi
    rw [harp,go_swatch v _ x i hi]
    have h1 : v=1 := by rw [pow_zero] at hv; omega
    simp only [h1, show i=0 by omega, stencil, sum_range_one,rise,le_refl,↓reduceIte,
      Nat.sub_self]
  | succ e ih =>
    rw [harp]
    have g : Springs e r := fun i hi => hr i (by omega)
    apply flows_hoop _ _ _ _ hz _ _ _ hv _ _ _ hr
    · rw [beats_harp,beats_harp]
    · exact sound_harp _ _ _ _ _ (min_le_left ..)
    · exact ih _ (min_le_left ..) g
    · exact ih _ (branch_smaller _ _ hv) g

end
end PowerSaving.Slant

end OAI
