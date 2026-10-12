import OAI.Computability.FourierTransform.ToeplitzLayers

namespace OAI

/-! Fourier layer word. Correct on each axis at exact width, even when coincident
intermediate wires hold arbitrary data. -/
namespace PowerSaving.Slant
open Reel Stroke Spectral Zone Matrix Finset
noncomputable section

def Creates (p : Reel) (n : ℕ) (M : RootMat n) : Prop :=
  ∀ x, front n (p.go x)=M *ᵥ front n x

lemma Creates.stack {p q : Reel} {n} {M N : RootMat n}
    (h : Creates p n M) (g : Creates q n N) :
    Creates (p.stack q) n (N*M) :=
  fun x => by rw [go_stack,g,h,Matrix.mulVec_mulVec]

lemma creates_swatch (n : ℕ) (f : Line) :
    Creates (swatch n f) n (fade n f) := by
  intro x; ext i
  change (swatch n f).go x i.val = _
  rw [go_swatch n f x _ i.isLt]
  change f i.val*x i.val=∑ j : Fin n, Matrix.diagonal (front n f) i j*front n x j
  simp [ite_mul, diagonal_apply,front]

lemma front_flows {p : Reel} {n : ℕ} {f : Line→Line} (h : Flows p n f) (x : Line) :
    front n (p.go x)=front n (f x) :=
  funext fun i => h x _ i.isLt

def echo (n : ℕ) : Reel := lace n fun i => n-1-i

lemma sound_echo (n : ℕ) : (echo n).Sound n :=
  sound_lace _ _ (fun i hi => by omega)
lemma echo_go (n : ℕ) (i : ℕ) (hi : i<n) (x : Line) :
    (echo n).go x i=x (n-1-i) := go_lace n _ x i hi

def coda (n : ℕ) (u : Reel) : Reel := ((echo n).stack u).stack (echo n)

lemma sound_coda (n : ℕ) (u : Reel) (h : u.Sound n) : (coda n u).Sound n :=
  ((sound_echo n).stack h).stack (sound_echo n)

lemma creep_coda (n : ℕ) (u : Reel) (h : Line) (hh : Flows u n (stencil n h)) :
    Flows (coda n u) n (creep n h) := by
  intro x i hi
  unfold coda
  rw [go_stack,go_stack,echo_go n i hi,hh _ _ (by omega)]
  exact (congrFun (stencil_congr n h (x:=(echo n).go x) (y:=fun j => x (n-1-j))
    (fun j hj => echo_go n j hj x)) _).trans (stencil_reversed n h x i hi)

def voices (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((swatch n (roof u)).stack p).stack (swatch n (gap u))

def repeatV (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((swatch n (gap u)).stack (coda n p)).stack (swatch n (roof u))

def ode (n : ℕ) (u : ℂ) (p : Reel) : Reel :=
  ((repeatV n u p).stack (swatch n (fun i => (cog u i)⁻¹))).stack (voices n u p)

def ballad (n : ℕ) (e : ℕ) (u : ℂ) (r : Line) : Reel :=
  let h := floorH u
  ode n u (harp h (recoil h) r e n)

lemma sound_ode (n : ℕ) (u : ℂ) (p : Reel) (h : p.Sound n) : (ode n u p).Sound n :=
  ((((sound_swatch n _).stack (sound_coda n p h)).stack (sound_swatch n _)).stack
    (sound_swatch n _)).stack (((sound_swatch n _).stack h).stack (sound_swatch n _))

lemma beats_ode (n : ℕ) (u : ℂ) (p : Reel) :
    (ode n u p).beats=2*p.beats+7 := by
  change 1+(1+p.beats+1)+1+1+(1+p.beats+1)=_
  omega

lemma fade_flip (n : ℕ) (d : Line) : (fade n d)ᵀ = fade n d := by
  ext i j
  rcases eq_or_ne i j with rfl|h <;> simp [fade, eq_comm, *]

lemma creates_voices (n : ℕ) (u : ℂ) (p : Reel) (h : Flows p n (stencil n (floorH u))) :
    Creates (voices n u p) n (steps n u) := by
  have hp : Creates p n (stairs n (floorH u)) :=
    fun x => (front_flows h x).trans (front_stencil _ _ x)
  have H := ((creates_swatch n (roof u)).stack hp).stack (creates_swatch n (gap u))
  rw [steps,Matrix.mul_assoc]
  exact H

lemma creates_repeatV (n : ℕ) (u : ℂ) (p : Reel) (h : Flows p n (stencil n (floorH u))) :
    Creates (repeatV n u p) n (steps n u)ᵀ := by
  have hp : Creates (coda n p) n (stairs n (floorH u))ᵀ :=
    fun x => (front_flows (creep_coda n p _ h) x).trans (front_creep _ _ x)
  have H := ((creates_swatch n (gap u)).stack hp).stack (creates_swatch n (roof u))
  rw [steps,transpose_mul,transpose_mul,fade_flip,fade_flip]
  exact H

lemma creates_ode (n : ℕ) (u : ℂ) (p : Reel) (h : Flows p n (stencil n (floorH u)))
    (hu : IsPrimitiveRoot u n) :
    Creates (ode n u p) n (winds n u) := by
  have H := ((creates_repeatV n u p h).stack (creates_swatch n (fun i => (cog u i)⁻¹))).stack
    (creates_voices n u p h)
  rw [winds_reduction n u hu, Matrix.mul_assoc]
  exact H

lemma sound_ballad (n e : ℕ) (u : ℂ) (r : Line) (h : n ≤ 2^e) :
    (ballad n e u r).Sound n :=
  sound_ode n u _ (sound_harp _ _ r e n h)

lemma creates_ballad (n e : ℕ) (u : ℂ) (r : Line) (h : n ≤ 2^e) (hr : Springs e r)
    (hu : IsPrimitiveRoot u n) :
    Creates (ballad n e u r) n (winds n u) :=
  creates_ode _ _ _ (flows_harp _ _ _ _ h (by simp [floorH,gap]) hr) hu

def score (e : ℕ) := 2*chorus e+7

lemma beats_ballad (n e : ℕ) (u : ℂ) (r : Line) :
    (ballad n e u r).beats=score e := by
  unfold ballad
  dsimp only; rw [beats_ode,beats_harp]; rfl

lemma score_le (e : ℕ) : score e ≤ 20000000*(e+1)^2+7 := by
  have := chorus_le e
  unfold score; omega

end
end PowerSaving.Slant

end OAI
