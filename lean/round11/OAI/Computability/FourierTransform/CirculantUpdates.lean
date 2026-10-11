import OAI.Computability.FourierTransform.BinaryFFT

namespace OAI

/-! Circulant addition between disjoint dirty intervals by two transformed words and inverses. -/
namespace PowerSaving.Slant
open Reel Zone Stroke Spectral Finset
noncomputable section

def eddy (d : ℕ) (r : ℂ) (u v : Zone) (h : Line) : Reel :=
  let p := pulse d r; let b := backPulse d r
  let f := flash v u (freq (2^d) r h)
  ((((atBase u.lo p).stack (atBase v.lo p)).stack f).stack (atBase u.lo b)).stack
    (atBase v.lo b)

lemma beat_mounted (p : ℕ) (r : Reel) : (atBase p r).beats=r.beats := rfl

lemma beats_eddy (d : ℕ) (r : ℂ) (u v : Zone) (h : Line) :
    (eddy d r u v h).beats=20*d+28 := by
  unfold eddy; dsimp only
  simp only [stack,beat_mounted,beats_pulse,beats_flash,beats_back]
  omega

lemma Zone.Fits.end_le {v : Zone} {n : ℕ} (hv : v.Fits n) (hp : 0<v.wide) :
    v.lo+v.wide ≤ n := by
  have := hv _ (v.inside (by omega : v.wide-1<v.wide))
  omega

lemma Zone.Fits.mount {v : Zone} {n : ℕ} (hv : v.Fits n) (hp : 0<v.wide)
    {r : Reel} (h : r.Sound v.wide) :
    (atBase v.lo r).Sound n :=
  (h.atBase _).wider (hv.end_le hp)

section
variable {u v : Zone} {d n : ℕ} (r : ℂ) (h : Line) (hu : u.wide=2^d)
  (hv : v.wide=2^d) (hs : u.Sep v)

include hu hv hs
theorem sound_eddy (pu : u.Fits n) (pv : v.Fits n) :
    (eddy d r u v h).Sound n := by
  have HU {a : Reel} (h : a.Sound (2^d)) :=
    pu.mount (by rw [hu]; positivity) (show a.Sound u.wide by rwa [hu])
  have HV {a : Reel} (h : a.Sound (2^d)) :=
    pv.mount (by rw [hv]; positivity) (show a.Sound v.wide by rwa [hv])
  have hq : v.wide=u.wide := hv.trans hu.symm
  exact ((((HU (sound_pulse d r)).stack (HV (sound_pulse d r))).stack
    (sound_flash pv pu hq hs.symm _)).stack (HU (sound_back d r))).stack
    (HV (sound_back d r))

theorem spill_eddy (hr : IsPrimitiveRoot r (2^d)) :
    Spill (eddy d r u v h) u v (cyclic (2^d) h) := by
  let q := 2^d
  let f := freq q r
  let g := fun (x : Line) (i : ℕ) => (q:ℂ)⁻¹ * freq q r⁻¹ x i
  let p := pulse d r; let b := backPulse d r
  let pa := atBase u.lo p; let pb := atBase v.lo p
  let ba := atBase u.lo b; let bb := atBase v.lo b
  let fl := flash v u (f h)
  have hq : v.wide=u.wide := hv.trans hu.symm
  have h1 : Retrace pa u f := atBase_retrace (by rw [hu]; exact sound_pulse d _)
    (by rw [hu]; exact flows_pulse d _ hr)
  have h2 : Retrace pb v f := atBase_retrace (by rw [hv]; exact sound_pulse d _)
    (by rw [hv]; exact flows_pulse d _ hr)
  have h4 : Retrace ba u g := atBase_retrace (by rw [hu]; exact sound_back d _)
    (by rw [hu]; exact flows_back d _ hr)
  have h5 : Retrace bb v g := atBase_retrace (by rw [hv]; exact sound_back d _)
    (by rw [hv]; exact flows_back d _ hr)
  have h3 : Spill fl u v (fun x i => f h i*x i) := spill_flash hq hs.symm (f h)
  have gf (x y : Line) (i : ℕ) (hi : i<q) (H : ∀ i<q, x i=f y i) :
      g x i=y i := by
    unfold g
    rw [freq_congr H]
    exact freq_inv hr y i hi
  change u.wide=q at hu; change v.wide=q at hv
  have clean (x : Line) (i : ℕ) (hi : i<u.wide) :
      u.peek ((eddy d r u v h).go x) i=u.peek x i := by
    change u.peek (((((pa.stack pb).stack fl).stack ba).stack bb).go x) i=_
    simp only [go_stack]
    rw [retrace_preserve h5 hs _ i hi,h4.draws _ i hi]
    refine gf _ _ i (hu ▸ hi) ?_
    intro j hj
    have hk : j<u.wide := hu.symm ▸ hj
    rw [h3.preserves hs _ j hk,retrace_preserve h2 hs _ j hk,h1.draws _ j hk]
  constructor
  · intro x i hi
    change v.peek (((((pa.stack pb).stack fl).stack ba).stack bb).go x) i=_
    simp only [go_stack]
    rw [h5.draws _ i hi]
    refine gf _ (v.peek x + cyclic q h (u.peek x)) i (hv ▸ hi) ?_
    intro j hj
    have hk : j<v.wide := hv.symm ▸ hj
    have hp : j<u.wide := hq ▸ hk
    rw [retrace_preserve h4 hs.symm _ j hk,h3.adds _ j hk,h2.draws _ j hk]
    rw [retrace_preserve h2 hs _ j hp, h1.draws _ j hp]
    have hx : freq q r (v.peek (pa.go x)) = f (v.peek x) := freq_congr
      (fun j hj => retrace_preserve h1 hs.symm _ j (hv.symm ▸ hj)) r
    unfold f
    rw [hx, freq_add]
    exact congr_arg (freq q r (v.peek x) j + ·) (freq_cyclic hr.pow_eq_one _ _ _).symm
  · intro x i hi
    by_cases hh : u.has i
    · have H := clean x (i-u.lo) (u.enter hh)
      simpa [Zone.peek,Stroke.drift,u.identify hh] using H
    · change ((((pa.stack pb).stack fl).stack ba).stack bb).go x i=_
      simp only [go_stack]
      rw [h5.waits _ i hi,h4.waits _ i hh,h3.keeps _ i hi,h2.waits _ i hi,h1.waits _ i hh]

end

lemma cyclic_reads (v : ℕ) (h : Line) : Reads v v (cyclic v h) := by
  intro x y hxy i hi
  unfold cyclic
  exact sum_congr rfl fun _ hj => congr_arg (_*·) (hxy _ (mem_range.mp hj))

lemma cyclic_add (v : ℕ) (h : Line) : AdditiveOn v (cyclic v h) := by
  intro x y i _
  simp [cyclic,mul_add,sum_add_distrib]

lemma cyclic_neg (v : ℕ) (h : Line) :
    cyclic v (fun i => -h i) = minusFn (cyclic v h) := by
  ext x i
  simp [cyclic,minusFn]

end
end PowerSaving.Slant

end OAI
