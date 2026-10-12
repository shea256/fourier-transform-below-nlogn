import OAI.Computability.FourierTransform.IntervalEffects

namespace OAI
/-! Word primitives across equal disjoint intervals. Uniform shear realizations. -/
namespace PowerSaving.Slant

open Zone Reel Stroke Spectral Binary Complex
noncomputable section

/- aligned spells with coordinates u and v -/
def shade (u v : Zone) (f g : Line) : Reel :=
  tick ⟨id, (fun i => if u.has i then f (i-u.lo) else if v.has i then g (i-v.lo)
          else 1),id⟩

def jumps (u v : Zone) (i : ℕ) :=
  if u.has i then v.lo+(i-u.lo)
  else if v.has i then u.lo+(i-v.lo) else i

def snap (u v : Zone) : Reel := tick ⟨id,fun _ => 1,jumps u v⟩

theorem sound_shade {u v : Zone} {f g : Line} {n : ℕ} (h : u.Fits n) (k : v.Fits n) :
    (shade u v f g).Sound n := by
  apply Reel.sound_tick
  refine ⟨fun _ hi => hi,fun _ hi => hi,fun _ => rfl,fun _ _ => rfl,
    fun _ _ => rfl,fun i hi => ?_⟩
  exact (ite_eq_right_iff.mpr fun hu => by
    have := h _ hu; omega).trans (ite_eq_right (fun hv => by have := k _ hv; omega))

lemma jumps_u {u v : Zone} {i} (h : i<u.wide) :
    jumps u v (u.lo+i)=v.lo+i := by simp [jumps,u.inside h]

lemma jumps_v {u v : Zone} (h : u.Sep v) {i} (g : i<v.wide) :
    jumps u v (v.lo+i)=u.lo+i := by
  simp [jumps, v.inside g, h.symm _ (v.inside g)]

lemma sound_snap {u v : Zone} {n : ℕ} (h : u.Fits n) (g : v.Fits n)
    (hv : u.wide=v.wide) (hw : u.Sep v) : (snap u v).Sound n := by
  have H1 (i : ℕ) (hi : u.has i) : jumps u v i=v.lo+(i-u.lo) := by rw [jumps,ite_eq_left hi]
  have H2 (i : ℕ) (hi : v.has i) : jumps u v i=u.lo+(i-v.lo) := by
    rw [jumps,ite_eq_right (hw.symm _ hi), ite_eq_left hi]
  apply sound_tick
  refine ⟨fun i hi => hi, fun i hi => ?_, fun i => ?_, fun i hi => rfl,fun i hi => ?_,
    fun i hi => rfl⟩
  · change jumps u v i<n
    by_cases hk : u.has i
    · rw [H1 i hk]; exact g _ (v.inside (hv ▸ u.enter hk))
    by_cases hk' : v.has i
    · rw [H2 i hk']; exact h _ (u.inside (hv.symm ▸ v.enter hk')) -- dep rewrite?
    · simpa only [jumps,ite_eq_right hk,ite_eq_right hk']
  · change jumps u v (jumps u v i)=i
    by_cases hk : u.has i
    · rw [H1 i hk, jumps_v hw (hv ▸ u.enter hk),u.identify hk]
    by_cases hk' : v.has i
    · rw [H2 i hk', jumps_u (hv.symm ▸ v.enter hk'),v.identify hk']
    · simp only [jumps,ite_eq_right hk,ite_eq_right hk']
  · unfold jumps; dsimp
    split
    · rename_i hk; have := h _ hk; omega
    split
    · rename_i hk; have := g _ hk; omega
    · rfl

abbrev Bicolor := ℂ × ℂ

def twinsAt (u v : Zone) (x : Line) (i : ℕ) : Bicolor := (u.peek x i,v.peek x i)

structure Twins (r : Reel) (u v : Zone) (f : ℕ → Bicolor → Bicolor) : Prop where
  acts : ∀ x i, i<u.wide → twinsAt u v (r.go x) i=f i (twinsAt u v x i)
  waits : ∀ x i, ¬u.has i → ¬v.has i → r.go x i=x i

lemma Twins.stack {r s : Reel} {u v f g} (h : Twins r u v f) (k : Twins s u v g) :
    Twins (r.stack s) u v (fun i x => g i (f i x)) :=
  ⟨fun x i hi => by rw [go_stack, k.acts _ i hi,h.acts _ i hi],fun x i hi gi => by
    rw [go_stack,k.waits _ _ hi gi,h.waits _ _ hi gi]⟩

lemma Twins.congr {r : Reel} {u v f g} (h : Twins r u v f)
    (k : ∀ i<u.wide, ∀ t, f i t=g i t) :
    Twins r u v g :=
  ⟨fun x i hi => (h.acts x i hi).trans (k i hi _),h.waits⟩

section
variable {u v : Zone} (hv : u.wide=v.wide) (hw : u.Sep v)

include hv hw

lemma twins_shade (f g : Line) :
    Twins (shade u v f g) u v (fun i t => (f i * t.1, g i * t.2)) := by
  constructor
  · intro x i hi
    have hp := u.inside hi
    have hh := v.inside (hv ▸ hi)
    simp [shade,twinsAt,Zone.peek,drift,send,applyM,applyC,hp,hh,hw.symm _ hh]
  · intro x i hi hk
    simp [shade,send,applyM,applyC,hi,hk]

lemma twins_snap :
    Twins (snap u v) u v (fun _ t => (ca*t.1+cb*t.2,ca*t.2+cb*t.1)) := by
  constructor
  · intro x i hi
    have hh : u.lo ≠ v.lo := by
      intro g
      have H (i) := hw.symm i
      exact H (v.lo+i) (v.inside (hv ▸ hi)) (by rw [← g]; exact u.inside hi)
    simp [snap,twinsAt,Zone.peek,drift,send,applyC,applyM,
      jumps_u (v:=v) hi,jumps_v hw (hv ▸ hi),hh,Ne.symm hh]
  · intro x i hi hk
    simp [snap,send,applyC,applyM,jumps,hi,hk]

end

def hinge (u v : Zone) : Reel :=
  ((shade u v (fun _ => 1) (fun _ => I)).stack (snap u v)).stack
    (shade u v (fun _ => 1-I) (fun _ => 1+I))

def brick (u v : Zone) : Reel :=
  ((((hinge u v).stack (shade u v (fun _ => -3) (fun _ => 1))).stack
      (hinge u v)).stack (shade u v (fun _ => 2) (fun _ => 1))).stack (hinge u v)

/-- Shear strong when f ≠ 0. -/
def spark (u v : Zone) (f : Line) : Reel :=
  ((shade u v (fun i => (4*f i/5)⁻¹) (fun _ => 1)).stack (brick u v)).stack
    (shade u v (fun i => (-1/8)*(4*f i/5)) (fun _ => -1/6))

def blaze (f : Line) : Line := fun i => 1+ f i * starRingEnd ℂ (f i)

/-- Avoid a coefficient zero test: uniform word for adding f*src. -/
def flash (dst src : Zone) (f : Line) : Reel :=
  (spark dst src (blaze f)).stack (spark dst src (fun i => f i-blaze f i))

section
variable {u v : Zone} {n : ℕ} (h : u.Fits n) (g : v.Fits n)
  (hv : u.wide=v.wide) (hw : u.Sep v)

include h g hv hw

lemma sound_hinge : (hinge u v).Sound n :=
  ((sound_shade h g).stack (sound_snap h g hv hw)).stack (sound_shade h g)

lemma sound_brick : (brick u v).Sound n :=
  have hp := sound_hinge h g hv hw
  ((((hp.stack (sound_shade h g)).stack hp).stack (sound_shade h g)).stack hp)

lemma sound_spark (f : Line) : (spark u v f).Sound n :=
  ((sound_shade h g).stack (sound_brick h g hv hw)).stack (sound_shade h g)

lemma sound_flash (f : Line) : (flash u v f).Sound n :=
  (sound_spark h g hv hw _).stack (sound_spark h g hv hw _)

omit h g

lemma twins_hinge :
    Twins (hinge u v) u v (fun _ t => (t.1+t.2,t.1-t.2)) := by
  unfold hinge
  refine (((twins_shade hv hw _ _).stack (twins_snap hv hw)).stack
    (twins_shade hv hw _ _)).congr ?_
  intro i hi t
  apply Prod.ext
  · apply Complex.ext <;> norm_num [ca,cb,mul_re,mul_im] <;> ring
  · apply Complex.ext <;> norm_num [ca,cb,mul_re,mul_im] <;> ring

lemma twins_brick :
    Twins (brick u v) u v (fun _ t => (-8*t.1-10*t.2,-6*t.2)) := by
  unfold brick
  have hp := twins_hinge hv hw
  refine (((((hp.stack (twins_shade hv hw _ _)).stack hp).stack (twins_shade hv hw _ _)).stack hp)).congr ?_
  intro i hi t
  apply Prod.ext <;> dsimp <;> ring

lemma twins_spark (f : Line) (hh : ∀ i<u.wide, f i ≠ 0) :
    Twins (spark u v f) u v (fun i t => (t.1+f i*t.2,t.2)) := by
  unfold spark
  refine (((twins_shade hv hw _ _).stack (twins_brick hv hw)).stack
    (twins_shade hv hw _ _)).congr ?_
  intro i hi t
  have hz := hh i hi
  apply Prod.ext <;> dsimp
  · field_simp
    ring
  · ring

omit hv hw

lemma blaze_ne (f : Line) (i : ℕ) : blaze f i ≠ 0 := by
  rw [blaze,Complex.mul_conj]
  intro h
  have H := congrArg re h
  simp [normSq_apply] at H
  nlinarith

lemma after_ne (f : Line) (i : ℕ) : f i-blaze f i ≠ 0 := by
  rw [blaze,Complex.mul_conj]
  intro h
  have H := congrArg re h
  simp [normSq_apply] at H
  nlinarith

include hv hw

lemma twins_flash (f : Line) :
    Twins (flash u v f) u v (fun i t => (t.1+f i*t.2,t.2)) := by
  unfold flash
  refine ((twins_spark hv hw (blaze f) (fun i _ => blaze_ne f i)).stack (twins_spark hv hw
    (fun i => f i-blaze f i) (fun i _ => after_ne f i))).congr ?_
  intro i hi t
  apply Prod.ext
  · dsimp; ring
  · rfl

lemma spill_flash (f : Line) :
    Spill (flash u v f) v u (fun x i => f i * x i) := by
  have h := twins_flash hv hw f
  constructor
  · intro x i hi
    exact congrArg Prod.fst (h.acts x i hi)
  · intro x i hi
    by_cases hk : v.has i
    · have hh := congrArg Prod.snd (h.acts x (i-v.lo) (hv.symm ▸ v.enter hk))
      simpa [Zone.peek,drift,twinsAt, v.identify hk] using hh
    · exact h.waits x i hi hk

end

@[simp] lemma beats_shade (u v : Zone) (f g : Line) : (shade u v f g).beats=1 := rfl
@[simp] lemma beats_snap (u v : Zone) : (snap u v).beats=1 := rfl
@[simp] lemma beats_hinge (u v : Zone) : (hinge u v).beats=3 := rfl
@[simp] lemma beats_brick (u v : Zone) : (brick u v).beats=11 := rfl
@[simp] lemma beats_spark (u v : Zone) (f : Line) : (spark u v f).beats=13 := rfl
@[simp] lemma beats_flash (u v : Zone) (f : Line) : (flash u v f).beats=26 := rfl

end
end PowerSaving.Slant

end OAI
