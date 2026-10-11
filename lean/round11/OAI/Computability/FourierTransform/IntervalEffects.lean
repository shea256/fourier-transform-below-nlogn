import OAI.Computability.FourierTransform.LayerWords

namespace OAI

/-! Disjoint interval effects of layer words. In particular a composition of two rectangular
maps can be added by a commutator of adds on an arbitrary-content intermediate. -/
namespace PowerSaving.Slant
open Reel Stroke Spectral
noncomputable section

structure Zone where
  lo : ℕ
  wide : ℕ

namespace Zone
def has (u : Zone) (i : ℕ) : Prop := u.lo ≤ i ∧ i < u.lo+u.wide

instance instDecidableHas (u : Zone) (i : ℕ) : Decidable (u.has i) := by
  unfold has
  infer_instance

def Fits (u : Zone) (v : ℕ) : Prop := ∀ i, u.has i → i<v

lemma fits_of (u : Zone) (n : ℕ) (h : u.lo+u.wide ≤ n) : u.Fits n :=
  fun _ hi => hi.2.trans_le h

lemma fits_empty (i n : ℕ) : Fits ⟨i,0⟩ n := by
  simp [Fits,has]

def Sep (u v : Zone) : Prop := ∀ i, u.has i → ¬ v.has i

lemma sep_of (u v : Zone) (h : u.lo+u.wide ≤ v.lo) : u.Sep v :=
  fun _ hi hj => Nat.not_lt.mpr (h.trans hj.1) hi.2

lemma Sep.symm {u v : Zone} (h : u.Sep v) : v.Sep u := fun i hi g => h i g hi

lemma inside (u : Zone) {i : ℕ} (hi : i<u.wide) : u.has (u.lo+i) :=
  ⟨by omega,by omega⟩

lemma enter (u : Zone) {i : ℕ} (hi : u.has i) :
    i-u.lo < u.wide := by
  unfold has at hi; omega

lemma identify (u : Zone) {i} (hi : u.has i) : u.lo+(i-u.lo)=i := by
  unfold has at hi; omega

lemma boundary (u : Zone) {i : ℕ} (hi : ¬ u.has i) : i<u.lo ∨ u.lo+u.wide ≤ i := by
  unfold has at hi; omega

/-- Only read entries within 'wide'; other values are ignored. -/
def peek (u : Zone) (x : Line) : Line := drift u.lo x

def slim (u : Zone) (n : ℕ) : Zone := ⟨u.lo,n⟩

lemma slim_has (u : Zone) {n i : ℕ} (hn : n ≤ u.wide)
    (hi : (u.slim n).has i) : u.has i := ⟨hi.1,hi.2.trans_le (by change u.lo+n ≤ _; omega)⟩

lemma Fits.slim {u : Zone} {v n : ℕ} (h : u.Fits v) (hn : n ≤ u.wide) :
    (u.slim n).Fits v := fun i hi => h i (slim_has u hn hi)

lemma Sep.slim_left {u v : Zone} (h : u.Sep v) {n : ℕ} (hn : n ≤ u.wide) :
    (u.slim n).Sep v := fun i hi => h i (slim_has u hn hi)

lemma Sep.slim_right {u v : Zone} (h : u.Sep v) {n : ℕ} (hn : n ≤ v.wide) :
    u.Sep (v.slim n) := (h.symm.slim_left hn).symm

end Zone

/-- f read only first p entries for the first q output entries -/
def Reads (p q : ℕ) (f : Line → Line) : Prop :=
  ∀ x y, (∀ i<p, x i=y i) → ∀ i<q, f x i=f y i

def AdditiveOn (q : ℕ) (f : Line → Line) : Prop :=
  ∀ x y, ∀ i<q, f (x+y) i=f x i+f y i

def minusFn (f : Line→Line) : Line → Line := fun x i => -f x i

structure Spill (r : Reel) (u v : Zone) (f : Line→Line) : Prop where
  adds : ∀ (x : Line) (i), i<v.wide → v.peek (r.go x) i=v.peek x i + f (u.peek x) i
  keeps : ∀ (x : Line) (i), ¬ v.has i → r.go x i=x i

namespace Spill
variable {r : Reel} {u v z : Zone} {f g : Line→Line}

lemma preserves (h : Spill r u v f) (hz : z.Sep v) (x : Line) :
    ∀ i<z.wide, z.peek (r.go x) i=z.peek x i :=
  fun _ hi => h.keeps x _ (hz _ (z.inside hi))

lemma congr (h : Spill r u v f) (hg : ∀ (x : Line), ∀ i<v.wide, f x i = g x i) :
    Spill r u v g :=
  ⟨fun x i hi => (h.adds x i hi).trans (by rw [hg _ i hi]),h.keeps⟩

end Spill

open Zone
/-- The commutator construction. Disjoint x->z, z->y adds. -/
def cameo (a b c d : Reel) : Reel := ((a.stack b).stack c).stack d

lemma sound_cameo (a b c d : Reel) (n) (h : a.Sound n) (g : b.Sound n)
    (p : c.Sound n) (q : d.Sound n) :
    (cameo a b c d).Sound n :=
  ((h.stack g).stack p).stack q

theorem spill_cameo {a b c d : Reel} {u v z : Zone}
    {f g : Line→Line}
    (ha : Spill a u z f) (hb : Spill b z v g)
    (hc : Spill c u z (minusFn f)) (hd : Spill d z v (minusFn g))
    (rf : Reads u.wide z.wide f) (rg : Reads z.wide v.wide g)
    (hh : AdditiveOn v.wide g)
    (huv : u.Sep v) (huz : u.Sep z) (hzv : z.Sep v) :
    Spill (cameo a b c d) u v (g ∘ f) := by
  have middle (x : Line) :
      ∀ i < z.wide, z.peek (c.go (b.go (a.go x))) i = z.peek x i := by
    intro i hi
    have H (j : ℕ) (hj : j < u.wide) :
        u.peek (b.go (a.go x)) j = u.peek x j :=
      (hb.preserves huv _ j hj).trans (ha.preserves huz _ j hj)
    rw [hc.adds _ i hi, hb.preserves hzv _ i hi, ha.adds _ i hi, minusFn, rf _ _ H i hi]
    ring
  constructor
  · intro x i hi
    have H := rg _ _ (middle x) i hi
    have mid : g (z.peek (a.go x)) i=g (z.peek x + f (u.peek x)) i := by
      apply rg
      · intro j hj
        exact ha.adds x j hj
      · exact hi
    simp only [cameo,Reel.go_stack]
    rw [hd.adds _ i hi,minusFn,H, hc.preserves hzv.symm _ i hi, hb.adds _ i hi,
      ha.preserves hzv.symm _ i hi,mid, hh _ _ i hi,Function.comp_apply]
    ring
  · intro x i hi
    simp only [cameo,Reel.go_stack]
    rw [hd.keeps _ i hi]
    by_cases h : z.has i
    · have G := middle x (i-z.lo) (z.enter h)
      simpa [Zone.peek, Stroke.drift,z.identify h] using G
    · rw [hc.keeps _ i h,hb.keeps _ i hi,ha.keeps _ i h]

end
end PowerSaving.Slant

end OAI
