import OAI.Computability.FourierTransform.ToeplitzUpdates

namespace OAI

namespace PowerSaving.Slant
open Reel Stroke Zone Spectral Finset
noncomputable section

def strand (a : ℕ → Reel) : ℕ → Reel
  | 0 => wait 0
  | i+1 => (strand a i).stack (a i)

lemma beat_strand {a : ℕ→Reel} (n d : ℕ) (h : ∀ i<n,(a i).beats=d) :
    (strand a n).beats=n*d := by
  induction n with
  | zero => simp [strand,wait]
  | succ n ih =>
    change (strand a n).beats+(a n).beats=_
    rw [ih (by intro i hi; exact h i (by omega)),h n (by omega),add_mul,one_mul]

lemma sound_strand {a : ℕ→Reel} (n m : ℕ) (h : ∀ i<n,(a i).Sound m) :
    (strand a n).Sound m := by
  induction n with
  | zero => exact sound_wait 0 m
  | succ n ih =>
    exact (ih (fun i hi => h i (by omega))).stack (h n (by omega))

def summary (n : ℕ) (f : ℕ → Line → Line) (x : Line) : Line :=
  fun i => ∑ j ∈ range n, f j x i

lemma reads_summary {a b : ℕ} (n : ℕ) (f : ℕ → Line→Line)
    (h : ∀ i<n, Reads a b (f i)) :
    Reads a b (summary n f) :=
  fun x y hx i hi => sum_congr rfl fun j hj => h j (mem_range.mp hj) x y hx i hi

lemma spill_strand {a : ℕ→Reel} (n : ℕ) (u v : Zone) (f : ℕ→Line→Line)
    (h : ∀ i<n, Spill (a i) u v (f i)) (hs : u.Sep v)
    (hr : ∀ i<n, Reads u.wide v.wide (f i)) :
    Spill (strand a n) u v (summary n f) := by
  induction n with
  | zero =>
    constructor
    · intro x i hi; simp [strand,summary]
    · intro x i hi; simp [strand]
  | succ n ih =>
    have hp := ih (fun i hi => h i (by omega)) (fun i hi => hr i (by omega))
    have hh := h n (by omega)
    constructor
    · intro x i hi
      rw [strand,go_stack,hh.adds _ i hi, hr n (by omega) _ _ (hp.preserves hs x) i hi,
        hp.adds x i hi]
      simp [summary,sum_range_succ,add_assoc]
    · intro x i hi
      rw [strand,go_stack,hh.keeps _ i hi,hp.keeps _ i hi]

/-- geometry, p = count*b. -/
def quay (b j : ℕ) : Zone := ⟨j*b,b⟩
def coast (p w : ℕ) : Zone := ⟨p,w⟩
def jetty (p w b s : ℕ) : Zone := ⟨p+s*b,min b (w-s*b)⟩

lemma quay_fits (l b j w : ℕ) (hj : j<l) : (quay b j).Fits (l*b+w) :=
  fits_of _ _ (by
    have h := Nat.mul_le_mul_right b hj
    change j*b+b ≤ _
    change (j+1)*b ≤ _ at h; rw [add_mul,one_mul] at h; omega)

lemma jetty_has (p w b s i : ℕ) (hi : (jetty p w b s).has i) :
    (coast p w).has i := by
  change p+s*b ≤ i ∧ i < p+s*b+min b (w-s*b) at hi
  change p ≤ i ∧ i < p+w
  omega

lemma jetty_fits (p w b s : ℕ) :
    (jetty p w b s).Fits (p+w) :=
  fun i hi => (jetty_has p w b s i hi).2

lemma body_sep (p w : ℕ) : (initial p).Sep (coast p w) :=
  sep_of _ _ (by change 0+p ≤ p; omega)

lemma quay_sep (l w b s j : ℕ) (hj : j<l) :
    (quay b j).Sep (jetty (l*b) w b s) := by
  intro i hi hk
  have h1 : i<l*b := by simpa using quay_fits l b j 0 hj i hi
  have h2 : l*b ≤ i := (jetty_has _ _ _ _ i hk).1
  omega

lemma quay_peek (b j p : ℕ) (x : Line) :
    (quay b j).peek ((initial p).peek x)=(quay b j).peek x := by
  ext i; simp [initial,Zone.peek,drift]

lemma spill_quay {u : Reel} {v : Zone} {p b j : ℕ} {f : Line→Line}
    (h : Spill u (quay b j) v f) :
    Spill u (initial p) v (fun x => f ((quay b j).peek x)) := by
  constructor
  · intro x i hi; rw [h.adds x i hi,quay_peek]
  · exact h.keeps

lemma reads_quay {l b j p : ℕ} {f : Line→Line} (hj : j<l) (h : Reads b p f) :
    Reads (initial (l*b)).wide p (fun x => f ((quay b j).peek x)) := by
  intro x y hx
  apply h
  intro i hi
  apply hx
  exact (by simpa [initial] using
    quay_fits l b j 0 hj _ ((quay b j).inside hi))

-- extend a jetty effect f (given with whole target indexing)
def jet_effect (p w b s : ℕ) (f : Line→Line) (x : Line) : Line :=
  fun i => if (jetty p w b s).has (p+i) then f x i else 0

lemma spill_jet {u : Reel} {v : Zone} {p w b s : ℕ} {f : Line→Line}
    (h : Spill u v (jetty p w b s) (fun x i => f x (s*b+i))) :
    Spill u v (coast p w) (jet_effect p w b s f) := by
  let M := jetty p w b s
  constructor
  · intro x i hi
    change u.go x (p+i) = _ + if M.has (p+i) then _ else _
    by_cases H : M.has (p+i)
    · simp only [ite_eq_left H]
      have hh := h.adds x (p+i-M.lo) (M.enter H)
      change u.go x (M.lo+(p+i-M.lo)) = x (M.lo+(p+i-M.lo))+_ at hh
      rw [M.identify H] at hh
      have hh' : s*b+(p+i-M.lo)=i := by
        have := M.identify H
        change p+s*b+(_-(p+s*b))=_ at this
        change s*b+(_-(p+s*b))=_
        omega
      rw [hh'] at hh
      exact hh
    · simp only [ite_eq_right H,add_zero]
      exact h.keeps x (p+i) H
  · intro x i hi
    exact h.keeps x i fun H => hi (jetty_has _ _ _ _ i H)

lemma reads_jet {p w b s n : ℕ} {f : Line→Line} (h : Reads n w f) :
    Reads n w (jet_effect p w b s f) := by
  intro x y H i hi
  simp only [jet_effect,h x y H i hi]

lemma sum_mult (f : ℕ→ℂ) (l b : ℕ) :
    ∑ j ∈ range (l*b), f j =
    ∑ j ∈ range l, ∑ k ∈ range b, f (j*b+k) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [add_mul,one_mul,sum_range_add,ih,sum_range_succ]

lemma summary_jet (l p w b : ℕ) (hb : 0<b) (hw : w ≤ l*b) (f : Line→Line) :
    ∀ x, ∀ i<w, summary l (fun s => jet_effect p w b s f) x i = f x i := by
  intro x i hi
  let j := i/b
  have hl : j<l := (Nat.div_lt_iff_lt_mul hb).mpr (hi.trans_le hw)
  have hp : i=j*b+i%b := by
    unfold j; rw [mul_comm]; exact (Nat.div_add_mod i b).symm
  have hq : i%b<b := Nat.mod_lt _ hb
  have h (s : ℕ) : (jetty p w b s).has (p+i) ↔ s=j := by
    change (p+s*b ≤ p+i ∧ p+i < p+s*b+min b (w-s*b)) ↔ _
    constructor
    · intro H
      by_contra HH
      rcases lt_or_ge s j with hk|hk
      · have hh := Nat.mul_le_mul_right b hk
        change (s+1)*b ≤ _ at hh; rw [add_mul,one_mul] at hh
        omega
      · have hg := Nat.mul_le_mul_right b (show j+1 ≤ s by omega)
        rw [add_mul,one_mul] at hg
        omega
    · intro H; rw [H]; omega
  unfold summary
  simp [jet_effect,h,hl]

-- A piece effect for a target chunk s, intermediary chunk c and source chunk j.
def wave (p b s c j : ℕ) (h g : Line) : Line → Line :=
  (spout b (c*b) (p+s*b) h) ∘ (spout b (j*b) (c*b) g)

/-- Cross term at (p+i) from updated left half of width p. -/
def surf (p : ℕ) (h g : Line) (x : Line) : Line :=
  fun i => stencil p h (stencil p g x) (p+i)

lemma wave_reads (p b s c j v : ℕ) (h g : Line) :
    Reads b v (wave p b s c j h g) :=
  (reads_spout b (j*b) (c*b) b g).chain (reads_spout b (c*b) (p+s*b) v h)

lemma surf_reads (p w : ℕ) (h g : Line) :
    Reads p w (surf p h g) := by
  intro x y hx i hi
  unfold surf; rw [stencil_congr _ g hx]

lemma wave_sum (l b s : ℕ) (h g x : Line) (i : ℕ) :
    (∑ c ∈ range l, ∑ j ∈ range l, wave (l*b) b s c j h g ((quay b j).peek x) i) =
    surf (l*b) h g x (s*b+i) := by
  simp only [wave, surf, Function.comp_apply, spout,stencil]
  -- expand RHS over corresponding chunks
  rw [sum_mult _ l b]
  have hp (k : ℕ) :
      ∑ j ∈ range (l*b), rise g k j*x j =
      ∑ j ∈ range l, ∑ a ∈ range b, rise g k (j*b+a) * x (j*b+a) := sum_mult ..
  simp only [hp,mul_sum]
  refine sum_congr rfl ?_
  intro c hc
  rw [sum_comm]
  simp only [add_assoc,quay,Zone.peek,drift]

def riprap (a : ℕ → ℕ → ℕ → Reel) (l : ℕ) : Reel :=
  strand (fun s => strand (fun c => strand (fun j => a s c j) l) l) l

lemma beats_riprap (a : ℕ → ℕ → ℕ → Reel) (l n : ℕ)
    (h : ∀ s<l, ∀ c<l, ∀ j<l, (a s c j).beats=n) :
    (riprap a l).beats=l*(l*(l*n)) :=
  beat_strand _ _ fun s hs => beat_strand _ _ fun c hc => beat_strand _ _ (h s hs c hc)

lemma sound_riprap (a : ℕ → ℕ → ℕ → Reel) (l n : ℕ)
    (h : ∀ s<l, ∀ c<l, ∀ j<l, (a s c j).Sound n) :
    (riprap a l).Sound n :=
  sound_strand _ _ fun s hs => sound_strand _ _ fun c hc => sound_strand _ _ (h s hs c hc)

lemma spill_riprap (a : ℕ → ℕ → ℕ → Reel) (l b w : ℕ) (h g : Line)
    (hb : 0<b) (hw : w ≤ l*b)
    (H : ∀ s<l, ∀ c<l, ∀ j<l,
      Spill (a s c j) (quay b j) (jetty (l*b) w b s) (wave (l*b) b s c j h g)) :
    Spill (riprap a l) (initial (l*b)) (coast (l*b) w) (surf (l*b) h g) := by
  let p := l*b
  let W s := jetty p w b s
  let f := surf p h g
  let q s := strand (fun c => strand (fun j => a s c j) l) l
  let T s c j (x : Line) := wave p b s c j h g ((quay b j).peek x)
  have hu (s : ℕ) (hs : s<l) :
      Spill (q s) (initial p) (W s) (fun x i => f x (s*b+i)) := by
    have hS : (initial p).Sep (W s) := fun i hi hg => body_sep p w _ hi (jetty_has _ _ _ _ i hg)
    have ht (c j : ℕ) (hj : j<l) :
        Reads (initial p).wide (W s).wide (T s c j) :=
      reads_quay hj (wave_reads _ _ _ _ _ _ h g)
    have G := spill_strand (a:=fun c => strand (fun j => a s c j) l) l (initial p)
      (W s) (fun c => summary l (T s c))
      (fun c hc => spill_strand l _ _ (T s c) (fun j hj => spill_quay
        (H s hs c hc j hj)) hS (ht c))
      hS (fun c _ => reads_summary l (T s c) (ht c))
    exact G.congr (fun x i _ => wave_sum l b s h g x i)
  have hh := spill_strand l (initial p) (coast p w) (fun s => jet_effect p w b s f)
    (a:=q) (fun s hs => spill_jet (hu s hs)) (body_sep p w)
    (fun _ _ => reads_jet (surf_reads p w h g))
  exact hh.congr (summary_jet l p w b hb hw f)

end
end PowerSaving.Slant

end OAI
