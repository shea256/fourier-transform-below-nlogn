import OAI.Computability.FourierTransform.ConvolutionProgram

namespace OAI

/- Static allowance to programs. -/
namespace PowerSaving
open RAM Ty Selection Spectral Slant
noncomputable section

namespace RAM.Bench
universe U
variable {ι : Type U} {κ : Type*} {m : Bool} {b : Bench m ι}
  {n : ι→ℕ} {t : Ty}

lemma fairwind_small (N : ι→ℕ) (hn : ∀ i,0<N i) (d : ℕ) :
    Small N fun i => fairwind d (N i) := by
  have H := Small.self N
  have hX i := barge_spec (N i) (hn i)
  have h4 := (Small.const _ 4).mul H
  have hu := h4.mono (fun (i : ι) => stack_le (N i) (hn i))
  have hk : Small N fun i => harvestN (N i) :=
    (((Small.const _ 16).mul (hu.add (Small.const _ 4))).pow 2)
  have hh := ((Small.const _ 8).mul hk).mono
    (fun i => Nat.lt_two_pow_self.le.trans (orderE_small (N i)))
  have hi := ((((Small.const _ 20000000).mul ((hh.add (Small.const _ 1)).pow 2)).add
    (Small.const _ 7))).mono (fun i => score_le (orderE (N i)))
  have hp : Small N fun i => hills (barge (N i)).l :=
    (hu.add (Small.const _ 1)).mono fun i => (hills_le _).trans
      (Nat.add_le_add_right (hX i).count _)
  have hj := (hi.add (Small.const _ 1)).mul
    ((h4.mono fun i => (hX i).upper.le).mul hp)
  have hl := H.add hj |>.add ((hu.add (Small.const _ 2)).pow d)
  exact hl.add (((H.add (Small.const _ 2)).pow d).mono fun i => by split <;> omega)

-- package extracted charges
abbrev Sizes := {n : ℕ // 0<n}
abbrev entry : Sizes→ℕ := Subtype.val

structure Ration where
  d : ℕ
  c : ℕ
  p : ℕ
def calorie (a : Ration) (n : ℕ) := a.c*(fairwind a.d n+1)

lemma Breezy.ration {x : ι→T t} (h : b.Breezy n t x) :
    ∃ (s : Prog m b.tray t) (a : Ration), ∀ i,
      (run s (b.env i)).OK (x i) (calorie a (n i)) ((b.size i+2)^a.p) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨s,c,p,hc⟩ := Can.unfold_bound hd
  exact ⟨s,⟨d,c,p⟩,hc⟩

def lunch (a b : Ration) (N : ℕ→ℕ) (n : ℕ) :=
  calorie a (N n)+1+calorie b (N n)

lemma storehouse (N : ℕ→ℕ) (h : ∀ n,0<n → 0<N n) (g : Small entry (fun i => N (entry i)))
    (a b : Ration) : ∃ c : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^c
    lunch a b N n + 10*(n+2) ≤ cap ∧ (n+2)^a.p ≤ cap ∧ (n+2)^b.p ≤ cap ∧
    receipt (N n) ≤ cap := by
  let M i := N (entry i)
  have H (a : Ration) : Small entry (fun i => calorie a (M i)) :=
    (Small.const _ a.c).mul (((fairwind_small M (fun i => h _ i.property) a.d).trans g).add
      (Small.const _ 1))
  have hu := (Small.self entry).add (Small.const _ 2)
  have hh := (Small.const _ 10).mul hu
  have hp := ((Small.const _ 8).mul (g.pow 3)).mono
    (fun i => (receipt_bound _ (h _ i.property)).2.le)
  have ht := ((((H a).add (Small.const _ 1)).add (H b)).add hh)
  obtain ⟨c,hc⟩ := (((ht.max (hu.pow a.p)).max (hu.pow b.p)).max hp)
  refine ⟨c,fun n hn => ?_⟩
  specialize hc (⟨n,hn⟩:Sizes)
  have hx :
      max (max (max (lunch a b N n + 10*(n+2)) ((n+2)^a.p)) ((n+2)^b.p)) (receipt (N n)) ≤
        (n+2)^c := hc
  have h1 := max_le_iff.mp hx
  have h2 := max_le_iff.mp h1.1
  have h3 := max_le_iff.mp h2.1
  exact ⟨h3.1,h3.2,h2.2,h1.2⟩

-- order environments
def onlyLength : Bench false Sizes := ⟨entry,w,entry⟩
lemma onlyLength_num : onlyLength.Nick entry := ⟨Can.id,Small.self _⟩

lemma orders1 : ∃ (s : Prog false w w) (a : Ration), ∀ n,0<n →
    (run s n).OK (receipt n) (calorie a n) ((n+2)^a.p) := by
  obtain ⟨s,a,ha⟩ := (onlyLength_num.landOrder (fun i => i.property)).ration
  exact ⟨s,a,fun i hi => ha ⟨i,hi⟩⟩
lemma orders2 : ∃ (s : Prog false w w) (a : Ration), ∀ n,0<n →
    (run s n).OK (receipt (stretch n)) (calorie a (stretch n)) ((n+2)^a.p) := by
  have H : onlyLength.Nick fun i => stretch (entry i) :=
    ((Nick.wc 2).mul onlyLength_num).sub (Nick.wc 1)
  obtain ⟨s,a,ha⟩ := (H.landOrder (fun i => stretch_pos i.property)).ration
  exact ⟨s,a,fun i hi => ha ⟨i,hi⟩⟩

def towerOne : Bench false (Sizes×Line) :=
  ⟨fun i => entry i.1,dftInKind,fun i =>
    (entry i.1, root (receipt (entry i.1)),Tape.tab (entry i.1) i.2)⟩

lemma executeOne : ∃ (s : Prog false dftInKind dftOutKind) (a : Ration),
    ∀ (n : ℕ),0<n → ∀ x : Vec n,
    (run s (n, root (receipt n), (⟨n,x⟩ : Tape ℂ))).OK
      (⟨n, dft n x⟩ : Tape ℂ) (calorie a n) ((n+2)^a.p) := by
  let K := towerOne
  have ht : K.Moves (fun _ => 0) dftInKind K.env := envNow K
  let n (i : Sizes × Line) := entry i.1
  have hk : K.Nick n := ⟨ht.fst,Small.self _⟩
  have H := hk.land (fun i => i.1.property) (ht.snd.fst) false (x:=Prod.snd) (cl:=Paint.left)
    (ht.snd.snd)
  obtain ⟨s,a,ha⟩ := H.ration
  refine ⟨s,a,fun n hn x => ?_⟩
  specialize ha ((⟨n,hn⟩:Sizes),extendLine x)
  change (run s (n,root (receipt n),(⟨n,front n (extendLine x)⟩:Tape ℂ))).OK
    (⟨n,front n (freq n (pr false n) (extendLine x))⟩ : Tape ℂ) _ _ at ha
  rw [← dft_front n,front_exact] at ha
  exact ha

def towerBoth : Bench true (Sizes×Line×Line) :=
  ⟨fun i => entry i.1,convInKind,fun i =>
    (entry i.1, root (receipt (stretch (entry i.1))),Tape.tab (entry i.1) i.2.1,
      Tape.tab (entry i.1) i.2.2)⟩

lemma executeBoth : ∃ (s : Prog true convInKind convOutKind) (a : Ration),
    ∀ (n : ℕ),0<n → ∀ x y : Vec n,
    (run s (n, root (receipt (stretch n)), (⟨n,x⟩ : Tape ℂ),(⟨n,y⟩ : Tape ℂ))).OK
      (⟨stretch n, conv n x y⟩ : Tape ℂ) (calorie a (stretch n)) ((n+2)^a.p) := by
  let K := towerBoth
  have ht : K.Moves (fun _ => 0) convInKind K.env := envNow K
  let n (i : Sizes × Line×Line) := entry i.1
  have hk : K.Nick n := ⟨ht.fst,Small.self _⟩
  have H := fusing hk (fun i => i.1.property) (x:=fun i => i.2.1) (y:=fun i => i.2.2)
    ht.snd.snd.fst ht.snd.snd.snd ht.snd.fst
  obtain ⟨s,a,ha⟩ := H.ration
  refine ⟨s,a,fun n hn x y => ?_⟩
  specialize ha ((⟨n,hn⟩:Sizes),extendLine x,extendLine y)
  change (run s (n,root (receipt (stretch n)),
    (⟨n,front n (extendLine x)⟩:Tape ℂ),(⟨n,front n (extendLine y)⟩:Tape ℂ))).OK
    (⟨2*n-1,front (2*n-1)
      (cyclic (2*n-1) (padline n (extendLine y)) (padline n (extendLine x)))⟩ : Tape ℂ) _ _ at ha
  rw [cyclic_pad_front,front_exact,front_exact] at ha
  exact ha

theorem flagshipOne : ∃ order solve a b,
    DFTProgram order solve (lunch a b id) ∧
    ∀ n, 0<n → (run order n).val = receipt n := by
  obtain ⟨o,a,ho⟩ := orders1
  obtain ⟨s,b,hs⟩ := executeOne
  obtain ⟨c,hc⟩ := storehouse id (fun _ h => h) (Small.self entry) a b
  refine ⟨o,s,a,b,⟨c,fun n hn => ?_⟩,fun n hn => (ho n hn).result⟩
  obtain ⟨hu,hA,hB,hR⟩ := hc n hn
  have H := ho n hn
  have HH := receipt_bound n hn
  have he := H.result
  refine ⟨hu,H.bound.trans hA,H.valid,he.symm ▸ HH.1,he.symm ▸ ?_,he.symm ▸ hR,fun x => ?_⟩
  · exact HH.2.trans_le (by omega)
  dsimp only
  rw [he]
  have hj := hs n hn x
  exact ⟨hj.valid,hj.bound.trans hB,add_le_add (add_le_add_left H.time 1) hj.time,hj.result⟩

theorem flagshipBoth : ∃ order solve a b,
    ConvProgram order solve (lunch a b stretch) ∧
    ∀ n, 0<n → (run order n).val = receipt (stretch n) := by
  obtain ⟨o,a,ho⟩ := orders2
  obtain ⟨s,b,hs⟩ := executeBoth
  obtain ⟨c,hc⟩ := storehouse stretch (fun _ h => stretch_pos h)
    (((Small.const _ 2).mul (Small.self entry)).sub (Q:=fun _ => 1)) a b
  refine ⟨o,s,a,b,⟨c,fun n hn => ?_⟩,fun n hn => (ho n hn).result⟩
  obtain ⟨hu,hA,hB,hR⟩ := hc n hn
  have H := ho n hn
  have HH := receipt_bound _ (stretch_pos hn)
  have he := H.result
  refine ⟨hu,H.bound.trans hA,H.valid,he.symm ▸ HH.1,he.symm ▸ ?_,he.symm ▸ hR,fun x y => ?_⟩
  · exact HH.2.trans_le (by unfold stretch; omega)
  dsimp only
  rw [he]
  have hj := hs n hn x y
  exact ⟨hj.valid,hj.bound.trans hB,add_le_add (add_le_add_left H.time 1) hj.time,hj.result⟩

end RAM.Bench
end
end PowerSaving

end OAI
