import OAI.Computability.FourierTransform.CompilerEnvironment

namespace OAI

namespace PowerSaving.RAM
open Ty
noncomputable section

universe U V

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

lemma restricted (b : Bench m ι) (p : ι→Prop) :
    (b.scrutin p).Feeds b Subtype.val := Feeds.along b _

/-- Branches tested by integer registers. -/
def Study (b : Bench m ι) (P : ι→Prop) : Prop :=
  ∃ x : ι→ℕ, b.Digit x ∧ ∀ i, P i ↔ x i ≠ 0

namespace Study

variable {P Q : ι→Prop}

lemma transport {P : κ→Prop} {f : ι→κ} (h : b.Feeds q f) (k : q.Study P) :
    b.Study (fun i => P (f i)) :=
  let ⟨_,hx,g⟩ := k
  ⟨_,draw h hx,fun i => g (f i)⟩

lemma equiv (h : b.Study P) (g : ∀ i, P i ↔ Q i) :
    b.Study Q :=
  let ⟨x,hx,k⟩ := h
  ⟨x,hx,fun i => (g i).symm.trans (k i)⟩

lemma lt {x y} (h : b.Digit x) (g : b.Digit y) :
    b.Study (fun i => x i < y i) :=
  ⟨_,h.isLess g, fun i => by split <;> simp [*]⟩

lemma neg (h : b.Study P) :
    b.Study (fun i => ¬ P i) := by
  obtain ⟨x,hx,k⟩ := h
  refine (lt hx (Digit.wc 1)).equiv ?_
  intro i; rw [k]; omega

lemma le {x y} (h : b.Digit x) (g : b.Digit y) :
    b.Study (fun i => x i ≤ y i) :=
  ((lt g h).neg).equiv (fun i => by simp)

lemma both (h : b.Study P) (g : b.Study Q) :
    b.Study (fun i => P i ∧ Q i) := by
  obtain ⟨x,hx,k⟩ := h
  obtain ⟨y,hy,j⟩ := g
  refine ⟨_,hx.mul hy,fun i => ?_⟩
  simp [k,j,not_or]

lemma eq {x y} (h : b.Digit x) (g : b.Digit y) :
    b.Study (fun i => x i=y i) :=
  ((le h g).both (le g h)).equiv (fun i => by omega)

end Study

theorem chooseM {t : Ty} {y : ι→T t} {P}
    (h : b.Study P)
    (a : (b.scrutin P).Makes t (fun i => y i.val))
    (c : (b.scrutin (fun i => ¬P i)).Makes t (fun i => y i.val)) :
    b.Makes t y := by
  obtain ⟨x,hx,g⟩ := h
  refine PolyCan.testz hx.run ?_ ?_
  · exact PolyCan.reindex c (fun i : {i // x i = 0} => ⟨i.val,by
      rw [g]; exact not_not_intro i.property⟩)
  · exact PolyCan.reindex a (fun i : {i // x i ≠ 0} => ⟨i.val,(g _).mpr i.property⟩)

theorem branchM {t : Ty} {P : ι→Prop} [DecidablePred P] {x y : ι→T t}
    (h : b.Study P)
    (a : (b.scrutin P).Makes t (fun i => x i.val))
    (c : (b.scrutin (fun i => ¬ P i)).Makes t (fun i => y i.val)) :
    b.Makes t (fun i => if P i then x i else y i) :=
  chooseM h (a.congr (fun i => (ite_eq_left i.property).symm))
    (c.congr (fun i => (ite_eq_right i.property).symm))

theorem splice {F : ι→ℕ} {P : ι→Prop}
    (h : Small (b.scrutin P).size (fun i => F i.val))
    (g : Small (b.scrutin (fun i => ¬ P i)).size (fun i => F i.val)) :
    Small b.size F := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨y,hy⟩ := g
  refine ⟨x+y,fun i => ?_⟩
  by_cases hi : P i
  · exact (hx ⟨i,hi⟩).trans (Small.pow_mono_degree (b.size i) (by omega))
  · exact (hy ⟨i,hi⟩).trans (Small.pow_mono_degree (b.size i) (by omega))

lemma chooseN {x : ι→ℕ} {P} (h : b.Study P)
    (a : (b.scrutin P).Digit (fun i => x i.val))
    (c : (b.scrutin (fun i => ¬P i)).Digit (fun i => x i.val)) :
    b.Digit x := ⟨chooseM h a.run c.run,splice a.small c.small⟩

lemma branchN {P : ι→Prop} [DecidablePred P] {x y : ι→ℕ}
    (h : b.Study P)
    (a : (b.scrutin P).Digit (fun i => x i.val))
    (c : (b.scrutin (fun i => ¬ P i)).Digit (fun i => y i.val)) :
    b.Digit (fun i => if P i then x i else y i) :=
  chooseN h (a.congr (fun i => (ite_eq_left i.property).symm)) (c.congr
    (fun i => (ite_eq_right i.property).symm))

lemma iteN {P : ι→Prop} [DecidablePred P] {x y : ι→ℕ}
    (h : b.Study P) (a : b.Digit x) (c : b.Digit y) :
    b.Digit (fun i => if P i then x i else y i) :=
  branchN h (draw (restricted ..) a) (draw (restricted ..) c)

end Bench
end
end PowerSaving.RAM

end OAI
