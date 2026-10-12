import OAI.Computability.FourierTransform.NetworkStages

namespace OAI

namespace PowerSaving.Binary
open Finset Matrix
noncomputable section

theorem shift_zero {α : Type*} [Fintype α] [DecidableEq α] :
    shift (0 : Space α) = 1 := by ext i j; simp [shift,one_apply]

/-- Terminal exceptional ratio. -/
theorem terminal_calc {α : Type*} [Fintype α] [DecidableEq α]
    (A : OBase α) (p : α) :
    kernel α * frame A {p} = shift (A.v p) * frame A (univ \ {p}) := by
  have hi : frame A {p} = delta (A.v p) := by
    simpa using frame_ins A ∅ p (by simp)
  let s := univ \ ({p}:Finset α)
  have hs : insert p s = univ := by ext i; by_cases i=p <;> simp [s, *]
  have hk : kernel α = delta (A.v p) * frame A s := by
    have h := frame_ins A s p (by simp [s])
    rwa [hs, frame_univ] at h
  rw [hi,hk,mul_assoc,← delta_comm,← mul_assoc,delta_sq _ (A.self _)]

theorem translateAll {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (z : ρ → Space α) :
    ∃ p : PWord α ρ, tally p=0 ∧ ∀ f x,
      walk f p x = multiAct f (fun i => shift (z i)) x := by
  have hh (s : Finset ρ) :
      ∃ p : PWord α ρ, tally p=0 ∧ ∀ f x,
        walk f p x = multiAct f (fun i => if i∈s then shift (z i) else 1) x := by
    induction s using Finset.induction with
    | empty =>
      exact ⟨[],rfl, by intro f x; funext j; simp [walk,multiAct]⟩
    | insert i s h ih =>
      obtain ⟨p,hp,hm⟩ := ih
      refine ⟨p++[.shift i (z i)],by rw [tally_append,hp]; rfl,?_⟩
      intro f x
      rw [walk_append, hm]
      funext j; by_cases e : j=i
      · subst j; simp [walk,multiAct,Move.go,roleAct,h]
      · simp [walk,multiAct,Move.go,roleAct,e]
  obtain ⟨p,hp,h⟩ := hh univ
  exact ⟨p,hp,by simpa using h⟩

theorem framed_surj {α ρ : Type*} [Fintype α] [DecidableEq α]
    [Fintype ρ] [DecidableEq ρ] (A : ρ → OBase α) (s : ρ→Finset α)
    (f : ℕ) : Function.Surjective (withFrame A s f) := by
  intro x
  refine ⟨multiAct f (fun r => unframe (A r) (s r)) x, ?_⟩
  funext r; simp [withFrame,multiAct,unframe_right]

end
end PowerSaving.Binary

namespace PowerSaving.Cluster
open Finset Binary Matrix
noncomputable section

def sink : Role → Mask
  | .inl (.inr _) => univ \ {pole}
  | _ => univ

lemma region_zero : region 0 = {pole} := by
  ext k
  simp [region,pole,funext_iff]

lemma region_full : region 3 = univ := by
  ext k
  simp only [mem_univ,in_reg, iff_true]
  intro i hi
  exact (Nat.not_lt.mpr hi i.isLt).elim
lemma border_inx (k : Key) : border 0 (gx k)={pole} := region_zero
lemma border_iny (k : Key) : border 0 (gy k)=∅ := by
  change rim 0=∅
  simp [rim,region_zero]
lemma border_inr (r : AllAux ⊕ Spare) : border 0 (.inr r)=∅ := by
  rcases r with ⟨j,v,a⟩|r <;> simp [border]
lemma border_le_sink (r : Role) : border 3 r ⊆ sink r := by
  rcases r with ((k|k)|(⟨j,v,a⟩|r)) <;> simp [border,region_full,sink,rim]

def exchange (x : Role→ℂ) : Role→ℂ
  | .inl (.inl k) => -x (gy k)
  | .inl (.inr k) => x (gx k)
  | r => x r

lemma all_stages : Path bases (border 0) sink exchange (3*stageLoss) := by
  have h := ((stage false 0).trans (stage true 1)).trans (stage false 2)
  change Path _ (border 0) (border 3)
    (stageOp false ∘ stageOp true ∘ stageOp false) ((stageLoss+stageLoss)+stageLoss) at h
  have g := h.trans (Path.inc bases border_le_sink)
  have he : id ∘ (stageOp false ∘ stageOp true ∘ stageOp false) = exchange := by
    funext x r
    rcases r with (k|k)|r <;> simp [Function.comp_apply, stageOp,exchange,gx,gy]
  rw [he, show stageLoss+stageLoss+stageLoss+0=3*stageLoss by omega] at g
  exact g

private lemma mass_groups {K R α : Type*} [Fintype K] [Fintype R]
    (s : ((K ⊕ K) ⊕ R) → Finset α) (l k : ℕ) (hc : Fintype.card ((K ⊕ K) ⊕ R)=l)
    (hd : Fintype.card K=k) (x y z : ℕ)
    (hx : ∀ i : K, (s (.inl (.inl i))).card=x)
    (hy : ∀ i : K, (s (.inl (.inr i))).card=y)
    (hz : ∀ i : R, (s (.inr i)).card=z) :
    mass s = k*x + k*y + (l-(k+k))*z := by
  unfold mass
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp_rw [hx,hy,hz]
  simp only [sum_const,card_univ, hd, nsmul_eq_mul]
  simp only [Fintype.card_sum, hd] at hc
  simp [← hc]

lemma mass_border : mass (border 0) = 4060^3 := by
  have hx (i : Key) : (border 0 (gx i)).card=1 := Eq.trans
    (congrArg Finset.card (border_inx i)) (card_singleton _)
  have hy (i : Key) : (border 0 (gy i)).card=0 :=
    congrArg Finset.card (border_iny i)
  have hz (i : AllAux ⊕ Spare) : (border 0 (.inr i)).card=0 :=
    congrArg Finset.card (border_inr i)
  exact (mass_groups (K:=Key) (R:=AllAux ⊕ Spare)
    (border 0) tower (4060^3) card_role card_key 1 0 0 hx hy hz).trans (by simp)

lemma mass_sink : mass sink + 4060^3 = tower*mcol := by
  have hh : (univ \ ({pole}:Finset Blocks)).card = mcol-1 := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,card_block,card_singleton]
  have hu : (univ:Finset Blocks).card=mcol := card_univ.trans card_block
  have hd := mass_groups (K:=Key) (R:=AllAux ⊕ Spare) sink tower (4060^3)
    card_role card_key mcol (mcol-1) mcol (fun _ => hu) (fun _ => hh) (fun _ => hu)
  simp only [hd]; norm_num [tower,mcol]

def correction : Role → Space Blocks
  | .inl (.inr k) => (bases (gy k)).v pole
  | _ => 0

def recover (x : Role→ℂ) : Role→ℂ
  | .inl (.inl k) => x (gy k)
  | .inl (.inr k) => -x (gx k)
  | r => x r

-- monomial point move witnessing recovery
def pull : Role → Role
  | .inl (.inl k) => gy k
  | .inl (.inr k) => gx k
  | r => r
def flipSign : Role → ℚ
  | .inl (.inr _) => -1
  | _ => 1
def recoverM : Matrix Role Role ℚ := fun i j =>
  if j=pull i then flipSign i else 0

lemma recover_eq : actPoint recoverM = recover := by
  funext x r
  unfold actPoint
  rw [sum_eq_single (pull r)]
  · rcases r with (k|k)|r <;> simp [recoverM,pull,recover,flipSign]
  · intro i _ hi; simp [recoverM,hi]
  · simp

theorem netEffect (f : ℕ) (x : Data Blocks Role f) :
    point f recover
      (multiAct f (fun r => shift (correction r))
        (withFrame bases sink f (point f exchange x))) =
    multiAct f (fun _ => kernel Blocks) (withFrame bases (border 0) f x) := by
  have hneg (x : Sky Blocks f→ℂ) : matAct f (kernel Blocks) (-x) =
      -(matAct f (kernel Blocks) x) := by rw [matAct, Matrix.mulVec_neg]; rfl
  funext r
  rcases r with (k|k)|r
  · change matAct f (shift (correction (gy k))) (matAct f (frame (bases (gy k)) _) (x (gx k))) =
      matAct f (kernel Blocks) (matAct f (frame (bases (gx k)) (border 0 (gx k))) (x (gx k)))
    rw [matAct_mul,matAct_mul,border_inx,terminal_calc]
    rfl
  · change -(matAct f (shift (0:Space Blocks))
      (matAct f (frame (bases (gx k)) univ) (-(x (gy k))))) =
      matAct f _ (matAct f (frame (bases (gy k)) (border 0 (gy k))) (x (gy k)))
    rw [border_iny,shift_zero,frame_zero,matAct_one,matAct_one,frame_univ,hneg,neg_neg]
  · change matAct f (shift (0:Space Blocks))
      (matAct f (frame (bases (.inr r)) univ) (x (.inr r))) =
      matAct f _ (matAct f (frame (bases (.inr r)) (border 0 (.inr r))) (x (.inr r)))
    rw [border_inr,shift_zero,frame_zero,matAct_one,matAct_one,frame_univ]

def nMoves : ℕ := tower*mcol-bankSave

private lemma c_tally (a b c : ℕ) (h : a + b = c + 2*(3*stageLoss))
  (g : b=4060^3) (k : c+4060^3=tower*mcol) : (a+0)+0=nMoves := by
  unfold nMoves; norm_num [tower,mcol,bankSave,stageLoss] at *; omega

/-- Finite certificate. No operation count for point work here: the word and matrices
  in the point moves have fixed size. It holds on arbitrary values in *all* roles,
  for any f columns of bits. -/
theorem certificate :
    ∃ p : PWord Blocks Role,
    tally p = nMoves ∧
      ∀ f (x : Data Blocks Role f), walk f p x = multiAct f (fun _ => kernel Blocks) x := by
  obtain ⟨p,hp,he⟩ := all_stages
  obtain ⟨q,hq,hf⟩ := translateAll correction
  refine ⟨(p++q)++[.localM recoverM],?_,?_⟩
  · rw [tally_append,tally_append,hq]
    change (_+0)+0=nMoves
    exact c_tally (tally p) _ _ hp mass_border mass_sink
  · intro f x
    rw [walk_append, walk_append, hf]
    obtain ⟨y,rfl⟩ := framed_surj bases (border 0) f x
    rw [he]
    simp only [walk, List.foldl_cons, List.foldl_nil, Move.go, recover_eq]
    exact netEffect f y
end
end PowerSaving.Cluster

end OAI
