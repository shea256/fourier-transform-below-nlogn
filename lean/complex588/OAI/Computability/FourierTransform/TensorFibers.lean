import OAI.Computability.FourierTransform.BitLayout

namespace OAI

namespace PowerSaving.Binary
open Finset Matrix
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem choose_pivot {z : Space α} (hz : z≠0) : ∃ i, z i=1 := by
  by_contra! h
  exact hz (funext fun i => (bit_cases _).resolve_right (h i))

abbrev Minus {α : Type*} (i : α) := {j : α // j ≠ i}

def peel (i : α) (z : Space α) : Space α ≃ Space (Minus i) × F where
  toFun x := (fun j => x j.1 + z j.1*x i, x i)
  invFun q j := if h : j=i then q.2 else q.1 ⟨j,h⟩ + z j*q.2
  left_inv x := by ext j; by_cases j=i <;> simp [*,add_assoc]
  right_inv q := by
    apply Prod.ext
    · funext j; simp [j.property,add_assoc]
    · simp

omit [Fintype α] in
theorem peel_shift (i : α) (z : Space α) (hz : z i=1) (x : Space α) :
    peel i z (x+z) = ((peel i z x).1,(peel i z x).2+1) := by
  apply Prod.ext
  · ext j
    change x _ + z _ + z _ * (x i + z i) = _
    rw [hz, _root_.mul_add, mul_one]
    dsimp [peel]
    simp [add_comm, add_left_comm]
    simp [← add_assoc]
  · change x i + z i = x i + 1
    rw [hz]

theorem bit_flip (x y : F) : x+1=y ↔ x≠y := by
  rcases bit_cases x with rfl|rfl <;> rcases bit_cases y with rfl|rfl <;> decide

theorem peel_dir (i : α) (z : Space α) (hz : z i=1)
    (x y : Space α) :
    dir z x y = (if (peel i z x).1 = (peel i z y).1 then (1:ℂ) else 0) *
      littleC ((peel i z x).2) ((peel i z y).2) := by
  have ha : x=y ↔ (peel i z x).1 = (peel i z y).1 ∧
      (peel i z x).2 = (peel i z y).2 :=
    (peel i z).injective.eq_iff.symm.trans Prod.ext_iff
  have hb : x+z=y ↔ (peel i z x).1 = (peel i z y).1 ∧
      (peel i z x).2 ≠ (peel i z y).2 := by
    rw [← (peel i z).injective.eq_iff, peel_shift _ _ hz, Prod.ext_iff]
    exact and_congr_right (fun _ => bit_flip _ _)
  simp only [dir,Matrix.add_apply,Matrix.smul_apply,one_apply,shift,ha,hb,littleC, smul_eq_mul]
  by_cases h : (peel i z x).1 = (peel i z y).1 <;>
    by_cases h' : (peel i z x).2 = (peel i z y).2 <;> simp [h,h']

def skySplit (i : α) (z : Space α) (f : ℕ) :
    Sky α f ≃ Sky (Minus i) f × Bits f where
  toFun x := (fun k => (peel i z (x k)).1, fun k => (peel i z (x k)).2)
  invFun x k := (peel i z).symm (x.1 k,x.2 k)
  left_inv x := by simp
  right_inv x := by apply Prod.ext <;> funext k <;> simp

def peelBook (i : α) (z : Space α) (r f : ℕ) :
    Grid α r f ≃ Grid (Minus i) r f × Bits f where
  toFun x := ((x.1,(skySplit i z f x.2).1),(skySplit i z f x.2).2)
  invFun p := (p.1.1,(skySplit i z f).symm (p.1.2,p.2))
  left_inv x := by simp
  right_inv p := by simp

theorem product_dir (i : α) (z : Space α) (hz : z i=1) (f : ℕ)
    (x y : Sky α f) :
    let e := skySplit i z f
    digitProd (fun _ : Fin f => dir z) x y =
    if (e x).1=(e y).1 then kernel (Fin f) (e x).2 (e y).2 else 0 := by
  intro e
  rw [digitProd_apply]
  simp_rw [peel_dir i z hz]
  rw [prod_mul_distrib]
  -- delta compares functions Fin f → Space ...
  change (∏ k:Fin f, (if (e x).1 k=(e y).1 k then (1:ℂ) else 0))*kernel (Fin f) (e x).2 (e y).2 = _
  rw [prod_delta (κ:=fun _ : Fin f => Space (Minus i))]
  split <;> simp_all

lemma act_dir (i : α) (z : Space α) (hz : z i=1) (f : ℕ)
    (x : Sky α f → ℂ) (j : Sky α f) :
    let e := skySplit i z f
    matAct f (dir z) x j = ripple f (fun k => x (e.symm ((e j).1,k))) (e j).2 := by
  intro e
  change ∑ y, digitProd (fun _ => dir z) j y * x y =
    ∑ k, kernel (Fin f) _ k * x _
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have h (k : Sky (Minus i) f × Bits f) :
      digitProd (fun _ : Fin f => dir z) j (e.symm k) =
        if k.1=(e j).1 then kernel (Fin f) (e j).2 k.2 else 0 := by
    rw [product_dir i z hz]
    change (if _ = (e (e.symm k)).1 then kernel _ _ (e (e.symm k)).2 else 0)=_
    rw [e.apply_symm_apply]
    congr 1
    all_goals apply propext eq_comm
  rw [sum_eq_single (e j).1]
  · simp_rw [h]; simp
  · intro l _ hl
    apply sum_eq_zero; intro k hk
    rw [h,ite_eq_right]; simp; exact hl
  · simp

lemma peel_act (i : α) (z : Space α) (hz : z i=1)
    (r f : ℕ) (x : Grid α r f → ℂ) (j : Grid α r f) :
    let e := peelBook i z r f
    matAct f (dir z) (fun k => x (j.1,k)) j.2 =
    ripple f (fun k => x (e.symm ((e j).1,k))) (e j).2 := by
  exact act_dir i z hz f (fun k => x (j.1,k)) j.2

lemma act_shift (z : Space α) (f : ℕ) (x : Sky α f→ℂ)
    (j : Sky α f) :
    matAct f (shift z) x j=x (fun k => j k+z) := by
  change ∑ i, digitProd (fun _ : Fin f => shift z) j i * x i = _
  have h (i : Sky α f) : digitProd (fun _ : Fin f => shift z) j i =
      if (fun k => j k+z)=i then 1 else 0 := prod_delta (κ:=fun _ : Fin f => Space α) _ _
  simp_rw [h]
  simp [ite_mul]

lemma card_minus (i : α) :
    Fintype.card (Minus i) + 1 = Fintype.card α := by
  simp [Minus, Fintype.card_subtype_compl]
  have h : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

end
end PowerSaving.Binary

end OAI
