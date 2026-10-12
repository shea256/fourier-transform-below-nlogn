import Work.Block.Split

/-!
# Block moves, part 2: cutting an array into fibres along `r` directions at once

(agent key: block-engine).  Generalises upstream `TensorFibers.lean` (`peel`, `skySplit`,
`peelBook`, `product_dir`, `act_dir`, `peel_act`) from one direction to a splitting
`S : Split α β (Fin r)`.

* `flat r f`      the `f` columns of `r` block bits, read as ONE string of `r*f` bits
                  (the index set of one recursive call of order `r*f`);
* `Split.peel`    `Grid α r' f ≃ Grid β r' f × Bits (r*f)`: fibre label, position in the fibre;
* `Split.act`     the block matrix `S.lift (kernel (Fin r))`, applied to all `f` columns, is the
                  order-`r*f` kernel (`ripple (r*f)`) on every fibre.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

/-- `f` columns of `r` bits as one string of `r*f` bits, in upstream's serial order. -/
lemma flat_len (r f : ℕ) : (Layout.std r).n*f+0 = r*f := rfl

def flat (r f : ℕ) : Sky (Fin r) f ≃ Bits (r*f) :=
  (Equiv.uniqueProd (Sky (Fin r) f) (Bits 0)).symm.trans
    (serial (Layout.std r) 0 f (flat_len r f))

lemma bits_zero_loc (b : Bits 0) : (bits 0).loc b = 0 := by
  have h := (bits 0).bd b
  rw [bits_len] at h
  omega

lemma flat_apply (r f : ℕ) (s : Sky (Fin r) f) :
    flat r f s = serial (Layout.std r) 0 f (flat_len r f)
      ((Equiv.uniqueProd (Sky (Fin r) f) (Bits 0)).symm s) := rfl

lemma kernel_zero (a b : Bits 0) : kernel (Fin 0) a b = 1 := by
  simp [kernel]

lemma flat_code (r f : ℕ) (s : Sky (Fin r) f) :
    (bits (r*f)).loc (flat r f s) = (bodyOrder (Layout.std r) f).loc s := by
  rw [flat_apply, serial_code]
  change (bits 0).loc _ * (bodyOrder (Layout.std r) f).n + (bodyOrder (Layout.std r) f).loc s = _
  rw [bits_zero_loc, zero_mul, zero_add]

lemma flat_kernel (r f : ℕ) (s t : Sky (Fin r) f) :
    kernel (Fin (r*f)) (flat r f s) (flat r f t) =
      digitProd (fun _ : Fin f => kernel (Fin r)) s t := by
  rw [flat_apply, flat_apply, kernel_serial, kernel_zero, one_mul]
  rfl

section
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- The splitting applied to every column. -/
def Split.sky (S : Split α β γ) (f : ℕ) : Sky α f ≃ Sky β f × Sky γ f where
  toFun x := (fun k => (S.e (x k)).1, fun k => (S.e (x k)).2)
  invFun x k := S.e.symm (x.1 k, x.2 k)
  left_inv x := by simp
  right_inv x := by apply Prod.ext <;> funext k <;> simp

variable {r : ℕ}

/-- Fibre label and position inside the fibre (generalises upstream `peelBook`). -/
def Split.peel (S : Split α β (Fin r)) (r' f : ℕ) :
    Grid α r' f ≃ Grid β r' f × Bits (r*f) where
  toFun x := ((x.1,(S.sky f x.2).1), flat r f (S.sky f x.2).2)
  invFun p := (p.1.1,(S.sky f).symm (p.1.2,(flat r f).symm p.2))
  left_inv x := by simp
  right_inv p := by simp

theorem Split.product (S : Split α β (Fin r)) (f : ℕ) (x y : Sky α f) :
    digitProd (fun _ : Fin f => S.lift (kernel (Fin r))) x y =
    if (S.sky f x).1=(S.sky f y).1 then
      kernel (Fin (r*f)) (flat r f (S.sky f x).2) (flat r f (S.sky f y).2) else 0 := by
  rw [digitProd_apply, flat_kernel, digitProd_apply]
  have h (k : Fin f) : S.lift (kernel (Fin r)) (x k) (y k) =
      (if (S.sky f x).1 k = (S.sky f y).1 k then (1:ℂ) else 0) *
        kernel (Fin r) ((S.sky f x).2 k) ((S.sky f y).2 k) := by
    change (if (S.e (x k)).1 = (S.e (y k)).1 then
      kernel (Fin r) (S.e (x k)).2 (S.e (y k)).2 else 0) =
      (if (S.e (x k)).1 = (S.e (y k)).1 then (1:ℂ) else 0) *
        kernel (Fin r) (S.e (x k)).2 (S.e (y k)).2
    split <;> simp
  simp_rw [h]
  rw [prod_mul_distrib, prod_delta (κ:=fun _ : Fin f => Space β)]
  split <;> simp

lemma Split.act_sky (S : Split α β (Fin r)) (f : ℕ)
    (x : Sky α f → ℂ) (j : Sky α f) :
    matAct f (S.lift (kernel (Fin r))) x j =
      ripple (r*f) (fun k => x ((S.sky f).symm ((S.sky f j).1,(flat r f).symm k)))
        (flat r f (S.sky f j).2) := by
  let E : Sky α f ≃ Sky β f × Bits (r*f) :=
    (S.sky f).trans (Equiv.prodCongr (Equiv.refl _) (flat r f))
  change ∑ y, digitProd (fun _ => S.lift (kernel (Fin r))) j y * x y =
    ∑ k, kernel (Fin (r*f)) _ k * x _
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  have h (k : Sky β f × Bits (r*f)) :
      digitProd (fun _ : Fin f => S.lift (kernel (Fin r))) j (E.symm k) =
        if k.1=(S.sky f j).1 then kernel (Fin (r*f)) (flat r f (S.sky f j).2) k.2 else 0 := by
    rw [Split.product]
    have e1 : (S.sky f (E.symm k)).1 = k.1 := by simp [E]
    have e2 : flat r f (S.sky f (E.symm k)).2 = k.2 := by simp [E]
    rw [e1, e2]
    congr 1
    exact propext eq_comm
  rw [sum_eq_single (S.sky f j).1]
  · simp_rw [h]
    simp only [↓reduceIte]
    rfl
  · intro l _ hl
    apply sum_eq_zero; intro k _
    rw [h, if_neg hl, zero_mul]
  · intro h'; exact absurd (mem_univ _) h'

/-- **One block = the order-`r*f` kernel on every fibre** (generalises upstream `peel_act`). -/
lemma Split.act (S : Split α β (Fin r)) (r' f : ℕ) (x : Grid α r' f → ℂ) (j : Grid α r' f) :
    matAct f (S.lift (kernel (Fin r))) (fun k => x (j.1,k)) j.2 =
    ripple (r*f) (fun k => x ((S.peel r' f).symm (((S.peel r' f) j).1,k)))
      ((S.peel r' f) j).2 :=
  S.act_sky f (fun k => x (j.1,k)) j.2

end
end
end PowerSaving.Binary
end OAI

#print axioms OAI.PowerSaving.Binary.Split.act
