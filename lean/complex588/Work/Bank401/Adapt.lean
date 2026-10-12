import Work.GFrame.Clifford.Climb
import Work.GFrame.Engine.Free
import Work.GFrame.Labels.BXMap

/-!
# (key: bank-401, L2) Pattern banks: bank frames `A * pk U * B` (`A` free), gauged step, bank adapter, pad

A bank of the #401 layout holds its frame in the form `A * pk U * B` (`A` free, `U` = the coordinates already climbed,
`|U|` = the load, `B` = the bank's start frame, never changed).  A gauged use applies `Wn = C * pk R * C'`
(`C`, `C'` free, `|R| = 9 - e`).

* `cperm τ`        the coordinate permutation `x ↦ x ∘ τ` as an additive bijection (`permMat` of it is free);
* `pk_cperm`       `permMat (cperm τ) * pk s = pk (s.map τ) * permMat (cperm τ)`;
* `gauged_step`    `X.Φ ⟨G, univ⟩ = A * pk R * A' * X.Φ ⟨G, s⟩` with `A`, `A'` free, `|R| = card H - |s|`;
* `gauged_Wn`      the `Wn` of an invocation with an entrance label (`GInvE`) has the form `A * pk R * A'`;
* `bank_start`     the start frame `B` is `1 * pk ∅ * B`;
* `bank_adapt`     **K6**: if `|U| + |R| ≤ card α` there is a free `P` (an address permutation between free
                   adapters) with `C * pk R * C' * (P * (A * pk U * B)) = A2 * pk U2 * B`, `A2` free, `U ⊆ U2`,
                   `|U2| = |U| + |R|`;
* `bank_pad`       **K7**: from `A * pk U * B` to `kernel α * B` is ONE block of rank `card α - |U|` (`1 ≤ |U|`);
* `bank_full`      from `A * pk univ * B` to `kernel α * B` is free.
(`pk_union` is Jacob's, `Work/GFrame/Clifford/Core.lean`.)

The entrance gauges and residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the exact bank patterns
are Lydakis's (#275).  The engine (`pk`, `kg`, `core`, `Free`, `gstep_of_factor`) is Jacob Sussman's.  No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving
namespace B401
open Binary Matrix Finset GF
noncomputable section

section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the coordinate permutation `x ↦ x ∘ τ`, as an additive bijection. -/
def cperm (τ : Equiv.Perm α) : APerm α where
  π := { toFun := fun x k => x (τ k)
         invFun := fun x k => x (τ.symm k)
         left_inv := fun x => by funext k; simp
         right_inv := fun x => by funext k; simp }
  add := fun _ _ => rfl

lemma cperm_apply (τ : Equiv.Perm α) (x : Space α) (k : α) : (cperm τ).π x k = x (τ k) := rfl

lemma cperm_symm_apply (τ : Equiv.Perm α) (x : Space α) (k : α) :
    (cperm τ).π.symm x k = x (τ.symm k) := rfl

lemma free_cperm (τ : Equiv.Perm α) : Free (permMat (cperm τ)) := Free.perm _

lemma lum_comp (τ : Equiv.Perm α) (x : Space α) : lum (fun k => x (τ k)) = lum x := by
  unfold lum
  exact Equiv.prod_comp τ (fun i => tint (x i))

/-- **A coordinate permutation moves the kernel on `s` to the kernel on `s.map τ`.** -/
theorem pk_cperm (τ : Equiv.Perm α) (s : Finset α) :
    permMat (cperm τ) * pk s = pk (s.map τ.toEmbedding) * permMat (cperm τ) := by
  ext x y
  rw [permMat_mul_apply, mul_permMat_apply, pk_apply, pk_apply, Finset.card_map]
  have hc : (∀ k, k ∉ s → (cperm τ).π x k = y k) ↔
      (∀ j, j ∉ s.map τ.toEmbedding → x j = (cperm τ).π.symm y j) := by
    constructor
    · intro h j hj
      have hk : τ.symm j ∉ s := fun hm => hj (Finset.mem_map.mpr ⟨_, hm, by simp⟩)
      have e := h _ hk
      rw [cperm_apply, Equiv.apply_symm_apply] at e
      rw [cperm_symm_apply]
      exact e
    · intro h k hk
      have hj : τ k ∉ s.map τ.toEmbedding := by
        rw [Finset.mem_map]
        rintro ⟨a, ha, e⟩
        rw [Equiv.toEmbedding_apply] at e
        exact hk (τ.injective e ▸ ha)
      have e := h _ hj
      rw [cperm_symm_apply, Equiv.symm_apply_apply] at e
      rw [cperm_apply]
      exact e
  by_cases h : ∀ k, k ∉ s → (cperm τ).π x k = y k
  · rw [if_pos h, if_pos (hc.mp h)]
    congr 1
    have e : (cperm τ).π x + y = fun k => (x + (cperm τ).π.symm y) (τ k) := by
      funext k
      simp [cperm_apply, cperm_symm_apply]
    rw [e, lum_comp]
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]

/-- **The gauged step.**  In one base `G`, the full label is ONE kernel block on the coordinates
`liftS univ \ liftS s` (between free adapters) after the entrance label `⟨G, s⟩`. -/
theorem gauged_step {H : Type} [Fintype H] [DecidableEq H] (X : BXMap H α) (G : APerm H) (s : Finset H) :
    ∃ (A A' : CMat α) (R : Finset α), Free A ∧ Free A' ∧ R.card = Fintype.card H - s.card ∧
      X.Φ ⟨G, univ⟩ = A * pk R * A' * X.Φ ⟨G, s⟩ := by
  have hsub : X.liftS s ⊆ X.liftS univ := X.mono (Finset.subset_univ s)
  refine ⟨kg (X.liftG G), kg (apInv (X.liftG G)), X.liftS univ \ X.liftS s, free_kg _, free_kg _, ?_, ?_⟩
  · rw [X.card (Finset.subset_univ s), Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]
  · show core (X.liftG G) (X.liftS univ) = _ * core (X.liftG G) (X.liftS s)
    rw [core_nested _ hsub, pk_eq_blockMat]

/-- **`Wn` of a gauged invocation.**  If `X.Φ E * N = 1` and `X.Φ ⟨E.G, univ⟩ = Wn * X.Φ E` (the hypotheses of
`GInvE`), then `Wn = A * pk R * A'` with `A`, `A'` free and `|R| = card H - dim E`. -/
theorem gauged_Wn {H : Type} [Fintype H] [DecidableEq H] (X : BXMap H α) (E : SLbl H) {N Wn : CMat α}
    (hN : X.Φ E * N = 1) (hW : X.Φ ⟨E.G, univ⟩ = Wn * X.Φ E) :
    ∃ (A A' : CMat α) (R : Finset α), Free A ∧ Free A' ∧ R.card = Fintype.card H - E.dim ∧
      Wn = A * pk R * A' := by
  obtain ⟨A, A', R, hA, hA', hR, he⟩ := gauged_step X E.G E.s
  refine ⟨A, A', R, hA, hA', hR, ?_⟩
  have hE : (⟨E.G, E.s⟩ : SLbl H) = E := rfl
  rw [hE] at he
  calc Wn = Wn * (X.Φ E * N) := by rw [hN, Matrix.mul_one]
    _ = X.Φ ⟨E.G, univ⟩ * N := by rw [hW, Matrix.mul_assoc]
    _ = A * pk R * A' * (X.Φ E * N) := by rw [he, Matrix.mul_assoc]
    _ = A * pk R * A' := by rw [hN, Matrix.mul_one]

/-- **The start of a bank**: its start frame `B` is `1 * pk ∅ * B`. -/
theorem bank_start (B : CMat α) : B = 1 * pk (∅ : Finset α) * B := by
  rw [pk_empty, Matrix.one_mul, Matrix.one_mul]

/-- **K6, the bank adapter.**  A free address permutation `P` before the invocation moves the residual
coordinates `R` of the gauged step off the coordinates `U` already climbed in the bank. -/
theorem bank_adapt {A B C C' : CMat α} (hA : Free A) (hC : Free C) (hC' : Free C')
    (U R : Finset α) (hc : U.card + R.card ≤ Fintype.card α) :
    ∃ P, Free P ∧ ∃ (A2 : CMat α) (U2 : Finset α), Free A2 ∧ U ⊆ U2 ∧ U2.card = U.card + R.card ∧
      C * pk R * C' * (P * (A * pk U * B)) = A2 * pk U2 * B := by
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  obtain ⟨Ci, hCi, -, hC'Ci⟩ := free_inv hC'
  have hUc : R.card ≤ (univ \ U).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ]
    omega
  obtain ⟨T, hTU, hTc⟩ := Finset.exists_subset_card_eq hUc
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T R (hTc.trans rfl)
  -- `pk R * Pm = Pm * pk T` with `Pm = permMat (cperm σ)`
  have hPi : pk R * permMat (cperm σ) = permMat (cperm σ) * pk T := by
    rw [pk_cperm, hσ]
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro a ha hu
    exact (Finset.mem_sdiff.mp (hTU ha)).2 hu
  refine ⟨Ci * permMat (cperm σ) * Ai, Free.mul (Free.mul hCi (free_cperm σ)) hAi,
    C * permMat (cperm σ), T ∪ U, Free.mul hC (free_cperm σ), Finset.subset_union_right, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hTc, Nat.add_comm]
  · have e : C * pk R * C' * (Ci * permMat (cperm σ) * Ai * (A * pk U * B))
        = C * (pk R * permMat (cperm σ)) * (Ai * A) * pk U * B := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C' Ci, hC'Ci, Matrix.one_mul]
    rw [e, hAiA, Matrix.mul_one, hPi, pk_union T U hdisj]
    simp only [Matrix.mul_assoc]

/-- **K7, the pad**: from `A * pk U * B` to `kernel α * B` is ONE block of rank `card α - |U|`. -/
theorem bank_pad {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) {A : CMat α} (hA : Free A) (B : CMat α)
    (U : Finset α) (h1 : U.card < Fintype.card α) (h2 : 1 ≤ U.card) :
    GStep l (A * pk U * B) (kernel α * B) (fun φ => φ (Fintype.card α - U.card)) := by
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  have hk : (univ \ U).card = Fintype.card α - U.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ]
  have h := gstep_of_factor l (A * pk U * B) ((OBase.canonical α).fam (univ \ U))
    ((OBase.canonical α).fam_indep _) (Free.one) hAi (by omega) (by omega)
  have e : 1 * blockMat ((OBase.canonical α).fam (univ \ U)) * Ai * (A * pk U * B) = kernel α * B := by
    rw [← pk_eq_blockMat, ← pk_univ, pk_sdiff (Finset.subset_univ U)]
    have e2 : 1 * pk (univ \ U) * Ai * (A * pk U * B) = pk (univ \ U) * (Ai * A) * pk U * B := by
      simp only [Matrix.mul_assoc, Matrix.one_mul]
    rw [e2, hAiA, Matrix.mul_one]
  rw [e, hk] at h
  exact h

/-- a full bank (load `card α`, no pad): to `kernel α * B` is free. -/
theorem bank_full {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) {A : CMat α} (hA : Free A) (B : CMat α) :
    GStep l (A * pk univ * B) (kernel α * B) (fun _ => 0) := by
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  have h := gstep_free hAi l (A * pk univ * B)
  have e : Ai * (A * pk univ * B) = kernel α * B := by
    rw [← pk_univ]
    simp only [← Matrix.mul_assoc]
    rw [hAiA, Matrix.one_mul]
  rw [e] at h
  exact h

end
end
end B401
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.B401.pk_cperm
#print axioms OAI.PowerSaving.B401.gauged_step
#print axioms OAI.PowerSaving.B401.gauged_Wn
#print axioms OAI.PowerSaving.B401.bank_start
#print axioms OAI.PowerSaving.B401.bank_adapt
#print axioms OAI.PowerSaving.B401.bank_pad
#print axioms OAI.PowerSaving.B401.bank_full
