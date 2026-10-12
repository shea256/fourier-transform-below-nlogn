import Submission.Work.GCert.Data.G5Glue401
import Submission.Work.GCert.Data.InstC401Gg5
import Submission.Work.Bridge401.End

/-!
# THE SEAM for the Fourier transfer: our kernel program in OpenAI's `hills_program` form

New file, not a copy of an OpenAI file: Jacob Sussman's Work/FourierE8/Seam.lean (Apache-2.0) for the
entrance-gauged nine-stage layout of PR #401 (Dugongue, CrocSwap/integer-mult-bounds; on jacklightChen's PR #377 layout;
Lean: gauged halves DFT Bridge3, network DFT New Sums, end theorem Work/Bridge401/End.lean), certificate `GXD.G5`,
suffix `C401G5`; written by tools/mkseam401.py (DFT Lean). Sections 2 and 3 of Jacob's file are replaced by one theorem
that calls `GX.engine_of_ginv_401`.  It contains lines 95-99 of
lean/OAI/Computability/FourierTransform/TensorProgram.lean (the statement of `hills_program`) and line 114 of
lean/OAI/Computability/FourierTransform/TensorSaving.lean (the definition of `hills`) of github.com/openai/math
(commit fd4aeeb, Apache-2.0), with `hills`, `alpha` replaced by `hillsC401G5`, `alphaC401G5`.

Twin of Work/Fourier/Seam.lean for the certificate `GXD.G5` (label width 9; Work/GCert/Data/C401Gg5.lean) in the
place of `GXD.P193`: the same text with the names and numbers of that certificate, and with every declared name
changed (`C401G5` in the place of `Z`, `C401G5` appended to the other names, namespace `SeamC401G5` for `Seam`), so that the
two files have no declaration in common.  This file imports the C401G5 instance only, not the published seam; that
is why the general lemmas of sections 1 and 2 are stated here again, under new names, with the same proofs.

OpenAI's Fourier proof uses the tensor network through ONE theorem, `RAM.hills_program`
(OAI/Computability/FourierTransform/TensorProgram.lean:95), with ONE call site (`Bench.gleamT`,
SectorAlgorithm.lean:45), plus four envelope facts (`hills_pos`, `hills_mono`, `hills_le`, `hills_real`,
TensorSaving.lean:116-133) and the number facts `alpha_pos`, `alpha_lt`, `Skies.alpha_theta`,
`Skies.decimal_range`.  This file gives all of them at OUR exponent

  `alphaC401G5 = 1 - 10221077/10^10`      (OpenAI: `alpha = 1 - 2/10^11`),

under OpenAI's names with `C401G5` after `hills` / `alpha`, in OpenAI's own namespaces.

* `GX.engine_of_ginvC401G5`, `GX.engine_of_halvesC401G5`   twins of `GX.wht_of_ginv`, `GX.wht_of_halves`
  (Work/GCert/Chain/End.lean) ending in the kernel program (`RAM.engine_program_ggroup_list`) instead of the
  Walsh-Hadamard corollary: every colour `cl`, both modes `m`, every batch of inputs.
* `SeamC401G5.engine_C401Gg5x_of_scal`, `_of_ids`   twins of `WHT.wht_C401Gg5x_of_scal`, `_of_ids`
  (Work/GCert/Data/C401Gg5.lean): same certificate `GXD.G5`, same unit list, same rate fact
  `BlockAccounting.fold_C401Gg5x`, fill parameter `s = 40`.
* `RAM.hillsC401G5_program`   THE SEAM, closed with the kernel-checked scalar half `GXD.G5.scalOK`.
* `RAM.envelope_program_geC401G5`   the same at every exponent `z ≥ alphaC401G5`.

No `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
noncomputable section

/-! ## 1. The exponent and the envelope facts -/

/-- Our exponent, in the place of OpenAI's `alpha` (TensorSaving.lean:81). -/
def alphaC401G5 : ℝ := 1 - 10221077/(10:ℝ)^10

theorem alphaC401G5_pos : 0 < alphaC401G5 := by norm_num [alphaC401G5]
theorem alphaC401G5_lt : alphaC401G5 < 1 := by norm_num [alphaC401G5]

lemma envelope_monoC401G5 (z : ℝ) (hz : 0 ≤ z) {a b : ℕ} (h : a ≤ b) : envelope z a ≤ envelope z b := by
  unfold envelope
  gcongr

-- `envelope_le` (for `z ≤ 1`) and `envelope_real` (for `0 ≤ z`) already exist: Work/Block/WHT.lean:26, :31.

lemma envelope_mono_expC401G5 {z z' : ℝ} (h : z ≤ z') (k : ℕ) : envelope z k ≤ envelope z' k := by
  unfold envelope
  exact Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le (by simp) h)

/-- Natural envelope at our exponent, in the place of OpenAI's `hills` (TensorSaving.lean:114). -/
def hillsC401G5 (k : ℕ) := Nat.ceil (((k:ℝ)+1)^alphaC401G5)

lemma hillsC401G5_eq_envelope : hillsC401G5 = envelope alphaC401G5 := rfl

lemma hillsC401G5_pos (k : ℕ) : 1≤hillsC401G5 k := envelope_pos alphaC401G5 k

lemma hillsC401G5_mono {a b : ℕ} (h : a≤b) : hillsC401G5 a ≤ hillsC401G5 b := envelope_monoC401G5 alphaC401G5 alphaC401G5_pos.le h

lemma hillsC401G5_le (k : ℕ) : hillsC401G5 k ≤ k+1 := envelope_le alphaC401G5 alphaC401G5_lt.le k

lemma hillsC401G5_real (k : ℕ) : (hillsC401G5 k:ℝ) ≤ 2*((k:ℝ)+1)^alphaC401G5 := envelope_real alphaC401G5 alphaC401G5_pos.le k

/-! ## 3. The certificate `GXD.G5` with entrance gauges (PR #401 layout) -/

namespace SeamC401G5
open Binary Matrix Finset RAM RAM.Ty
universe U

/-- **Kernel program at `1 - 10221077/10^10`** for the certificate `GXD.G5`: `GX.engine_of_ginv_401` with its gauged
invocation package `GXD.G5.ginv` (`GXD.ginvOf` of its kernel checks), its bank schedule `GXD.G5.sched` (`Work/GCert/Data/G5Glue401.lean`), the
unit list `BlockAccounting.blocksC401Gg5x` and the rate fact `BlockAccounting.fold_C401Gg5x` (fill parameter `s = 40`). -/
theorem engine_C401Gg5x (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 10221077/(10:ℝ)^10) (k i)) :=
  GX.engine_of_ginv_401 GXD.G5.ginv GXD.G5.h9 GXD.G5.sched GXD.G5.fitsS
    73 14353 rfl GXD.G5.width (by norm_num) BlockAccounting.blocksC401Gg5x
    (fun φ => by rw [GXD.G5.price φ]; exact BridgeRate.C401Gg5.unit_cost_x φ)
    40 (1 - 10221077/(10:ℝ)^10) (by norm_num) (by norm_num) BlockAccounting.fold_C401Gg5x cl m k v

end SeamC401G5

/-! ## 4. THE SEAM -/

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- **THE SEAM.**  OpenAI's `hills_program` (TensorProgram.lean:95) word for word, with `hillsC401G5`
(exponent `1 - 10221077/10^10`) in the place of `hills` (exponent `1 - 2/10^11`): the kernel program of
the certificate `GXD.G5` (the one behind `WHT.wht_main_block_C401Gg5x`), for every colour,
both modes and every batch of inputs, in `2^k * hillsC401G5 k` operations. -/
theorem hillsC401G5_program (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hillsC401G5 (k i)) :=
  SeamC401G5.engine_C401Gg5x cl m k v

/-- **General exponent**: the same at every exponent `z ≥ alphaC401G5`, envelope `⌈(k+1)^z⌉`. -/
theorem envelope_program_geC401G5 (z : ℝ) (hz : alphaC401G5 ≤ z) (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  (hillsC401G5_program cl m k v).mono fun i => Nat.mul_le_mul_left _ (envelope_mono_expC401G5 hz (k i))

end RAM

/-! ## 5. Number facts for the copy of `Main.lean` -/

namespace SeamC401G5

lemma alphaC401G5_lt_alpha : alphaC401G5 < alpha := by norm_num [alphaC401G5, alpha]

/-- for `Skies.alpha_theta` (Main.lean:39): below the paper's exponent. -/
lemma alphaC401G5_theta : alphaC401G5 < theta := alphaC401G5_lt_alpha.trans Skies.alpha_theta

/-- for `Skies.decimal_range` (Main.lean:59). -/
lemma alphaC401G5_decimal : alphaC401G5 < decimalExponent ∧ decimalExponent < 1 := by
  norm_num [decimalExponent, alphaC401G5]

/-- Target exponent of the final Fourier statement: strictly above `alphaC401G5`, so that the
`(log log n)^2` factor of the reduction is absorbed. -/
def targetExponentC401G5 : ℝ := 1 - 10221076/(10:ℝ)^10
/-- Fallback exponent. -/
def fallbackExponentC401G5 : ℝ := 1 - 102210/(10:ℝ)^8

lemma alphaC401G5_lt_target : alphaC401G5 < targetExponentC401G5 := by norm_num [alphaC401G5, targetExponentC401G5]
lemma alphaC401G5_lt_fallback : alphaC401G5 < fallbackExponentC401G5 := by norm_num [alphaC401G5, fallbackExponentC401G5]
lemma target_lt_fallbackC401G5 : targetExponentC401G5 < fallbackExponentC401G5 := by
  norm_num [targetExponentC401G5, fallbackExponentC401G5]
lemma target_posC401G5 : 0 < targetExponentC401G5 := by norm_num [targetExponentC401G5]
lemma target_lt_oneC401G5 : targetExponentC401G5 < 1 := by norm_num [targetExponentC401G5]
lemma fallback_lt_oneC401G5 : fallbackExponentC401G5 < 1 := by norm_num [fallbackExponentC401G5]
lemma target_lt_decimalC401G5 : targetExponentC401G5 < decimalExponent := by
  norm_num [targetExponentC401G5, decimalExponent]
lemma fallback_lt_decimalC401G5 : fallbackExponentC401G5 < decimalExponent := by
  norm_num [fallbackExponentC401G5, decimalExponent]
lemma target_lt_thetaC401G5 : targetExponentC401G5 < theta :=
  (show targetExponentC401G5 < alpha by norm_num [targetExponentC401G5, alpha]).trans Skies.alpha_theta
lemma fallback_lt_thetaC401G5 : fallbackExponentC401G5 < theta :=
  (show fallbackExponentC401G5 < alpha by norm_num [fallbackExponentC401G5, alpha]).trans Skies.alpha_theta

end SeamC401G5
end
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RAM.hillsC401G5_program
#print axioms OAI.PowerSaving.RAM.envelope_program_geC401G5
#print axioms OAI.PowerSaving.SeamC401G5.alphaC401G5_theta
#print axioms OAI.PowerSaving.hillsC401G5_real
