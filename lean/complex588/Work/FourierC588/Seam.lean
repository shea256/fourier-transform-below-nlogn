import Work.GCert.Data.C588Glue401
import Work.GCert.Data.InstC588
import Work.Bridge401.End

/-!
# THE SEAM for the Fourier transfer: our kernel program in OpenAI's `hills_program` form

New file, not a copy of an OpenAI file: Jacob Sussman's Work/FourierE8/Seam.lean (Apache-2.0) for the
entrance-gauged nine-stage layout of PR #401 (Dugongue, CrocSwap/integer-mult-bounds; on jacklightChen's PR #377 layout;
Lean: gauged halves DFT Bridge3, network DFT New Sums, end theorem Work/Bridge401/End.lean), certificate `GXD.C588`,
suffix `C588`; written by tools/mkseam401.py (DFT Lean). Sections 2 and 3 of Jacob's file are replaced by one theorem
that calls `GX.engine_of_ginv_401`.  It contains lines 95-99 of
lean/OAI/Computability/FourierTransform/TensorProgram.lean (the statement of `hills_program`) and line 114 of
lean/OAI/Computability/FourierTransform/TensorSaving.lean (the definition of `hills`) of github.com/openai/math
(commit fd4aeeb, Apache-2.0), with `hills`, `alpha` replaced by `hillsC588`, `alphaC588`.

Twin of Work/Fourier/Seam.lean for the certificate `GXD.C588` (label width 9; Work/GCert/Data/C588.lean) in the
place of `GXD.P193`: the same text with the names and numbers of that certificate, and with every declared name
changed (`C588` in the place of `Z`, `C588` appended to the other names, namespace `SeamC588` for `Seam`), so that the
two files have no declaration in common.  This file imports the C588 instance only, not the published seam; that
is why the general lemmas of sections 1 and 2 are stated here again, under new names, with the same proofs.

OpenAI's Fourier proof uses the tensor network through ONE theorem, `RAM.hills_program`
(OAI/Computability/FourierTransform/TensorProgram.lean:95), with ONE call site (`Bench.gleamT`,
SectorAlgorithm.lean:45), plus four envelope facts (`hills_pos`, `hills_mono`, `hills_le`, `hills_real`,
TensorSaving.lean:116-133) and the number facts `alpha_pos`, `alpha_lt`, `Skies.alpha_theta`,
`Skies.decimal_range`.  This file gives all of them at OUR exponent

  `alphaC588 = 1 - 12331686/10^10`      (OpenAI: `alpha = 1 - 2/10^11`),

under OpenAI's names with `C588` after `hills` / `alpha`, in OpenAI's own namespaces.

* `GX.engine_of_ginvC588`, `GX.engine_of_halvesC588`   twins of `GX.wht_of_ginv`, `GX.wht_of_halves`
  (Work/GCert/Chain/End.lean) ending in the kernel program (`RAM.engine_program_ggroup_list`) instead of the
  Walsh-Hadamard corollary: every colour `cl`, both modes `m`, every batch of inputs.
* `SeamC588.engine_C588x_of_scal`, `_of_ids`   twins of `WHT.wht_C588x_of_scal`, `_of_ids`
  (Work/GCert/Data/C588.lean): same certificate `GXD.C588`, same unit list, same rate fact
  `BlockAccounting.fold_C588x`, fill parameter `s = 40`.
* `RAM.hillsC588_program`   THE SEAM, closed with the kernel-checked scalar half `GXD.C588.scalOK`.
* `RAM.envelope_program_geC588`   the same at every exponent `z ≥ alphaC588`.

No `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
noncomputable section

/-! ## 1. The exponent and the envelope facts -/

/-- Our exponent, in the place of OpenAI's `alpha` (TensorSaving.lean:81). -/
def alphaC588 : ℝ := 1 - 12331686/(10:ℝ)^10

theorem alphaC588_pos : 0 < alphaC588 := by norm_num [alphaC588]
theorem alphaC588_lt : alphaC588 < 1 := by norm_num [alphaC588]

lemma envelope_monoC588 (z : ℝ) (hz : 0 ≤ z) {a b : ℕ} (h : a ≤ b) : envelope z a ≤ envelope z b := by
  unfold envelope
  gcongr

-- `envelope_le` (for `z ≤ 1`) and `envelope_real` (for `0 ≤ z`) already exist: Work/Block/WHT.lean:26, :31.

lemma envelope_mono_expC588 {z z' : ℝ} (h : z ≤ z') (k : ℕ) : envelope z k ≤ envelope z' k := by
  unfold envelope
  exact Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le (by simp) h)

/-- Natural envelope at our exponent, in the place of OpenAI's `hills` (TensorSaving.lean:114). -/
def hillsC588 (k : ℕ) := Nat.ceil (((k:ℝ)+1)^alphaC588)

lemma hillsC588_eq_envelope : hillsC588 = envelope alphaC588 := rfl

lemma hillsC588_pos (k : ℕ) : 1≤hillsC588 k := envelope_pos alphaC588 k

lemma hillsC588_mono {a b : ℕ} (h : a≤b) : hillsC588 a ≤ hillsC588 b := envelope_monoC588 alphaC588 alphaC588_pos.le h

lemma hillsC588_le (k : ℕ) : hillsC588 k ≤ k+1 := envelope_le alphaC588 alphaC588_lt.le k

lemma hillsC588_real (k : ℕ) : (hillsC588 k:ℝ) ≤ 2*((k:ℝ)+1)^alphaC588 := envelope_real alphaC588 alphaC588_pos.le k

/-! ## 3. The certificate `GXD.C588` with entrance gauges (PR #401 layout) -/

namespace SeamC588
open Binary Matrix Finset RAM RAM.Ty
universe U

/-- **Kernel program at `1 - 12331686/10^10`** for the certificate `GXD.C588`: `GX.engine_of_ginv_401` with its gauged
invocation package `GXD.C588.ginv` (`GXD.ginvOf` of its kernel checks), its bank schedule `GXD.C588.sched` (`Work/GCert/Data/C588Glue401.lean`), the
unit list `BlockAccounting.blocksC588x` and the rate fact `BlockAccounting.fold_C588x` (fill parameter `s = 40`). -/
theorem engine_C588x (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 12331686/(10:ℝ)^10) (k i)) :=
  GX.engine_of_ginv_401 GXD.C588.ginv GXD.C588.h9 GXD.C588.sched GXD.C588.fitsS
    73 12208 rfl GXD.C588.width (by norm_num) BlockAccounting.blocksC588x
    (fun φ => by rw [GXD.C588.price φ]; exact BridgeRate.C588.unit_cost_x φ)
    40 (1 - 12331686/(10:ℝ)^10) (by norm_num) (by norm_num) BlockAccounting.fold_C588x cl m k v

end SeamC588

/-! ## 4. THE SEAM -/

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- **THE SEAM.**  OpenAI's `hills_program` (TensorProgram.lean:95) word for word, with `hillsC588`
(exponent `1 - 12331686/10^10`) in the place of `hills` (exponent `1 - 2/10^11`): the kernel program of
the certificate `GXD.C588` (the one behind `WHT.wht_main_block_C588x`), for every colour,
both modes and every batch of inputs, in `2^k * hillsC588 k` operations. -/
theorem hillsC588_program (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hillsC588 (k i)) :=
  SeamC588.engine_C588x cl m k v

/-- **General exponent**: the same at every exponent `z ≥ alphaC588`, envelope `⌈(k+1)^z⌉`. -/
theorem envelope_program_geC588 (z : ℝ) (hz : alphaC588 ≤ z) (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  (hillsC588_program cl m k v).mono fun i => Nat.mul_le_mul_left _ (envelope_mono_expC588 hz (k i))

end RAM

/-! ## 5. Number facts for the copy of `Main.lean` -/

namespace SeamC588

lemma alphaC588_lt_alpha : alphaC588 < alpha := by norm_num [alphaC588, alpha]

/-- for `Skies.alpha_theta` (Main.lean:39): below the paper's exponent. -/
lemma alphaC588_theta : alphaC588 < theta := alphaC588_lt_alpha.trans Skies.alpha_theta

/-- for `Skies.decimal_range` (Main.lean:59). -/
lemma alphaC588_decimal : alphaC588 < decimalExponent ∧ decimalExponent < 1 := by
  norm_num [decimalExponent, alphaC588]

/-- Target exponent of the final Fourier statement: strictly above `alphaC588`, so that the
`(log log n)^2` factor of the reduction is absorbed. -/
def targetExponentC588 : ℝ := 1 - 12331685/(10:ℝ)^10
/-- Fallback exponent. -/
def fallbackExponentC588 : ℝ := 1 - 102210/(10:ℝ)^8

lemma alphaC588_lt_target : alphaC588 < targetExponentC588 := by norm_num [alphaC588, targetExponentC588]
lemma alphaC588_lt_fallback : alphaC588 < fallbackExponentC588 := by norm_num [alphaC588, fallbackExponentC588]
lemma target_lt_fallbackC588 : targetExponentC588 < fallbackExponentC588 := by
  norm_num [targetExponentC588, fallbackExponentC588]
lemma target_posC588 : 0 < targetExponentC588 := by norm_num [targetExponentC588]
lemma target_lt_oneC588 : targetExponentC588 < 1 := by norm_num [targetExponentC588]
lemma fallback_lt_oneC588 : fallbackExponentC588 < 1 := by norm_num [fallbackExponentC588]
lemma target_lt_decimalC588 : targetExponentC588 < decimalExponent := by
  norm_num [targetExponentC588, decimalExponent]
lemma fallback_lt_decimalC588 : fallbackExponentC588 < decimalExponent := by
  norm_num [fallbackExponentC588, decimalExponent]
lemma target_lt_thetaC588 : targetExponentC588 < theta :=
  (show targetExponentC588 < alpha by norm_num [targetExponentC588, alpha]).trans Skies.alpha_theta
lemma fallback_lt_thetaC588 : fallbackExponentC588 < theta :=
  (show fallbackExponentC588 < alpha by norm_num [fallbackExponentC588, alpha]).trans Skies.alpha_theta

end SeamC588
end
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RAM.hillsC588_program
#print axioms OAI.PowerSaving.RAM.envelope_program_geC588
#print axioms OAI.PowerSaving.SeamC588.alphaC588_theta
#print axioms OAI.PowerSaving.hillsC588_real
