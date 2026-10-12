-- Entry point for the Big O Speedrun verifier (exact DFT, all lengths).
-- Saving 67/100000 = 6700000/10^10, the round-eleven saving of github.com/shea256/fourier-transform-below-nlogn
-- (results/round11.md). The helper circuit is Swapnil Jain's round-eleven complex word (Swapnil-jain/integer-mult-kappa
-- @ 1a580dc), as adopted there, converted to the certificate format gcert/1 (lean/round11/converter/word_to_gcert.py)
-- and placed in Jacob Sussman's five-stage bridged layout. The proof builds on Jacob Sussman's development
-- (github.com/jacobalansussman/wht-power-saving-lean, Apache-2.0) as extended by Chafik Boukhalfa
-- (github.com/chafreaky/wht-power-saving-lean @ fd19e46), and on OpenAI's files (github.com/openai/math @ fd4aeeb).
-- Source: github.com/shea256/fourier-transform-below-nlogn, lean/round11. See Submission/NOTICE.lean.
-- Imports are prefixed with `Submission.`.
import Submission.Work.FourierR11.Main

open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (67 : ℝ) / 100000)) := by
  obtain ⟨order, solve, W, hprogram, htime⟩ := transform_mainX
  refine ⟨order, solve, W, hprogram, ?_⟩
  have hexp : decimalExponentX = 1 - (67 : ℝ) / 100000 := by
    norm_num [decimalExponentX]
  have htime_eq : decimalTimeX =
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^ (1 - (67 : ℝ) / 100000)) := by
    funext n
    simp only [decimalTimeX, hexp]
  rw [← htime_eq]
  exact htime.2.1
