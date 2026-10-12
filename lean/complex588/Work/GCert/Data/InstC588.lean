import Work.Bridge377.Bank
import Work.FoldRate.Group
import Work.GCert.Data.RateC588x
namespace OAI.PowerSaving.BridgeRate.C588
open Finset Binary Matrix RAM CB FoldRate
noncomputable section
def invPrice (φ : ℕ → ℝ) : ℝ := 2596 * φ 1 + 492 * φ 2 + 280 * φ 3 + 232 * φ 4 + 56 * φ 5 + 56 * φ 6 + 120 * φ 8
def padPrice (φ : ℕ → ℝ) : ℝ := 2448 * bcost φ 1 + 72 * bcost φ 8
def unitPrice (φ : ℕ → ℝ) : ℝ := 72 * invPrice φ + ((112:ℕ):ℝ) * GX.bankPrice377 φ + padPrice φ
theorem unit_cost_x (φ : ℕ → ℝ) : unitPrice φ = listCost φ BlockAccounting.blocksC588x := by
  unfold unitPrice invPrice padPrice
  simp only [GX.bankPrice377, listCost, BlockAccounting.blocksC588x, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [bcost]
  try ring
theorem unit_tally : unitPrice (fun r => (r:ℝ)) = ((12208:ℕ):ℝ) * 73 - 2560 := by
  rw [unit_cost_x]
  exact BlockAccounting.blocksC588x_tally
end
end OAI.PowerSaving.BridgeRate.C588
#print axioms OAI.PowerSaving.BridgeRate.C588.unit_cost_x
