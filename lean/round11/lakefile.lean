import Lake
open System Lake DSL

-- Lake project for the Walsh-Hadamard power-saving theorems of this repository.
-- Package name, toolchain (lean-toolchain), package option and Mathlib revision are those of the
-- lakefile of github.com/openai/math (lean/lakefile.lean at commit fd4aeeb); every other
-- dependency of that lakefile is dropped because the files used here import only Mathlib.
package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

-- Files of github.com/openai/math (lean/OAI/Computability/, family 130), unmodified;
-- only the 89 files that the theorems of this repository depend on.
lean_lib OAI.Computability where
  roots := #[`OAI.Computability]
  globs := #[`OAI.Computability.+]

-- The Walsh-Hadamard wrapper (`wht`, `WHTProgram`) on top of the OpenAI development; not from openai/math.
lean_lib WHTCheck where globs := #[`WHTCheck.+]

-- The development of this repository, with the comparator challenge and solution modules
-- (`Work.CarrierCheck.ChallengeB2Ke16x` etc.); not from openai/math.
lean_lib Work where globs := #[`Work.+]
