import Lake
open Lake DSL

-- require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require scilean from git "https://github.com/lecopivo/SciLean" @ "af67d94b6cc276ec74bfb22b684a0fcdbe4a6c9c"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.2.0"
require LSpec from git "https://github.com/lurk-lab/LSpec.git" @ "main"

package ScileanExtra where
  -- add package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]


lean_lib «ScileanExtra» where
  -- add library configuration options here

@[default_target]
lean_exe «scilean-extra» where
  root := `Main
