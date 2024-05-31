import Lake
open Lake DSL
require scilean from git "https://github.com/lecopivo/SciLean" @ "master"
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
