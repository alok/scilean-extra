import Lake
open Lake DSL
require scilean from git "https://github.com/lecopivo/SciLean" @ "master"

package «scilean-extra» where
  -- add package configuration options here

lean_lib «ScileanExtra» where
  -- add library configuration options here

@[default_target]
lean_exe «scilean-extra» where
  root := `Main
