import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

package hakuiKoyori where

@[default_target]
lean_lib HakuiKoyori
