import Lake
open Lake DSL

package «mA4N1_2023» where
  -- add any package configuration options here
  moreServerArgs := #[ "-DautoImplicit=false" ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MA4N1_2023» {
  -- add any library configuration options here
  roots := #[`MA4N1_2023]
}
