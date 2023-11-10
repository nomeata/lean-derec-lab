import Lake
open Lake DSL

package Derec where

@[default_target]
lean_lib «Derec» where
   globs := #[.andSubmodules `Derec]

