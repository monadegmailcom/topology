import Lake
open Lake DSL

package topology {
  -- add package configuration options here
}

--require mathlib from
--    "/Users/monade/git/mathlib" with NameMap.empty

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

@[default_target]
lean_lib topology {
  -- add library configuration options here
  globs := #[Glob.submodules "Topology"]
}

--@[defaultTarget]
--lean_exe nothing {
--  root := `Main
  --root := topology
--}
