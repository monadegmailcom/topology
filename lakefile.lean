import Lake
open Lake DSL

package topology {
  -- add package configuration options here
}

require mathlib from
    "/Users/monade/git/mathlib" with NameMap.empty

lean_lib Topology {
  -- add library configuration options here
}

--@[defaultTarget]
lean_exe topology {
  root := `Main
}
