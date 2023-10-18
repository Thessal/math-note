import Lake
open Lake DSL

package «lecture_note» {
  -- add package configuration options here
}

lean_lib «LectureNote» {
  -- add library configuration options here
}

@[default_target]
-- lean_exe «lecture_note» {
lean_lib «lecture_note» {
--  root := `Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.1.0"