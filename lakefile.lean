import Lake
open Lake DSL

package «navier-stokes-bkm» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib NavierStokesBKM where
  roots := #[`NavierStokesBKM]
