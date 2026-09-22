import Lake
open Lake DSL

package «jsp-000404» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5ed2965256430c3649e86755f9576b54eca72435"

lean_lib JSP404 where
  srcDir := "ThirdParty/Sendov"
  leanOptions := #[⟨`autoImplicit, true⟩]

@[default_target]
lean_lib «Jsp000404» where
