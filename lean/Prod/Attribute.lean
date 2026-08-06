import Lean

/-!
# `@[prod]` tag attribute

Marks a definition for prod extraction: `prod-export` lowers every tagged
definition through Lean's own LCNF pipeline into the sexp IR consumed by the
Rust `prod-ir` parser.
-/

namespace Prod

/-- Marks a definition for prod extraction (LCNF → sexp IR). -/
initialize prodAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `prod "marks a definition for prod extraction"

end Prod
