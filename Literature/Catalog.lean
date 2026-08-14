/-!
# Literature coverage records

Small metadata records used by paper-specific Lean modules. Statements remain
ordinary proposition definitions and proofs remain ordinary theorem
declarations; this catalog records coverage without becoming a second logic.
-/

namespace Literature

/-- Coverage state of a source claim. -/
inductive ClaimStatus where
  | stated
  | proved
  | outOfScope
  | refuted
  deriving DecidableEq, Repr

/-- Auditable correspondence between one source claim and Lean declarations. -/
structure ClaimRecord where
  claimId : String
  sourceLocator : String
  statementName : String
  proofName : Option String := none
  status : ClaimStatus
  deriving Repr

/-- Coverage record exported by a paper-specific module. -/
structure PaperRecord where
  citationKey : String
  claims : List ClaimRecord
  deriving Repr

end Literature
