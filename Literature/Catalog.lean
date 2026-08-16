/-!
# Literature coverage records

Paper-specific modules use these data structures to describe source access and
Lean correspondence. Mathematical statements are ordinary proposition
definitions, and checked arguments are ordinary theorem declarations.

The claim lifecycle is explicit: a source claim starts as `sourceOnly`, may
become an `openInLean` proposition, and may then be recorded as either
`provedInLean` or `refutedInLean`. `outOfScope` is a terminal audit decision,
not evidence that the source claim is false. A refutation records the source
statement and a separate theorem proving its negation or a precise
obstruction; it is not an unchecked disagreement in metadata.
-/

namespace Literature

/-- Mathematical role of a work in the uniform-equilibrium bibliography. -/
inductive PaperRole where
  | foundations
  | zeroSumUniformValue
  | zeroSumBoundary
  | nonzeroSumExistence
  | recentNonzeroSum
  | finiteMemoryAlgorithms
  | counterexamples
  | formalization
  | surveys
  deriving DecidableEq, Repr

/-- Strongest kind of source inspection recorded for a paper. -/
inductive SourceEvidence where
  | bibliographic
  | abstractInspected
  | secondaryInspected
  | primaryInspected
  deriving DecidableEq, Repr

/-- Completeness state of the paper-specific audit. -/
inductive PaperAuditStatus where
  | catalogued
  | sourceInspected
  | claimAuditInProgress
  | claimAuditComplete
  | correspondenceComplete
  deriving DecidableEq, Repr

/-- Lean correspondence state of one source claim.

Declaration names are constructor data, so an open correspondence has one
statement name and a checked correspondence has both statement and proof names.
The `refutedInLean` constructor is first-class: its proof name must identify a
checked theorem for the refutation or obstruction, just as `provedInLean` must
identify a checked proof of the source statement.
-/
inductive ClaimStatus where
  | sourceOnly
  | openInLean (statementName : String)
  | provedInLean (statementName proofName : String)
  | outOfScope
  | refutedInLean (statementName proofName : String)
  deriving DecidableEq, Repr

/-- Auditable correspondence between one source claim and Lean declarations. -/
structure ClaimRecord where
  claimId : String
  sourceLocator : String
  summary : String
  status : ClaimStatus
  deriving Repr

/-- Coverage record exported by a paper-specific module. -/
structure PaperRecord where
  paperId : String
  bibliographyLabel : String
  bibliographyLocator : String
  role : PaperRole
  sourceEvidence : SourceEvidence
  auditStatus : PaperAuditStatus
  claims : List ClaimRecord
  deriving Repr

end Literature
