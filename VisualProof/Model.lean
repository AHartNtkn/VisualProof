import VisualProof.Lambda.Quotient

namespace VisualProof

/-- A semantic universe for the diagram calculus, backed by a lawful Lambda
model and an inhabited carrier. -/
structure Model extends Lambda.LambdaModel where
  nonempty : Nonempty Carrier

end VisualProof
