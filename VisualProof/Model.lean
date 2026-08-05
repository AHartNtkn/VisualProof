namespace VisualProof

/-- A semantic universe for the diagram calculus.  The calculus requires only
that its carrier be inhabited; relations supply all non-structural meaning. -/
structure Model where
  Carrier : Type
  nonempty : Nonempty Carrier

end VisualProof
