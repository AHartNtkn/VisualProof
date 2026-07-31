import VisualProof.Rule.WirePrimitive.Partition
import VisualProof.Rule.WirePrimitive.ContentWitnesses
import VisualProof.Rule.WirePrimitive.Content
import VisualProof.Rule.WirePrimitive.Arguments

/-!
The sole public facade for primitive wire transformations.

The facade exposes generic signature-indexed partition/merge, content-shape
primitives, and argument-plumbing primitives without restoring the
monolithic relation-content input model.
-/
