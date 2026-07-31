import VisualProof.Rule.WirePrimitive.Partition
import VisualProof.Rule.WirePrimitive.ContentWitnesses
import VisualProof.Rule.WirePrimitive.Content
import VisualProof.Rule.WirePrimitive.Arguments
import VisualProof.Rule.WirePrimitive.Leaves

/-!
The sole public facade for primitive wire transformations.

The facade exposes generic signature-indexed partition/merge, content-shape,
argument-plumbing, and formal/identity/folded-reference leaf primitives
without restoring the monolithic relation-content input model.
-/
