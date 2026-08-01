import VisualProof.Rule.WirePrimitive.Partition
import VisualProof.Rule.WirePrimitive.ContentWitnesses
import VisualProof.Rule.WirePrimitive.Content
import VisualProof.Rule.WirePrimitive.Arguments
import VisualProof.Rule.WirePrimitive.ArgumentsDropTransport
import VisualProof.Rule.WirePrimitive.ArgumentsExtendTransport
import VisualProof.Rule.WirePrimitive.ArgumentsArityTransport
import VisualProof.Rule.WirePrimitive.Leaves
import VisualProof.Rule.WirePrimitive.Program

/-!
The sole public facade for primitive wire transformations.

The facade exposes generic signature-indexed partition/merge, content-shape,
argument-plumbing, formal/identity/folded-reference leaf primitives, and
checked primitive programs.  Monolithic relation-content inputs remain
confined to the compiler specification/redundancy layer.
-/
