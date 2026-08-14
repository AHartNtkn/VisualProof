# Wire-Sever Port Partition Implementation Plan

**Goal:** Define wire severing from a selected wire and a partition of that
wire's structurally labelled ports, with both executable directions exactly
covering the rule up to open-diagram isomorphism.

**Architecture:** `Region.Port`, `Item.Port`, and `ItemSeq.Port` identify port
positions in source syntax. A `PortPartition` assigns every source port a wire
in the corresponding fiber of the join map. `partitionOutput` performs one
structural traversal and is the only constructor of separated syntax. Joining
is direct wire renaming. Open cases use source presentations to keep port
labels stable under diagram isomorphism; those presentations contain source
syntax only.

## Completed work

- [x] Define structural port labels and source-indexed port partitions.
- [x] Define computable region, item, and item-sequence partitioning.
- [x] Prove that joining every partition output recovers its source.
- [x] Prove that every separated syntax has a partition of its joined
  renaming; this is proof infrastructure, not executable index data.
- [x] State local and open wire severing using source partitions.
- [x] Replace both sever runners so they compute separated syntax.
- [x] Keep both join runners source-shaped and compute joining by renaming.
- [x] Prove forward and backward exactness up to `OpenDiagram.Isomorphic`.
- [x] Migrate semantic soundness to the port-partition relation.
- [x] Validate strict compilation, computability, authority boundaries, and
  the full build.

## Responsibility checks

- Sever indices contain a selected wire, source occurrence or presentation,
  and port labels. They contain no target region or target diagram.
- Join indices contain the separated source occurrence or presentation and
  the join map. They contain no target syntax and no evidence that the rule
  already holds.
- `runForward` and `runBackward` are computable and perform no search or
  occurrence discovery.
- Exactness theorems identify the union of indexed executions with
  `Rule.WireSever` in each direction.
- No alternate runner, compatibility constructor, or target reconstruction
  authority remains.
