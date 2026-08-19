# T1 isolated Aristotle input boundary

This packet is the only input for the independently submitted Phase T1
TruthAssembly evaluation. It contains exactly:

1. `b2.tar`, SHA-256
   `c3c05eae85fa0357501f177cbbcebbe103a9f29c90926d9ee9b5e08ac4dd5da8`;
2. `c1.tar`, SHA-256
   `0cd2d7b56e38d99f3aa9b20af0c87b752e4985dabec22bed9d85d2e98670f56e`;
3. C2's `AssemblyCompletion.md`, `AssemblyCompletion/`, and its result hash
   `ce81979d4ea258bfd255ea354e262b61fd3a4fc612dfe034fd4af1271ed49a61`;
4. `PHASE_T1_TRUTH_ASSEMBLY_PROMPT.md`; and
5. the source submission manifest.

It deliberately excludes B3, whole-frame equality targets, IVI, topology,
receipts, transport, held-out transfer, successor work, all later formal
modules, and every unrelated Aristotle project file. Any use of material
outside this packet is `INVALID_LEAKAGE_OR_SELF_CERTIFICATION`.
