# NRRF648 quarantined intake

Run `python3 experiments/attest_nrrf648.py ARCHIVE --output source_attestation.json`
against the authenticated Aristotle tarball. The verifier checks the tarball,
source, notes, and external `lakefile.toml` bytes and records a canonical
inventory hash. It does not extract into this checkout, compile Lean, or add a
main build root.

`theorem_interface.json` is an inventory of reported identifiers, not evidence
that their types or imports are compatible with the local theory. A later A2
audit must rebuild the unmodified source in its own exact environment.
