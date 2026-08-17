"""Quarantined byte attestation for an authenticated NRRF648 archive.

This verifier checks bytes and records archive provenance.  It never invokes
Lean, changes lakefile.toml, or derives a bridge to the local theory.
"""

import argparse
import hashlib
import json
import tarfile
from pathlib import PurePosixPath


EXPECTED = {
    "result_tar_sha256": "4f5b4d28422db7148d457c440f4bb65acc71845768c57bd708336884e2356819",
    "NRRF648ClosureNoExternalAuthorityConceptualFormTranslation.lean": "e4643d86577859bf2659a417d42683e65f52e6605fdb899b0021d8cbae6e0321",
    "CLOSURE_NO_EXTERNAL_AUTHORITY_NRRF648_NOTES.md": "9c59580f80c55e5b767ef2edf45ff0756bce0938c19639226e54a7de8d3e1930",
    "lakefile.toml": "22f6cb43d7ab96cc38be28e1fda9ab3d9638cddfa6e82075a7347c35e0e554ca",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    archive = open(args.archive, "rb").read()
    files = {}
    with tarfile.open(args.archive) as tar:
        for member in tar.getmembers():
            path = PurePosixPath(member.name)
            if member.isfile() and not path.is_absolute() and ".." not in path.parts:
                content = tar.extractfile(member).read()
                files[member.name] = {"sha256": sha256_bytes(content), "bytes": len(content)}
    selected = {}
    for suffix in EXPECTED:
        if suffix == "result_tar_sha256":
            continue
        matches = [entry for name, entry in files.items() if name.endswith("/" + suffix)]
        if len(matches) != 1:
            raise SystemExit(f"expected exactly one {suffix}, found {len(matches)}")
        selected[suffix] = matches[0]
    canonical_inventory = "\n".join(
        f"{name}\t{entry['sha256']}\t{entry['bytes']}" for name, entry in sorted(files.items())
    ).encode()
    result = {
        "stage": "external_source_environment_attestation",
        "status": "source_bytes_verified_not_built",
        "input_manifest_commit": "490a588",
        "artifact_checks": {
            "result_tar_sha256": sha256_bytes(archive),
            "result_tar_sha256_match": sha256_bytes(archive) == EXPECTED["result_tar_sha256"],
            "selected_files": selected,
            "selected_hashes_match": all(selected[name]["sha256"] == EXPECTED[name] for name in selected),
            "regular_file_count": len(files),
            "inventory_sha256": sha256_bytes(canonical_inventory),
        },
        "artifact_custody": {
            "retrieval_kind": "authenticated_aristotle_download",
            "archive_committed": False,
            "redistribution_status": "not_assumed",
        },
        "proof_environment": {
            "external_lakefile_sha256": selected["lakefile.toml"]["sha256"],
            "external_mathlib_revision": "v4.28.0",
            "complete_import_closure": "OPEN",
        },
        "local_formal_checks": {"lake_build": "NOT_RUN", "sorry_audit": "NOT_RUN", "axiom_audit": "NOT_RUN"},
        "non_implications": ["not_a_main_lake_build_root", "not_a_local_machine_checked_result", "not_a_phase_c2_input", "not_a_whole_frame_geom_equiv", "not_an_identification_of_topological_closure_with_translational_completion"],
    }
    if not result["artifact_checks"]["result_tar_sha256_match"] or not result["artifact_checks"]["selected_hashes_match"]:
        raise SystemExit("hash mismatch")
    with open(args.output, "w") as output:
        json.dump(result, output, indent=2, sort_keys=True)
        output.write("\n")


if __name__ == "__main__":
    main()
