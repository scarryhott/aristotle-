"""Verify the quarantined Aristotle archive that carries NRRF649 and NRRF650.

This script checks bytes only. It does not invoke Lean, alter a Lake root, or
bridge either external module to the native translation experiment.
"""

import argparse
import hashlib
import tarfile
from pathlib import PurePosixPath


EXPECTED = {
    "result_tar_sha256": "4083e862ce710a885738315be8894a44cecf8fcf689bdab193ea6c46bc8b0d1a",
    "NRRF649BallHairBigBangReanalysisThreeClosureLevels.lean": "3f69fa24d68e594b482d247492a4a49522530a398100878eefe9f794318ba65b",
    "BALL_HAIR_BIGBANG_REANALYSIS_NRRF649_NOTES.md": "8fc349225a10d4f07836f68c08aff0102565fdb4464009775223724881a19228",
    "NRRF650ReunifiedOriginlessTranslationPerspectivalReadings.lean": "e6f2b310dc2000a1be133a56b7697b5f4e0770129a4ad12afe3cad02f15d8a0d",
    "REUNIFIED_ORIGINLESS_TRANSLATION_NRRF650_NOTES.md": "bbd3258300888caf9a17f27548b5def68d58f4840b7f51911618ba8cf47a041e",
    "lakefile.toml": "86a4f6a6f001fbc5933a71717ed1064722f8eb0abac54be801bf0cf4839a9e0d",
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive")
    args = parser.parse_args()
    archive = open(args.archive, "rb").read()
    if digest(archive) != EXPECTED["result_tar_sha256"]:
        raise SystemExit("archive hash mismatch")
    found = {}
    with tarfile.open(args.archive) as tar:
        for member in tar.getmembers():
            path = PurePosixPath(member.name)
            if member.isfile() and not path.is_absolute() and ".." not in path.parts:
                found[member.name] = digest(tar.extractfile(member).read())
    for name, expected in EXPECTED.items():
        if name == "result_tar_sha256":
            continue
        matches = [actual for path, actual in found.items() if path.endswith("/" + name) or path == name]
        if matches != [expected]:
            raise SystemExit(f"selected file mismatch: {name}")
    print("NRRF649/650 source bytes verified; no Lean build or bridge was run.")


if __name__ == "__main__":
    main()
