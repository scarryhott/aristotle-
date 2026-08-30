"""Loader for the exact NRRF833 source fragments committed alongside this file.

The fragments are split only to keep GitHub connector writes bounded.  They
concatenate byte-for-byte to the tested source; no generated logic is omitted.
"""
from pathlib import Path as _Path

_root = _Path(__file__).with_name("_nrrf833_source")
_parts = sorted(_root.glob("*.part"))
if not _parts:
    raise RuntimeError("NRRF833 source fragments are missing")
_source = "".join(part.read_text(encoding="utf-8") for part in _parts)
exec(compile(_source, __file__, "exec"), globals(), globals())
