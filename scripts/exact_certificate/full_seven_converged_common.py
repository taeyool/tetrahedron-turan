"""Shared constants and hashing conventions of the FullSevenConverged Lean chain.

Every entry point (the two generators, the bounded sweep helper and the
verifier) imports the pinned certificate, bound, namespace, template and
output locations from here.

Hash convention: the certificate is hashed as its raw bytes (its directory
preserves them with ``-text``). Lean, Python and JSON sources are hashed as
UTF-8 text with CRLF normalized to LF, so that the manifests agree on every
checkout regardless of ``core.autocrlf``; the generators always write LF.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

CHAIN = "FullSevenConverged"
NS = "FlagAlgebras.Core.Tetrahedron." + CHAIN
PREFIX = "LeanFlagAlgebras.Core.Examples." + CHAIN + "."
SRC = ROOT / "LeanFlagAlgebras/Core/Examples"
GENERATED = SRC / CHAIN
AUDIT = ROOT / f"AxiomCheck{CHAIN}.lean"
VERIFICATION = ROOT / "certificate/verification"

# The certificate-dependent proof modules are generated from templates written
# for an earlier certificate with the same block structure. The templates are
# not Lean modules of this repository; they live under scripts/.
TEMPLATES = ROOT / "scripts/exact_certificate/templates/Examples"
OLD_FAMILY_TEMPLATES = [
    "TetrahedronAntitone",
    "TetrahedronBoost",
    "TetrahedronCompact",
    "TetrahedronDegreeCheck",
    "TetrahedronDegreeExpand",
    "TetrahedronDifferential",
    "TetrahedronExtremal",
    "TetrahedronLimitHom",
    "TetrahedronLimitLin",
    "TetrahedronLimitMul",
    "TetrahedronMaximizer",
    "TetrahedronOrder7Assembly",
    "TetrahedronOrder7BlockCheck",
    "TetrahedronOrder7BlockElt",
    "TetrahedronOrder7BlockFlags",
    "TetrahedronOrder7BlockGamma",
    "TetrahedronOrder7BlockSOS",
    "TetrahedronOrder7Blocks",
    "TetrahedronOrder7Bound",
    "TetrahedronOrder7CellSem",
    "TetrahedronOrder7CellWeight",
    "TetrahedronOrder7Chain",
    "TetrahedronOrder7Check",
    "TetrahedronOrder7ClassIdx",
    "TetrahedronOrder7ClassNum",
    "TetrahedronOrder7Column",
    "TetrahedronOrder7Covered",
    "TetrahedronOrder7Deck",
    "TetrahedronOrder7Edges",
    "TetrahedronOrder7Ext24",
    "TetrahedronOrder7Ext45",
    "TetrahedronOrder7Extension",
    "TetrahedronOrder7Fiber",
    "TetrahedronOrder7FoldSum",
    "TetrahedronOrder7GatherPull",
    "TetrahedronOrder7Induce5",
    "TetrahedronOrder7Induced",
    "TetrahedronOrder7Objective",
    "TetrahedronOrder7Pieces",
    "TetrahedronOrder7Realize",
    "TetrahedronOrder7Reduce",
    "TetrahedronOrder7Reindex",
    "TetrahedronOrder7RootAcct",
    "TetrahedronOrder7RootElt",
    "TetrahedronOrder7RootExpand",
    "TetrahedronOrder7RootFlags",
    "TetrahedronOrder7RootMatch",
    "TetrahedronOrder7RootSOS",
    "TetrahedronOrder7RootScaled",
    "TetrahedronOrder7Slack",
    "TetrahedronOrder7Split",
    "TetrahedronOrder7Sweep7_00",
    "TetrahedronOrder7Sweep7_01",
    "TetrahedronOrder7Sweep7_02",
    "TetrahedronOrder7Sweep7_03",
    "TetrahedronOrder7Sweep7_04",
    "TetrahedronOrder7Sweep7_05",
    "TetrahedronOrder7Sweep7_06",
    "TetrahedronOrder7Sweep7_07",
    "TetrahedronOrder7Sweep7_08",
    "TetrahedronOrder7Sweep7_09",
    "TetrahedronOrder7Sweep7_10",
    "TetrahedronOrder7Sweep7_11",
    "TetrahedronOrder7Sweep7_12",
    "TetrahedronOrder7Sweep7_13",
    "TetrahedronOrder7Sweep7_14",
    "TetrahedronOrder7Sweep7_15",
    "TetrahedronOrder7Sweep7_16",
    "TetrahedronOrder7Sweep7_17",
    "TetrahedronOrder7Sweep7_18",
    "TetrahedronOrder7Sweep7_19",
    "TetrahedronOrder7Sweep7_20",
    "TetrahedronOrder7Sweep7_21",
    "TetrahedronOrder7Sweep7_22",
    "TetrahedronOrder7Sweep7_23",
    "TetrahedronOrder7Sweep7_24",
    "TetrahedronOrder7Sweep7_25",
    "TetrahedronOrder7Sweep7_26",
    "TetrahedronOrder7Sweep7_27",
    "TetrahedronOrder7Sweep7_28",
    "TetrahedronOrder7Sweep7_29",
    "TetrahedronOrder7Sweep7_30",
    "TetrahedronOrder7Sweep7_31",
    "TetrahedronOrder7Sweep7_32",
    "TetrahedronOrder7Sweep7_33",
    "TetrahedronOrder7Sweep7_34",
    "TetrahedronOrder7Sweep7_35",
    "TetrahedronOrder7Sweep7_36",
    "TetrahedronOrder7Sweep7_37",
    "TetrahedronOrder7Sweep7_38",
    "TetrahedronOrder7Sweep7_39",
    "TetrahedronOrder7Sweep7_40",
    "TetrahedronOrder7Sweep7_41",
    "TetrahedronOrder7Sweep7_42",
    "TetrahedronOrder7Sweep7_43",
    "TetrahedronOrder7Sweep7_44",
    "TetrahedronOrder7Sweep7_45",
    "TetrahedronOrder7Sweep7_46",
    "TetrahedronOrder7Sweep7_47",
    "TetrahedronOrder7Sweep7_48",
    "TetrahedronOrder7Verified",
    "TetrahedronRealize",
    "TetrahedronRealizedApply",
    "TetrahedronStatComb",
    "TetrahedronTuran",
]

# The handwritten five-root semantic modules of the chain (not generated).
FIVE_ROOT_MODULES = [
    "TetrahedronOrder7FiveRootBits",
    "TetrahedronOrder7FiveRootColumn",
    "TetrahedronOrder7FiveRootColumnSum",
    "TetrahedronOrder7FiveRootExpand",
    "TetrahedronOrder7FiveRootFlags",
    "TetrahedronOrder7FiveRootGramSem",
    "TetrahedronOrder7FiveRootOrderedColumn",
    "TetrahedronOrder7FiveRootOrderedSem",
    "TetrahedronOrder7FiveRootPullback",
    "TetrahedronOrder7FiveRootSOS",
    "TetrahedronOrder7FiveRootSamples",
    "TetrahedronOrder7FiveRootSem",
    "TetrahedronOrder7FiveRootTableFacts",
]

# The sole formalization input, pinned by the raw-byte hash of the file.
CERT = ROOT / "certificate/K4_turan_order7_certificate.json"
CERT_SHA = "36f31cb3e30fa353c83a4a23b20cfed5846594d9983cd4f881ec7cf4cdc18625"
BOUND = "14993367693127837/26880000000000000"
BOUND_FRACTION = Fraction(BOUND)
SCALE = 8_000_000
COLUMN_DENOMINATOR = 5040 * SCALE ** 2
COLUMN_NUMERATOR = 179920412317534044
TAU_NUMERATOR = 710104654129914
EXAMPLE_MASK = 1629596093
TOTAL_FACTORS = 780
TOTAL_ENTRIES = 326557
OLD_FAMILY_COUNTS = [0, 0, 0, 0, 0, 0, 1, 2, 0, 7, 236, 185]
OLD_FAMILY_DIMS = [2, 2, 11, 8, 7, 64, 56, 50, 45, 7, 236, 191]
ACTIVE_TYPES = [0, 1, 3, 7, 11, 15, 30, 31, 63, 77, 87, 94, 116, 117, 119, 222, 237, 254]
ACTIVE_ROWS = [21, 30, 35, 12, 23, 23, 34, 37, 2, 1, 6, 28, 14, 17, 31, 10, 17, 8]
FIVE_ROOT_ROWS = sum(ACTIVE_ROWS)

HEADLINE_TARGETS = [PREFIX + name for name in ("TetrahedronDifferential", "TetrahedronBoost")]
SWEEP_COUNT = 49
SWEEP_TARGETS = [PREFIX + f"TetrahedronOrder7Sweep7_{i:02d}" for i in range(SWEEP_COUNT)]

# The literal fraction that the final theorems must state.
LEAN_BOUND = f"{BOUND_FRACTION.numerator} / {BOUND_FRACTION.denominator}"

assert Fraction(COLUMN_NUMERATOR, COLUMN_DENOMINATOR) == BOUND_FRACTION
assert FIVE_ROOT_ROWS == 349 and sum(OLD_FAMILY_COUNTS) + FIVE_ROOT_ROWS == TOTAL_FACTORS
assert len(OLD_FAMILY_TEMPLATES) == 105 and len(FIVE_ROOT_MODULES) == 13


def raw_sha(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def normalize(data: bytes) -> bytes:
    return data.replace(b"\r\n", b"\n")


def sha_text(text: str) -> str:
    return hashlib.sha256(normalize(text.encode("utf-8"))).hexdigest()


def text_sha(path: Path) -> str:
    """SHA-256 of a text source with CRLF normalized to LF."""
    return hashlib.sha256(normalize(Path(path).read_bytes())).hexdigest()


def read_text(path: Path) -> str:
    return normalize(Path(path).read_bytes()).decode("utf-8")


def write_lf(path: Path, text: str) -> None:
    """Write LF-terminated UTF-8, leaving an identical file untouched."""
    data = normalize(text.encode("utf-8"))
    path = Path(path)
    if not path.exists() or path.read_bytes() != data:
        path.write_bytes(data)


def certificate_bytes() -> bytes:
    raw = CERT.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != CERT_SHA:
        raise SystemExit(f"The pinned certificate {CERT} has SHA-256 {actual}, expected {CERT_SHA}")
    return raw
