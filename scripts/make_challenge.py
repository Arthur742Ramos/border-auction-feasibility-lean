"""Generate a self-contained, fully proved Mathlib-only comparison module.

No proof holes are introduced. The comparison module duplicates the proof
with a distinct helper namespace; it is not an independent second proof.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ORDER = ("Auction", "WeightedHall", "Flow", "Theorem", "Support", "Independent")
def render():
    imports = []
    bodies = []
    for name in ORDER:
        lines = (ROOT / "Border" / f"{name}.lean").read_text().splitlines()
        retained = []
        for line in lines:
            if line == "module":
                continue
            if line.startswith("public import "):
                if "Mathlib." in line and line not in imports:
                    imports.append(line)
                continue
            retained.append(line)
        body = "\n".join(retained).strip()
        body = body.replace("Border.Implementation", "Border.ChallengeProof")
        body = body.replace("Implementation.", "ChallengeProof.")
        bodies.append(f"/- Source: Border/{name}.lean; helpers renamed for comparison. -/\nsection\n{body}\nend")
    header = """/-!
    Self-contained comparison surface for Border's finite auction feasibility theorem.
    All definitions and all six selected theorems are fully proved in this module.
    Only pinned Mathlib is imported. The helper proofs below mirror the library,
    under a different namespace; they do not constitute independent proof discovery.
    -/
    """
    header = header.replace("\n    ", "\n")
    return "module\n" + "\n".join(imports) + "\n\n" + header + "\n\n".join(bodies) + "\n"

if __name__ == "__main__":
    (ROOT / "Challenge.lean").write_text(render())
