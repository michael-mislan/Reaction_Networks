# SPDX-License-Identifier: Apache-2.0
"""Check public catalogue coverage, artifact paths, tags and Markdown links.

Standard library only. Run from any directory inside this checkout:
    python -B scripts/check_catalogue.py --baseline <commit-or-ref>
An optional baseline compares the original README's complete paper table.
This validates discovery metadata; it does not compile proofs or verify claims.
"""
import argparse
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
ROW = re.compile(r"^\| (P\d{3}) \| \[(.*?)\]\((.*?)\) \| \[Proofs and notes\]\((.*?)\) \|$", re.M)
THEORY = ["Structure", "Algorithms", "Kinetics", "Thermodynamics", "Production", "Inheritance", "Memory", "Persistence", "Evolution", "Emergence"]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT).decode("utf-8").replace("\r\n", "\n")


def anchor_ids(text):
    found = set(re.findall(r'<a\s+id="([^"]+)"', text))
    seen = {}
    for heading in re.findall(r"^#{1,6} (.+?)\s*#*\s*$", text, re.M):
        heading = re.sub(r"\[([^]]+)\]\([^)]+\)", r"\1", heading)
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        number = seen.get(slug, 0)
        seen[slug] = number + 1
        found.add(slug if number == 0 else f"{slug}-{number}")
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", help="Compare all stable IDs, titles, PDFs and notes against this ref's README")
    args = parser.parse_args()
    errors = []
    data = json.loads((ROOT / "catalogue.json").read_text(encoding="utf-8"))
    table = (ROOT / "CATALOGUE.md").read_text(encoding="utf-8")
    rows = ROW.findall(table)
    papers = data["papers"]
    ids = [p["id"] for p in papers]
    expected = json.loads((ROOT / "Formal/migration/expected-papers.json").read_text(encoding="utf-8"))["expected_ids"]
    if len(ids) != len(set(ids)) or set(ids) != set(expected):
        errors.append("Machine catalogue IDs must equal the existing public inventory with no duplicates")
    records = [(p["id"], p["title"], p["artifacts"]["pdf"], p["artifacts"]["notes"]) for p in papers]
    if records != rows:
        errors.append("Human and machine catalogue records differ")
    baseline_count = None
    if args.baseline:
        original = git("show", f"{args.baseline}:README.md")
        if "## All papers\n" in original:
            original = original.split("## All papers\n", 1)[1].split("## Proofs and supporting material", 1)[0]
        elif "CATALOGUE.md" in original:
            original = git("show", f"{args.baseline}:CATALOGUE.md")
        baseline_rows = ROW.findall(original)
        baseline_count = len(baseline_rows)
        if baseline_rows != rows:
            errors.append("Stable IDs, titles or artifact URLs changed from the baseline")
    if data["theory_categories"] != THEORY or data["mathematical_strands"] != ["D-Stability"]:
        errors.append("Expected the ten canonical theory categories and the D-stability strand")

    tracked = set(git("ls-files", "-z").split("\0")) - {""}
    # Allow validated new catalogue files before they are staged. Existing sparse
    # artifact paths come from Git, so PDFs/proofs need not be materialized.
    new = {p.relative_to(ROOT).as_posix() for p in ROOT.glob("*.md")}
    new |= {"catalogue.json"}
    new |= {p.relative_to(ROOT).as_posix() for folder in ("Examples", "scripts", "Applications/Origin-of-Life") for p in (ROOT / folder).rglob("*") if p.is_file() and "__pycache__" not in p.parts}
    known = tracked | new

    def exists(path):
        return path in known or any(p.startswith(path.rstrip("/") + "/") for p in known)

    topics = (ROOT / "TAGS.md").read_text(encoding="utf-8")
    topic_members = {}
    for heading, body in re.findall(r"^## (.*?)\n(.*?)(?=^## |\Z)", topics, re.M | re.S):
        topic_members[heading] = set(re.findall(r"^\| (P\d{3}) \|", body, re.M))
    for name, members in topic_members.items():
        if not members <= set(ids):
            errors.append(f"Uncatalogued paper in topic {name}")
        key = "theory_tags" if name in THEORY + ["D-Stability"] else "application_tags"
        if members != {p["id"] for p in papers if name in p[key]}:
            errors.append(f"Topic membership differs from JSON: {name}")
    for paper in papers:
        for key, allowed in (("theory_tags", THEORY + ["D-Stability"]), ("application_tags", data["application_domains"])):
            tags = paper[key]
            if len(tags) != len(set(tags)) or not set(tags) <= set(allowed):
                errors.append(f"Invalid or duplicate tags: {paper['id']} {key}")
        if not paper["theory_tags"] and not paper["application_tags"]:
            errors.append(f"Paper lacks discovery tags: {paper['id']}")
        paths = list(paper["artifacts"].values()) + [paper["evidence"]["claim_map"], paper["evidence"]["scope_notes"]] + paper["example_code"]
        for path in paths:
            if path.startswith(("/", "http:", "https:")) or ".." in PurePosixPath(path).parts or not exists(path):
                errors.append(f"Missing or invalid artifact: {paper['id']} {path}")
    public_pdfs = {p for p in tracked if p.startswith(("Theory/", "Applications/")) and p.endswith(".pdf") and re.match(r"P\d{3}-", PurePosixPath(p).name)}
    if public_pdfs != {p["artifacts"]["pdf"] for p in papers}:
        errors.append("Public subject-tree paper PDFs and catalogue coverage differ")

    markdown = [ROOT / name for name in ("README.md", "CATALOGUE.md", "LITERATURE.md", "TAGS.md", "Examples/README.md")]
    markdown += list((ROOT / "Theory").rglob("README.md")) + list((ROOT / "Applications").rglob("README.md"))
    links_checked = 0
    external = set()
    for source in markdown:
        text = source.read_text(encoding="utf-8")
        # Targets are independent of brackets in scientific titles (e.g. W[P]).
        for target in re.findall(r"\]\(([^)\n]+)\)", text):
            url = urlsplit(target)
            if url.scheme in ("http", "https"):
                external.add(target)
                continue
            if url.scheme:
                continue
            relative = unquote(url.path)
            destination = (source.parent / relative).resolve()
            try:
                path = destination.relative_to(ROOT).as_posix()
            except ValueError:
                errors.append(f"Link leaves repository: {source.relative_to(ROOT)} -> {target}")
                continue
            links_checked += 1
            if not exists(path):
                errors.append(f"Broken link: {source.relative_to(ROOT)} -> {target}")
            elif url.fragment and destination.suffix == ".md" and destination.exists():
                if unquote(url.fragment) not in anchor_ids(destination.read_text(encoding="utf-8")):
                    errors.append(f"Broken anchor: {source.relative_to(ROOT)} -> {target}")

    report = {"papers": len(ids), "baseline_papers": baseline_count, "theory_categories": len(THEORY), "mathematical_strands": len(data["mathematical_strands"]), "application_domains": len(data["application_domains"]), "relative_links_checked": links_checked, "external_urls": sorted(external), "errors": errors}
    print(json.dumps(report, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
