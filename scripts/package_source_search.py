"""Build the single email attachment for the AMS source-search paper."""
from hashlib import sha256
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "source-search"


def main():
    main_source = (PAPER / "main.tex").read_text(encoding="utf-8")
    for name in ("sharper-large-sieve.tex", "two-channel.tex"):
        marker = "\\input{source-search/" + name + "}"
        if marker not in main_source:
            raise ValueError(f"missing proof section: {name}")
        main_source = main_source.replace(marker, (PAPER / name).read_text(encoding="utf-8"))
    main_source = main_source.replace("source-search/figures/", "figures/")
    if "\\input{" in main_source:
        raise ValueError("the email source still has an external TeX input")

    files = {
        "main.tex": main_source.encode("utf-8"),
        "erdosmdpi.pdf": (PAPER / "main.pdf").read_bytes(),
        "CITATION.cff": (PAPER / "CITATION.cff").read_bytes(),
    }
    for name in ("source-hyperbola", "two-channel-flow"):
        for suffix in (".tex", ".png"):
            files["figures/" + name + suffix] = (PAPER / "figures" / (name + suffix)).read_bytes()
    for name in ("verification.json", "million-census.json", "two-channel-checks.json",
                 "sharper-large-sieve.tex", "two-channel.tex"):
        files["source-search/" + name] = (PAPER / name).read_bytes()
    for name in ("source_search.py", "source_census.py", "two_channel.py"):
        files["checks/python/" + name] = (ROOT / "checks/python" / name).read_bytes()
    files["README.txt"] = (
        "Stronger sieve bounds and complete Type I source searches\n"
        "for the Erdos-Straus equation\n\n"
        "Authors: Deep Bhattacharjee, Tristan Romanov, Ushashi Bhattacharya.\n\n"
        "Read erdosmdpi.pdf. The appendix and declarations are included in the PDF.\n"
        "Compile main.tex from this directory with three pdflatex passes:\n"
        "  pdflatex -interaction=nonstopmode -halt-on-error main.tex\n"
        "The article uses amsart. The PNG figures are already supplied.\n"
        "Their editable TikZ sources are in figures/.\n\n"
        "Exact verification, from this directory:\n"
        "  python checks/python/source_search.py --limit 200000 "
        "--report source-search/verification.json\n"
        "  python checks/python/source_census.py --limit 1000000 "
        "--report source-search/million-census.json\n"
        "  python checks/python/two_channel.py\n\n"
        "Repository: https://github.com/anaxia-research/ErdosProblem1\n"
        "This archive is a single attachment containing the paper and supporting files.\n"
    ).encode("utf-8")

    manifest = "".join(f"{sha256(data).hexdigest()}  {name}\n"
                       for name, data in sorted(files.items()))
    files["MANIFEST.sha256"] = manifest.encode("ascii")
    output = PAPER / "erdosmdpitex.zip"
    temporary = PAPER / "erdosmdpitex.zip.tmp"
    with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 15, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            archive.writestr(info, data)
    with zipfile.ZipFile(temporary) as archive:
        if archive.testzip() is not None:
            raise ValueError("archive integrity check failed")
        if set(archive.namelist()) != set(files):
            raise ValueError("archive contents do not match the manifest")
    temporary.replace(output)
    print(f"{output.name}: {len(files)} files, {output.stat().st_size} bytes")
    print("SHA-256", sha256(output.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
