# Stronger sieve bounds and complete Type I source searches

**Deep Bhattacharjee, Tristan Romanov, and Ushashi Bhattacharya**

[Read the AMS paper](main.pdf) · [Email attachment](erdosmdpitex.zip) · [LaTeX source](main.tex) · [Verification report](verification.json) · [First-source census](million-census.json)

The revised large-sieve proof allows every density saving constant below 0.804900912498. The complementary finite search covers the entire specified Type I source family. The paper contains both proofs and the computational appendix.

The paper develops Tristan Romanov’s supplied sieve manuscript and gives an exact counterexample to the square-root search cutoff. For the prime 30241, every source through 160 fails, and source 161 with divisor 27 yields the denominators 7567, 8520442, and 1600414202. The full Erdős–Straus conjecture remains open.

The fixed-depth estimate, uniform estimate at logarithmic depth, and growing-depth arithmetic large-sieve proof use the stated standard analytic number theory results. The finite computations check certificates and the pointwise obstruction.

Build from the repository root with three passes.

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=source-search source-search/main.tex
~~~

The following commands reproduce the exact reports with Python’s standard library.

~~~sh
python checks/python/source_search.py --limit 200000 --report source-search/verification.json
python checks/python/source_census.py --limit 1000000 --report source-search/million-census.json
python checks/python/two_channel.py
~~~

The original supplied file was *fixed_m_proof.pdf*, titled *Failure of the first M sources: a sieve bound and its dependence on M*, attributed to Tristan Romanov in its PDF metadata. Its SHA-256 is `c3cf6dd2227f370803d2c24f3797ef2b201b01afe76b641d16b2e1b4428d7a73`. Its source and sieve arguments are credited to Tristan Romanov in the revised paper.

The publication-formatted manuscript is prepared for coauthor review. Coauthor approval and journal submission remain pending. The numerical and algebraic checks do not formalize the analytic sieve theorems in Lean.

The affiliations and the two available ORCIDs follow the [Yang–Mills metadata](https://github.com/anaxia-research/4Y-M/blob/main/CITATION.cff). Tristan Romanov has no ORCID. The archive contains one PDF with its appendix, a complete AMS article source, the included PNG figures with their original TikZ sources, and verification programs and reports.

Funding, ethics, conflicts of interest, data availability, and AI-assistance declarations appear before the references. Regenerate the single attachment after compiling the PDF with the following command.

~~~sh
python scripts/package_source_search.py
~~~
