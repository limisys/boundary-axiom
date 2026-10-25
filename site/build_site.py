#!/usr/bin/env python3
"""Build the static dark site from the Markdown documents.

No external network: MathJax is vendored under site/assets/mathjax.
"""
from __future__ import annotations

import html
import json
import shutil
from pathlib import Path

from markdown_it import MarkdownIt

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DOCS = ROOT / "docs"

SITE = "https://limisys.github.io/boundary-axiom/"
AUTHOR_NAME = "Xueqiang Gao"
ORCID = "https://orcid.org/0009-0008-3821-3454"
REPO = "https://github.com/limisys/boundary-axiom"
DOI = "https://doi.org/10.5281/zenodo.23627627"
OG_ALT = "Boundary / Axiom \u2014 the boundary is the report"

NAV = """<header class="sitebar">
  <div class="sitebar-inner">
    <a class="brand" href="index.html">Boundary <span>/</span> Axiom</a>
    <nav>
      <a href="index.html">Entry</a>
      <a href="technical.html">Technical</a>
      <a href="evidence.html">Evidence</a>
      <a href="open-bridge.html">Open bridge</a>
      <a href="https://github.com/limisys/boundary-axiom">GitHub</a>
    </nav>
  </div>
</header>"""

FOOTER = """<footer>
  <div class="wrap">
    <div>The Boundary Is the Report · public site · 2026-10-23</div>
    <div>Code Apache-2.0 · documentation CC BY 4.0 · papers are preprints, not peer-reviewed.</div>
    <div><a href="https://github.com/limisys/boundary-axiom">Repository</a> · <a href="technical.html">Technical edition</a> · <a href="https://github.com/limisys/boundary-axiom/issues">Issues</a></div>
  </div>
</footer>"""

MATHJAX = """<script>
window.MathJax = {
  tex: {
    inlineMath: [['$', '$'], ['\\\\(', '\\\\)']],
    displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']],
    processEscapes: true,
    tags: 'none'
  },
  svg: { fontCache: 'global', mtextInheritFont: true },
  options: {
    enableMenu: false,
    skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
  }
};
</script>
<script defer src="assets/mathjax/tex-svg-full.js"></script>"""

PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<meta name="description" content="{desc}">
<link rel="canonical" href="{url}">
<meta name="author" content="Xueqiang Gao">
<meta name="robots" content="{robots}">
<meta name="theme-color" content="#0a0c0f">
<meta property="og:site_name" content="Boundary / Axiom">
<meta property="og:type" content="article">
<meta property="og:locale" content="en_US">
<meta property="og:title" content="{title}">
<meta property="og:description" content="{desc}">
<meta property="og:url" content="{url}">
<meta property="og:image" content="{site}assets/og.png">
<meta property="og:image:width" content="1200">
<meta property="og:image:height" content="630">
<meta property="og:image:alt" content="{ogalt}">
<meta name="twitter:card" content="summary_large_image">
<meta name="twitter:title" content="{title}">
<meta name="twitter:description" content="{desc}">
<meta name="twitter:image" content="{site}assets/og.png">
<meta name="twitter:image:alt" content="{ogalt}">
<link rel="stylesheet" href="assets/style.css">
{mathjax}
{jsonld}
</head>
<body>
{nav}
<main class="wrap">
{body}
</main>
{footer}
</body>
</html>
"""


def render(md_path: Path) -> str:
    md = MarkdownIt("default", {"html": True, "linkify": False, "typographer": False})
    text = md_path.read_text(encoding="utf-8")
    # CommonMark treats backslash-bracket as an escape. Protect TeX delimiters
    # before parsing, then restore them for MathJax.
    text = (text.replace(r"\[", "MATHOPENDBL")
                .replace(r"\]", "MATHCLOSEDBL")
                .replace(r"\(", "MATHOPENINL")
                .replace(r"\)", "MATHCLOSEINL"))
    out = md.render(text)
    out = (out.replace("MATHOPENDBL", r"\[")
              .replace("MATHCLOSEDBL", r"\]")
              .replace("MATHOPENINL", r"\(")
              .replace("MATHCLOSEINL", r"\)"))
    return out


def page_url(slug: str) -> str:
    return SITE if slug in ("", "index.html") else SITE + slug


def jsonld(title: str, desc: str, url: str, kind: str = "WebPage") -> str:
    person = {
        "@type": "Person",
        "@id": SITE + "#author",
        "name": AUTHOR_NAME,
        "alternateName": "\u9ad8\u5b66\u5f3a",
        "identifier": ORCID,
        "url": "https://limisys.github.io/",
        "sameAs": ["https://github.com/limisys", ORCID],
    }
    website = {
        "@type": "WebSite",
        "@id": SITE + "#website",
        "url": SITE,
        "name": "Boundary / Axiom",
        "description": "The Boundary Cognition Hypothesis, formalized in Lean 4: "
                       "boundary\u2013report identity on Moore families.",
        "inLanguage": "en",
        "author": {"@id": SITE + "#author"},
    }
    page = {
        "@type": kind,
        "@id": url + "#page",
        "url": url,
        "name": title,
        "description": desc,
        "isPartOf": {"@id": SITE + "#website"},
        "author": {"@id": SITE + "#author"},
        "inLanguage": "en",
        "image": SITE + "assets/og.png",
    }
    graph = [person, website, page]
    if kind == "WebPage" and url == SITE:
        graph.append({
            "@type": "SoftwareSourceCode",
            "name": "boundary-axiom",
            "description": "Lean 4 formalization of boundary\u2013report identity "
                           "on Moore families, with a finite-state consistency gate.",
            "codeRepository": REPO,
            "programmingLanguage": "Lean 4",
            "version": "1.1.1",
            "identifier": DOI,
            "author": {"@id": SITE + "#author"},
            "isPartOf": {"@id": SITE + "#website"},
        })
    data = {"@context": "https://schema.org", "@graph": graph}
    return ('<script type="application/ld+json">\n'
            + json.dumps(data, ensure_ascii=False, indent=1)
            + "\n</script>")


def paper_page(title: str, desc: str, body: str, slug: str) -> str:
    body = (
        '<a class="back" href="index.html">← Index</a>\n'
        '<article class="paper">\n' + body + "\n</article>"
    )
    url = page_url(slug)
    return PAGE.format(
        title=html.escape(title),
        desc=html.escape(desc, quote=True),
        url=url,
        robots="index,follow,max-image-preview:large",
        site=SITE,
        ogalt=OG_ALT,
        jsonld=jsonld(title, desc, url),
        mathjax=MATHJAX,
        nav=NAV,
        body=body,
        footer=FOOTER,
    )


LANDING = """<section class="hero">
  <p class="kicker">Public site 1.0.1 · machine-checked core</p>
  <h1>The boundary<br><em>is the report.</em></h1>
  <p class="lede">A log can be stale. A report can be decoration. The question is
  whether a boundary and its report are two objects — or one.</p>
  <div class="actions">
    <a class="button" href="programme.html">Read the programme</a>
    <a class="quiet" href="technical.html">The formal core →</a>
  </div>
</section>

<section>
  <p class="label">The claim</p>
  <div class="claim">
    <p>On the class of <strong>Moore report families</strong>, a boundary closure
    operator and the system's report family determine each other. The report
    family is exactly the fixed-point family of the operator. Outside that class,
    the identity fails — and there is a machine-checked counterexample.</p>
  </div>
  <p style="margin-top:26px">The result is conditional and narrow. It does not say
  that every autonomous system has a Moore family, that the attribution layer has
  been bridged to the closure layer, or that a deployed agent cannot bypass the
  gate. Those are separate claims, and they are not made here.</p>
</section>

<section>
  <p class="label">Evidence, without inflation</p>
  <h2>467 theorems and lemmas.<br>90 definitions. Zero <em>sorry</em>.</h2>
  <div class="numbers">
    <div class="number"><b>56</b><span>Lean files</span></div>
    <div class="number"><b>467</b><span>Theorems / lemmas</span></div>
    <div class="number"><b>90</b><span>Definitions</span></div>
    <div class="number"><b>0</b><span>Sorry / custom axioms</span></div>
  </div>
  <p style="font-size:.9rem;color:var(--muted);margin-top:14px">This is the
  full verified corpus. The report-identity core is a six-module / 45-theorem
  subset under <code>report-core/</code>; the A-module contributes 33
  declarations. The numbers answer different questions and are not
  interchangeable.</p>
</section>

<section class="split">
  <div>
    <p class="label">What is proved</p>
    <ul class="list">
      <li><b>c<sub>R</sub> is a closure operator</b> for any report family.</li>
      <li><b>Moore families determine their closure</b> uniquely.</li>
      <li><b>Report = closed sets</b> is a joint fixed point, not a metaphor.</li>
      <li><b>Representation</b>: every Moore family is a closure's fixed family.</li>
      <li><b>The condition cannot be dropped</b>: a non-Moore counterexample.</li>
      <li><b>A finite gate</b> with R1–R7 and atomic commit, 14/14 tests.</li>
    </ul>
  </div>
  <div>
    <p class="label">What is not claimed</p>
    <ul class="list">
      <li><b>Not universal.</b> Conditional on the Moore structure.</li>
      <li><b>Not the attribution bridge.</b> A → closure is still open.</li>
      <li><b>Not a unique level.</b> The parameter w is not fixed by V.</li>
      <li><b>Not A7 from category.</b> The potential is a model-class result.</li>
      <li><b>Not production.</b> The gate is a finite-state reference.</li>
      <li><b>Not a theory of consciousness.</b> Functional and architectural only.</li>
    </ul>
  </div>
</section>

<section>
  <p class="label">Artifacts</p>
  <div class="artifact-grid">
    <a class="artifact" href="programme.html"><b>Programme</b><span>Why the claim matters; what the programme refuses to claim.</span></a>
    <a class="artifact" href="technical.html"><b>Technical edition</b><span>Definitions, results, negative control, scope.</span></a>
    <a class="artifact" href="evidence.html"><b>Evidence ledger</b><span>Counts by scope, hashes, build and gate records.</span></a>
    <a class="artifact" href="open-bridge.html"><b>Open bridge</b><span>The attribution → closure gap, stated plainly.</span></a>
    <a class="artifact" href="https://github.com/limisys/boundary-axiom/tree/main/report-core/lean"><b>Report-identity core</b><span>Six modules; entry ReportIdentity.</span></a>
    <a class="artifact" href="https://github.com/limisys/boundary-axiom/blob/main/architecture/gate_reference.py"><b>Gate reference</b><span>R1–R7 finite-state implementation.</span></a>
  </div>
</section>

<section>
  <p class="label">The wager</p>
  <h2>Not a finished theory. A way to ask the question that keeps the answer honest.</h2>
  <p>If the relation can be made precise, it gives a way to talk about
  self-organisation without an inner observer — and a way to build systems whose
  reports are not decorative. The wager may fail. The formal condition may be too
  strong for an interesting system, or too weak to distinguish boundary cognition
  from ordinary control. The release is written so that those failures can be
  discovered.</p>
  <div class="actions" style="margin-top:26px">
    <a class="button" href="technical.html">Read what is proved</a>
    <a class="quiet" href="open-bridge.html">See what is open →</a>
  </div>
</section>"""


def build_landing() -> str:
    title = "The Boundary Is the Report"
    desc = ("A machine-checked Lean 4 core for boundary–report identity on Moore "
            "families, with a finite-state consistency gate.")
    return PAGE.format(
        title=title,
        desc=desc,
        url=SITE,
        robots="index,follow,max-image-preview:large",
        site=SITE,
        ogalt=OG_ALT,
        jsonld=jsonld(title, desc, SITE),
        mathjax="",
        nav=NAV,
        body=LANDING,
        footer=FOOTER,
    )


def build_404() -> str:
    body = """<section class="hero">
  <p class="kicker">404</p>
  <h1>No such<br><em>page.</em></h1>
  <p class="lede">The boundary of this site is smaller than you thought.</p>
  <div class="actions"><a class="button" href="index.html">Return to index</a></div>
</section>"""
    url = SITE + "404.html"
    return PAGE.format(
        title="404 — The Boundary Is the Report",
        desc="Page not found.",
        url=url,
        robots="noindex,follow",
        site=SITE,
        ogalt=OG_ALT,
        jsonld=jsonld("404 — The Boundary Is the Report", "Page not found.", url),
        mathjax="",
        nav=NAV,
        body=body,
        footer=FOOTER,
    )


def main() -> int:
    pages = {
        "programme.html": (
            "Mind Has Boundaries: A Research Programme",
            "A research programme on boundary identification, representation, and maintenance; what it claims and refuses to claim.",
            DOCS / "PROGRAMME_EN.md",
        ),
        "technical.html": (
            "The report-identity core: what is proved, and what is not",
            "The formal objects, Moore report families, representation, negative control, gate, and scope.",
            DOCS / "TECHNICAL_PUBLIC.md",
        ),
        "evidence.html": (
            "Evidence ledger",
            "Counts by scope, hashes, build and gate records, and open items.",
            DOCS / "PUBLIC_EVIDENCE.md",
        ),
        "open-bridge.html": (
            "The open bridge: attribution → closure",
            "The attribution-to-closure gap, the section/level problem, and what a bridge would need.",
            DOCS / "OPEN_BRIDGE.md",
        ),
    }
    for name, (title, desc, path) in pages.items():
        (HERE / name).write_text(paper_page(title, desc, render(path), name), encoding="utf-8")
        print("OK", name)
    (HERE / "index.html").write_text(build_landing(), encoding="utf-8")
    print("OK index.html")
    (HERE / "404.html").write_text(build_404(), encoding="utf-8")
    print("OK 404.html")
    (HERE / "robots.txt").write_text(
        "User-agent: *\nAllow: /\n\nSitemap: " + SITE + "sitemap.xml\n",
        encoding="utf-8",
    )
    (HERE / "sitemap.xml").write_text(
        """<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
  <url><loc>https://limisys.github.io/boundary-axiom/</loc></url>
  <url><loc>https://limisys.github.io/boundary-axiom/programme.html</loc></url>
  <url><loc>https://limisys.github.io/boundary-axiom/technical.html</loc></url>
  <url><loc>https://limisys.github.io/boundary-axiom/evidence.html</loc></url>
  <url><loc>https://limisys.github.io/boundary-axiom/open-bridge.html</loc></url>
  <url><loc>https://limisys.github.io/boundary-axiom/demo.html</loc></url>
  <url><loc>https://limisys.github.io/boundary-axiom/bounty.html</loc></url>
</urlset>
""",
        encoding="utf-8",
    )
    print("OK robots.txt / sitemap.xml")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
