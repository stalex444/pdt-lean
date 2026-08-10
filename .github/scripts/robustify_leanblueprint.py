#!/usr/bin/env python3
"""Tolerate TeXFragment items in \\lean{decls} (pending an upstream fix).

plasTeX sometimes delivers a \\lean argument as a TeXFragment wrapping the
plain declaration string instead of the string itself (observed 2026-08-10;
python-version- and content-sensitive). leanblueprint's digest then dies on
`dec.strip()`. This patches the installed package to accept both shapes.
Idempotent; exits 1 loudly if the target line is missing so an upstream
release that changes the code surfaces here instead of silently unpatched.
"""
import pathlib
import sys

import leanblueprint

pkg = pathlib.Path(leanblueprint.__file__).parent / "Packages" / "blueprint.py"
src = pkg.read_text()
ROBUST = ("        decls = [dec.strip() if isinstance(dec, str)\n"
          "                 else getattr(dec, 'source', str(dec)).strip()\n"
          "                 for dec in self.attributes['decls']]")
TARGET = "        decls = [dec.strip() for dec in self.attributes['decls']]"
if ROBUST in src:
    print("already robust — nothing to do")
    sys.exit(0)
if TARGET not in src:
    print("PATCH TARGET NOT FOUND — leanblueprint changed upstream; "
          "re-inspect before trusting the web build.")
    sys.exit(1)
pkg.write_text(src.replace(TARGET, ROBUST))
print(f"patched {pkg}")
