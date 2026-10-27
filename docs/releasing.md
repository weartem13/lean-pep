# Code snapshot releases

The maintained working tree is the only editing source. Code checkouts and archives are generated deliverables. Keep new run outputs, release reports, staged exports, private decisions and backups outside the source root. Retained historical research inputs under `data/` are deliberate distribution assets.

## Prepare a candidate

1. Inspect the actual working tree, including untracked inputs. Do not use `git archive HEAD` as a substitute for this tree.
2. Update the README, CHANGELOG and CITATION.cff as appropriate. Project-owned software, including Lean proof sources and Python tools, uses the official Apache-2.0 text in root `LICENSE`; the CFF software `license` is `Apache-2.0`. Retain actual third-party notices and an existing root `NOTICE`, without inventing a copyright holder. The migrated evidence maps retain the scoped CC-BY-4.0 provenance described in [evidence/README.md](evidence/README.md).
3. Check the [declaration/evidence paths](evidence/claim-evidence.md) and preserve old experiment/source bindings. Version 0.1.0 is selected for [weartem13/lean-pep](https://github.com/weartem13/lean-pep); a version field is not evidence of an existing tag or Release.
4. Choose a new absolute staging path outside the maintained tree:

```sh
python3 scripts/export.py --output "$STAGE"
```

The script validates the destination before writing a manifest or output. Its code allowlist retains `.gitignore`, generated Lean inputs, captures, selected data, PSD witnesses and all retained `data/paper` research evidence. It omits the entire local manuscript project, paper packages, Git histories, dependency/build caches, environments and specifically identified local publication records. The source and public manifests cover the same code/evidence payload; the generated manifests are excluded from their own hashes. Unreviewed hidden files and source symlinks are rejected.

5. Review the complete inventory for private material, credentials and personal paths. Retain needed research values byte-for-byte. If a public receipt needs path redaction, preserve the original privately and identify the derivative and original hash in the evidence mapping. Manuscript-only files, editing reports and paper packages must remain outside the code allowlist; do not rely on `.gitignore` to filter an exporter.
6. Validate a separate fresh export with `scripts/setup.py --output "$OUT/setup" --dependencies-only` followed by `scripts/verify.py quick --output "$OUT/quick"`. A clean external cache may be passed to setup with `--cache`; all nine revisions must match the lockfile. Never seed the new tree with LeanPEP build objects. Run affected export/setup/verification-entry tests. Record any reused historical validation by its exact scope rather than treating it as a new run.

## Publish a checked candidate

Repository initialization and remote changes require the corresponding authorization. A first code history can be initialized in the verified staging directory with `git -C "$STAGE" init -b main`. Check its top-level path before staging; never import the maintenance `.git` directory or commits.

Compare `git ls-files` with every path in `PUBLIC_MANIFEST.json`, plus `SOURCE_MANIFEST.json` and `PUBLIC_MANIFEST.json`. Check that ignore rules have not hidden required data or generated proofs. Create the initial root commit using the user's actual configured identity. Keep its SHA, archive hashes, validation logs and push receipt outside the committed tree. Do not infer authorship or software copyright from a paper byline.

For later milestones, export to a new staging directory and compare it with a clean checkout of the code repository:

```sh
rsync -an --itemize-changes --delete --exclude='.git/' "$STAGE/" "$PUBLIC/"
```

Inspect the dry-run and both roots, then synchronize the reviewed candidate with the same arguments without `-n`. The destination must be the code checkout, never the maintenance tree. Preserve the code history and append ordinary reviewed commits. History replacement, visibility changes, tags and Release publication are separate actions requiring explicit authorization; daily development is not automatically synchronized.

## Independent manuscript packaging

The author workspace retains its manuscript, PDF, licenses and editorial history separately. `scripts/export.py --paper-output` remains an explicit local packaging mode for that project; it never adds manuscript files to a normal code export. It requires the final build's `--bbl` and a fresh external destination, and follows the reviewed manuscript input tree. This code-only distribution contains no manuscript source from which to invoke that mode. Consult the locally maintained paper instructions when preparing a paper package.
