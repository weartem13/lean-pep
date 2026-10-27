# Retained mathematical inputs and evidence

`fixtures/` contains the full input and generated-data collection used by the maintenance tests. A file named `generated`, `Imported`, `raw`, or `selected` is not a disposable build output. Keep these files under version control.

`cases/` separates concrete PG and GD instances by horizon and role. The exact one-step pairs and the earlier GD gap pair are separate cases. `paper/` supplies the fixed eight-configuration PG2 study and the historical execution records used in the paper.

The case files and batch capture/selected/proof files were copied byte-for-byte. The [evidence index](paper/evidence-index.json) records every old location, new location, original hash, public hash, and path-redaction operation. Original execution logs and frozen manifests remain in the private migration archive. Public execution records whose `content_changed` flag is true are explicitly derived copies with local path prefixes replaced by `<AUTHOR_HOME>`, `<WORK_TMP>`, or `<SYSTEM_TEMP>`; numerical results, command arguments other than local prefixes, exit status, and timings retain their original meaning. They are not original-byte logs or executions under this reorganized source identity.

Use the project verification entry points for current execution. Historical experiment scripts are supplied as provenance, with their original layout assumptions documented; they are not a second recommended command interface.
