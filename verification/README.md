# Verification

Run the complete check from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
python3 scripts/audit_health.py --output verification/health-current.json
```

The check validates module reachability and documentation links, builds the library, and checks Audit.lean. Declarations are audited by namespace and defining module, including private helpers. The permitted logical axioms are propext, Classical.choice, and Quot.sound. The health inventory also checks the actual dependency revisions and working-tree cleanliness.

The current public source snapshot matches the successful local check recorded in [self-audit-summary-20261101.json](self-audit-summary-20261101.json). Its [frozen source manifest](self-audit-source-manifest-20261101.json) lists the hashes of all formal sources and build configuration. The earlier [release baseline](release-baseline.json) and [release source manifest](release-source-manifest.json) are retained unchanged as records of that earlier snapshot.

Each successful check generates check.log, summary.json, and source-manifest.json in this directory. These generated outputs are ignored by Git. The frozen records describe the checked snapshots; run the commands above to verify a later checkout. The [build guide](../docs/BUILD.md) explains maintenance and source packaging.
