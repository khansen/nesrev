.PHONY: nesrev test check-agent-playbooks check-repo-hygiene test-shell project-doctor project-init project-regenerate-asm project-verify project-docs-check project-docs-provenance-lint project-ci project-inventory project-audit project-comment-audit project-compare project-intake project-process-check project-maturity-check project-maturity-summary project-semantic-claims-check project-legacy-retrofit-check project-data-extent-check project-pass-prep project-next-pass project-pass-start project-pass-closeout project-pass-finish project-raw-ram-review mod-new mod-build mod-patch clean

nesrev:
	javac NESrev.java -Xlint:unchecked

check-agent-playbooks:
	python3 scripts/check_agent_playbooks.py --strict

check-repo-hygiene:
	bash scripts/check_repo_hygiene.sh

test-shell:
	bash tests/shell/run_all.sh

test: check-agent-playbooks check-repo-hygiene test-shell
	javac NESrev.java NESrevTest.java -Xlint:unchecked
	java NESrevTest

project-doctor:
	bash scripts/project_doctor.sh

project-init:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-init PROJECT=<slug>"; exit 2; fi
	bash scripts/new_project.sh $(PROJECT)

project-regenerate-asm:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-regenerate-asm PROJECT=<slug> [CODEPOINTERS=<override>] [CODEENTRIES=<override>] [DATAPOINTERS=<override>] [INLINECALLS=<override>] [DATARANGES=<override>]"; exit 2; fi
	bash scripts/project_regenerate_asm.sh $(PROJECT) "$(CODEPOINTERS)" "$(CODEENTRIES)" "$(DATAPOINTERS)" "$(INLINECALLS)" "$(DATARANGES)"

project-verify:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-verify PROJECT=<slug>"; exit 2; fi
	bash scripts/project_verify.sh $(PROJECT)

project-docs-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-docs-check PROJECT=<slug>"; exit 2; fi
	bash scripts/project_docs_check.sh $(PROJECT)

project-docs-provenance-lint:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-docs-provenance-lint PROJECT=<slug>"; exit 2; fi
	bash scripts/project_docs_provenance_lint.sh $(PROJECT)

project-ci:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-ci PROJECT=<slug>"; exit 2; fi
	bash scripts/project_ci.sh $(PROJECT)

project-intake:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-intake PROJECT=<slug>"; exit 2; fi
	bash scripts/project_intake.sh $(PROJECT)

project-process-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-process-check PROJECT=<slug>"; exit 2; fi
	bash scripts/project_process_check.sh $(PROJECT)

project-maturity-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-maturity-check PROJECT=<slug>"; exit 2; fi
	bash scripts/project_maturity_check.sh $(PROJECT)

project-maturity-summary:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-maturity-summary PROJECT=<slug>"; exit 2; fi
	@bash scripts/project_maturity_summary.sh $(PROJECT)

project-semantic-claims-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-semantic-claims-check PROJECT=<slug>"; exit 2; fi
	bash scripts/project_semantic_claims_check.sh $(PROJECT)

project-legacy-retrofit-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-legacy-retrofit-check PROJECT=<slug> [REQUIRE=1]"; exit 2; fi
	bash scripts/project_legacy_retrofit_check.sh $(PROJECT) $(if $(filter 1 true yes,$(REQUIRE)),--require,)

project-data-extent-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-data-extent-check PROJECT=<slug>"; exit 2; fi
	@bash -c 'source scripts/project_common.sh; load_project_conf "$(PROJECT)"; bash scripts/data_extent_assertions_check.sh "$$ASM_FILE" "$$DATA_EXTENT_ASSERTIONS_FILE"'

project-pass-prep:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-prep PROJECT=<slug>"; exit 2; fi
	bash scripts/project_pass_prep.sh $(PROJECT)

project-next-pass:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-next-pass PROJECT=<slug> [FORMAT=text|json]"; exit 2; fi
	@bash scripts/project_next_pass.sh $(PROJECT) $(if $(FORMAT),$(FORMAT),text)

# Forward the corridor-objective fields through the recipe environment via
# target-specific export so prose values (apostrophes, spaces) are passed
# verbatim without shell re-quoting. project_pass_start.sh reads them from
# os.environ; empty values are treated as omitted.
project-pass-start: export CORRIDOR := $(CORRIDOR)
project-pass-start: export WHY_NOW := $(WHY_NOW)
project-pass-start: export BOUNDARIES := $(BOUNDARIES)
project-pass-start: export EVIDENCE := $(EVIDENCE)
project-pass-start: export OUT_OF_SCOPE := $(OUT_OF_SCOPE)
project-pass-start:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-start PROJECT=<slug> [PASS=<id>] [TARGET=<symbol_or_override>] [CORRIDOR=<text>] [WHY_NOW=<text>] [BOUNDARIES=<text>] [EVIDENCE=<text>] [OUT_OF_SCOPE=<text>]"; exit 2; fi
	@target='$(subst $$,$$$$,$(TARGET))'; \
	target="$$(python3 -c 'import re, sys; t=sys.argv[1]; m=re.fullmatch(r"raw_\$$*([0-9A-Fa-f]{1,4})", t); print(f"raw_$${int(m.group(1), 16):04X}" if m else t)' "$$target")"; \
	bash scripts/project_pass_start.sh "$(PROJECT)" "$(PASS)" "$$target"

project-pass-closeout:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-closeout PROJECT=<slug> [PASS=<id>]"; exit 2; fi
	@bash scripts/project_pass_closeout.sh $(PROJECT) $(PASS)

project-pass-finish: export FOCUS := $(FOCUS)
project-pass-finish: export NOTES := $(NOTES)
project-pass-finish:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-finish PROJECT=<slug> [PASS=<id>] [VERIFY_MODE=strict|relaxed] [FOCUS=<text>] [NOTES=<text>]"; exit 2; fi
	@bash scripts/project_pass_finish.sh "$(PROJECT)" "$(PASS)" "$(VERIFY_MODE)"

project-raw-ram-review:
	@if [ -z "$(PROJECT)" ] || [ -z "$(ADDR)" ] || [ -z "$(STATUS)" ]; then echo "usage: make project-raw-ram-review PROJECT=<slug> ADDR=<0x00bf|\\$$00BF> STATUS=<candidate|unreviewed|deferred|revisit|not_semantic_yet|symbolized> [SYMBOL=<name>] [NOTES=<text>] [PASS=<id>]"; exit 2; fi
	@bash scripts/project_raw_ram_review.sh "$(PROJECT)" "$(ADDR)" "$(STATUS)" "$(SYMBOL)" "$(NOTES)" "$(PASS)"

project-inventory:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-inventory PROJECT=<slug>"; exit 2; fi
	bash scripts/refresh_inventory.sh $(PROJECT)

project-audit:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-audit PROJECT=<slug> [FORMAT=text|json]"; exit 2; fi
	@bash scripts/project_audit.sh $(PROJECT) $(if $(FORMAT),$(FORMAT),text)

project-comment-audit:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-comment-audit PROJECT=<slug> [FORMAT=text|json]"; exit 2; fi
	@bash scripts/project_comment_audit.sh $(PROJECT) $(if $(FORMAT),$(FORMAT),text)

project-compare:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-compare PROJECT=<slug> [FORMAT=text|json]"; exit 2; fi
	@bash scripts/project_compare.sh $(PROJECT) $(if $(FORMAT),$(FORMAT),text)

mod-new:
	@if [ -z "$(PROJECT)" ] || [ -z "$(MOD)" ]; then echo "usage: make mod-new PROJECT=<slug> MOD=<mod_slug>"; exit 2; fi
	bash scripts/new_mod.sh $(PROJECT) $(MOD)

mod-build:
	@if [ -z "$(PROJECT)" ] || [ -z "$(MOD)" ]; then echo "usage: make mod-build PROJECT=<slug> MOD=<mod_slug>"; exit 2; fi
	bash scripts/build_mod.sh $(PROJECT) $(MOD)

mod-patch:
	@if [ -z "$(PROJECT)" ] || [ -z "$(MOD)" ]; then echo "usage: make mod-patch PROJECT=<slug> MOD=<mod_slug> [FORMAT=ips|bps]"; exit 2; fi
	bash scripts/create_mod_patch.sh $(PROJECT) $(MOD) $(if $(FORMAT),$(FORMAT),ips)

clean:
	rm -f *.class *.o
