.PHONY: nesrev test check-agent-playbooks check-repo-hygiene test-shell project-doctor project-init project-regenerate-asm project-regenerate-check project-prior-reuse-check project-verify project-docs-check project-docs-provenance-lint project-ci projects-ci projects-policy-check project-inventory project-audit project-comment-audit project-compare project-static-analysis project-hidden-code-scan project-intake project-process-check project-maturity-check project-maturity-summary project-semantic-claims-check project-policy-baseline-check project-data-extent-check project-pass-prep project-next-pass project-pass-start project-pass-closeout project-pass-review-packet project-pass-review-start project-raw-ram-review mod-new mod-build mod-patch clean

# Single-quote a raw command-line token for the recipe shell. $(value ...)
# prevents Make from consuming a dollar-prefixed target before this helper runs.
shell_quote_raw = '$(subst ','"'"',$(1))'

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

project-regenerate-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-regenerate-check PROJECT=<slug> [STRICT=1] [REGENERATE_DIFF_MAX_LINES=<count>]"; exit 2; fi
	bash scripts/project_regenerate_check.sh $(PROJECT)

project-prior-reuse-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-prior-reuse-check PROJECT=<slug> [STRICT=1]"; exit 2; fi
	bash scripts/project_prior_reuse_check.sh $(PROJECT) $(if $(filter 1 true yes,$(STRICT)),--strict,)

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

projects-policy-check:
	bash scripts/projects_policy_check.sh

projects-ci:
	bash scripts/projects_ci.sh

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

project-policy-baseline-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-policy-baseline-check PROJECT=<slug> [REQUIRE=1]"; exit 2; fi
	bash scripts/project_policy_baseline_check.sh $(PROJECT) $(if $(filter 1 true yes,$(REQUIRE)),--require,)

project-data-extent-check:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-data-extent-check PROJECT=<slug>"; exit 2; fi
	@bash -c 'source scripts/project_common.sh; load_project_conf "$(PROJECT)"; bash scripts/data_extent_assertions_check.sh "$$ASM_FILE" "$$DATA_EXTENT_ASSERTIONS_FILE"'

project-pass-prep:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-prep PROJECT=<slug>"; exit 2; fi
	bash scripts/project_pass_prep.sh $(PROJECT)

project-next-pass:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-next-pass PROJECT=<slug> [FORMAT=text|json]"; exit 2; fi
	@bash scripts/project_next_pass.sh $(PROJECT) $(if $(FORMAT),$(FORMAT),text)

project-pass-start: export NESREV_PASS_CORRIDOR := $(value CORRIDOR)
project-pass-start: export NESREV_PASS_WHY_NOW := $(value WHY_NOW)
project-pass-start: export NESREV_PASS_BOUNDARIES := $(value BOUNDARIES)
project-pass-start: export NESREV_PASS_EVIDENCE := $(value EVIDENCE)
project-pass-start: export NESREV_PASS_OUT_OF_SCOPE := $(value OUT_OF_SCOPE)
project-pass-start:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-start PROJECT=<slug> [PASS=<id>] [TARGET=<symbol_or_override>] [CORRIDOR=<text>] [WHY_NOW=<text>] [BOUNDARIES=<text>] [EVIDENCE=<text>] [OUT_OF_SCOPE=<text>]"; exit 2; fi
	@target=$(call shell_quote_raw,$(value TARGET)); \
	target="$$(python3 -c 'import re, sys; t=sys.argv[1]; m=re.fullmatch(r"raw_\$$*([0-9A-Fa-f]{1,4})", t); print(f"raw_$${int(m.group(1), 16):04X}" if m else t)' "$$target")"; \
	CORRIDOR="$${NESREV_PASS_CORRIDOR}" \
	WHY_NOW="$${NESREV_PASS_WHY_NOW}" \
	BOUNDARIES="$${NESREV_PASS_BOUNDARIES}" \
	EVIDENCE="$${NESREV_PASS_EVIDENCE}" \
	OUT_OF_SCOPE="$${NESREV_PASS_OUT_OF_SCOPE}" \
	bash scripts/project_pass_start.sh "$(PROJECT)" "$(PASS)" "$$target"

project-pass-closeout: export NESREV_PASS_FOCUS := $(value FOCUS)
project-pass-closeout: export NESREV_PASS_NOTES := $(value NOTES)
project-pass-closeout: export NESREV_PASS_DEFERRALS := $(value DEFERRALS)
project-pass-closeout: export NESREV_PASS_REWORK_ITEMS := $(value REWORK_ITEMS)
project-pass-closeout:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-pass-closeout PROJECT=<slug> [PASS=<id>] [VERIFY_MODE=strict|relaxed] [FOCUS=<text>] [NOTES=<text>] [DEFERRALS=<...>] [REWORK_ITEMS=<count>]"; exit 2; fi
	@FOCUS="$${NESREV_PASS_FOCUS}" \
	NOTES="$${NESREV_PASS_NOTES}" \
	DEFERRALS="$${NESREV_PASS_DEFERRALS}" \
	REWORK_ITEMS="$${NESREV_PASS_REWORK_ITEMS}" \
	bash scripts/project_pass_closeout.sh "$(PROJECT)" "$(PASS)" "$(VERIFY_MODE)"

project-pass-review-packet: export ALLOW_UNRESOLVED_LXXXX := $(ALLOW_UNRESOLVED_LXXXX)
project-pass-review-packet:
	@if [ -z "$(PROJECT)" ] || [ -z "$(BASE)" ] || [ -z "$(HEAD)" ]; then echo "usage: make project-pass-review-packet PROJECT=<slug> BASE=<base-ref> HEAD=<head-ref> [ALLOW_UNRESOLVED_LXXXX=1] [OUT=<packet.md>]"; exit 2; fi
	@if [ -n "$(OUT)" ]; then bash scripts/project_pass_review_packet.sh "$(PROJECT)" "$(BASE)" "$(HEAD)" > "$(OUT)"; else bash scripts/project_pass_review_packet.sh "$(PROJECT)" "$(BASE)" "$(HEAD)"; fi

project-pass-review-start: export NESREV_PASS_LEARNING := $(value LEARNING)
project-pass-review-start:
	@if [ -z "$(PROJECT)" ] || [ -z "$(PASS)" ]; then echo "usage: make project-pass-review-start PROJECT=<slug> PASS=<id> [BASE=<base-ref>] [HEAD=<head-ref>] [RUN_ID=<id>] [MAX_ROUNDS=<n>] [ALLOW_UNRESOLVED_LXXXX=1] [LEARNING=<text>]"; exit 2; fi
	@learning="$${NESREV_PASS_LEARNING}"; \
	set -- \
	  --project "$(PROJECT)" \
	  --pass-id "$(PASS)" \
	  --head "$(if $(HEAD),$(HEAD),HEAD)"; \
	if [ -n "$(BASE)" ]; then set -- "$$@" --base "$(BASE)"; fi; \
	if [ -n "$(RUN_ID)" ]; then set -- "$$@" --run-id "$(RUN_ID)"; fi; \
	if [ -n "$(MAX_ROUNDS)" ]; then set -- "$$@" --max-rounds "$(MAX_ROUNDS)"; fi; \
	if [ -n "$(filter 1 true yes,$(ALLOW_UNRESOLVED_LXXXX))" ]; then set -- "$$@" --allow-unresolved-lxxxx; fi; \
	if [ -n "$$learning" ]; then set -- "$$@" --learning "$$learning"; fi; \
	python3 scripts/agent_review.py start-pass "$$@"

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

project-static-analysis:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-static-analysis PROJECT=<slug>"; exit 2; fi
	@bash scripts/project_static_analysis.sh $(PROJECT)

project-hidden-code-scan:
	@if [ -z "$(PROJECT)" ]; then echo "usage: make project-hidden-code-scan PROJECT=<slug> [MIN_SIZE=12] [THRESHOLD=22] [MAX_START_OFFSET=64]"; exit 2; fi
	@MIN_SIZE="$(MIN_SIZE)" THRESHOLD="$(THRESHOLD)" MAX_START_OFFSET="$(MAX_START_OFFSET)" bash scripts/project_hidden_code_scan.sh "$(PROJECT)"

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
