"""Validate xasm instruction-record v1 facts without parsing assembly text."""

KINDS = {"integer", "string", "symbol", "local_symbol", "forward_label", "backward_label",
         "current_pc", "operator", "member", "scope", "index", "sizeof", "mask", "datatype"}
MODES = {"implied", "accumulator", "immediate", "zeropage", "zeropage_x", "zeropage_y",
         "absolute", "absolute_x", "absolute_y", "preindexed_indirect", "postindexed_indirect",
         "indirect", "relative"}
OPERATORS = {"+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "<", ">", "==",
             "!=", "<=", ">=", "bit_not", "logical_not", "low_byte", "high_byte", "negate", "bank"}


def require(condition, message):
    if not condition:
        raise ValueError("invalid instruction records: " + message)


def span(value, check_source=None):
    require(isinstance(value, dict), "source span required")
    require(isinstance(value.get("file"), str) and value["file"], "span file required")
    for key in ("line", "column", "end_line", "end_column"):
        require(type(value.get(key)) is int and value[key] > 0, "invalid span " + key)
    require((value["end_line"], value["end_column"]) >= (value["line"], value["column"]),
            "reversed source span")
    if check_source is not None:
        check_source(value["file"])


def source(value, check_source=None):
    require(isinstance(value, dict) and isinstance(value.get("text"), str), "source text required")
    span(value.get("span"), check_source)


def expression(value, check_source=None):
    require(isinstance(value, dict) and value.get("kind") in KINDS, "unknown expression kind")
    source(value.get("source"), check_source)
    children = value.get("children")
    require(isinstance(children, list), "expression children required")
    kind = value["kind"]
    if kind == "integer":
        require(type(value.get("value")) is int and not children, "invalid integer node")
    if kind == "current_pc":
        require(not children, "invalid current_pc node")
    if kind in {"string", "symbol", "local_symbol", "forward_label", "backward_label", "datatype"}:
        require(isinstance(value.get("name"), str), "expression name required")
    if kind == "operator":
        require(value.get("operator") in OPERATORS, "unknown expression operator")
        unary = value["operator"] in {"bit_not", "logical_not", "low_byte", "high_byte", "negate", "bank"}
        require(len(children) == (1 if unary else 2), "invalid operator arity")
    for child in children:
        expression(child, check_source)


def validate(payload, check_source=None):
    require(isinstance(payload, dict) and payload.get("version") == "1", "version 1 required")
    records = payload.get("records")
    require(isinstance(records, list), "complete records array required")
    origins = set()
    previous_end = 0
    for record in records:
        require(isinstance(record, dict), "record object required")
        for key in ("origin_id", "segment_id", "output_offset", "cpu_address", "opcode", "size"):
            require(type(record.get(key)) is int and record[key] >= 0, "invalid " + key)
        require(record["origin_id"] > 0 and record["origin_id"] not in origins, "duplicate/invalid origin_id")
        origins.add(record["origin_id"])
        require(record["output_offset"] >= previous_end, "records must be in nonoverlapping output order")
        previous_end = record["output_offset"] + record["size"]
        require(record.get("addressing_mode") in MODES and record.get("parsed_addressing_mode") in MODES,
                "unknown addressing mode")
        require(type(record.get("immediate")) is bool, "immediate boolean required")
        require(record.get("index_register") in (None, "X", "Y"), "invalid index register")
        require(isinstance(record.get("mnemonic"), str) and record["mnemonic"], "mnemonic required")
        require(record.get("operand_form") in {"integer_literal", "symbol", "expression", "none"},
                "invalid operand form")
        names = record.get("referenced_symbols")
        require(isinstance(names, list) and all(isinstance(name, str) for name in names)
                and len(names) == len(set(names)), "invalid referenced symbols")
        for key in ("operand_value", "branch_displacement"):
            require(key in record and (record[key] is None or type(record[key]) is int), "invalid " + key)
        require("structural_base" in record, "missing structural base")
        base = record["structural_base"]
        if base is not None:
            require(isinstance(base, dict) and isinstance(base.get("symbol"), str)
                    and type(base.get("displacement")) is int and base.get("projection") in {"none", "low", "high"},
                    "invalid structural base")
        require("lexical_owner" in record and (record["lexical_owner"] is None
                or isinstance(record["lexical_owner"], str)), "invalid lexical owner")
        octets = record.get("bytes")
        require(isinstance(octets, list) and len(octets) == record["size"] and 1 <= len(octets) <= 3,
                "invalid emitted size")
        require(all(type(b) is int and 0 <= b <= 255 for b in octets) and octets[0] == record["opcode"],
                "invalid emitted bytes")
        span(record.get("use"), check_source)
        source(record.get("source"), check_source)
        require("operand_source" in record and "expression" in record, "missing operand provenance")
        if record["operand_source"] is not None:
            source(record["operand_source"], check_source)
        if record["expression"] is not None:
            expression(record["expression"], check_source)
        operandless = record["addressing_mode"] in {"implied", "accumulator"}
        require((record["expression"] is None) == operandless, "operand/mode mismatch")
        require((record["operand_source"] is None) == (record["parsed_addressing_mode"] == "implied"),
                "operand source/mode mismatch")
        require(record["immediate"] == (record["addressing_mode"] == "immediate"), "immediate/mode mismatch")
        mode = record["addressing_mode"]
        expected_index = ("X" if mode.endswith("_x") or mode == "preindexed_indirect" else
                          "Y" if mode.endswith("_y") or mode == "postindexed_indirect" else None)
        require(record["index_register"] == expected_index, "index/mode mismatch")
    return records


def check_binary(payload, binary):
    for record in payload["records"]:
        start = record["output_offset"]
        require(binary[start:start + record["size"]] == bytes(record["bytes"]), "instruction bytes differ from output")
