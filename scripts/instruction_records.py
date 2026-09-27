"""Validate xasm instruction-record v2 facts without parsing assembly text."""

KINDS = {"integer", "string", "symbol", "local_symbol", "forward_label", "backward_label",
         "current_pc", "operator", "member", "scope", "index", "sizeof", "mask", "datatype"}
MODES = {"implied", "accumulator", "immediate", "zeropage", "zeropage_x", "zeropage_y",
         "absolute", "absolute_x", "absolute_y", "preindexed_indirect", "postindexed_indirect",
         "indirect", "relative"}
OPERATORS = {"+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "<", ">", "==",
             "!=", "<=", ">=", "bit_not", "logical_not", "low_byte", "high_byte", "negate", "bank"}
DATA_KINDS = {"read", "write", "read_modify_write"}
MEMORY_MODES = {"zeropage", "zeropage_x", "zeropage_y", "absolute", "absolute_x", "absolute_y",
                "preindexed_indirect", "postindexed_indirect"}
POINTER_MODES = {"preindexed_indirect", "postindexed_indirect", "indirect"}
DATA_INDEX = {"zeropage_x": "X", "absolute_x": "X", "zeropage_y": "Y", "absolute_y": "Y",
              "postindexed_indirect": "Y"}
TERM_KINDS = {"integer", "string", "symbol", "local_symbol", "forward_label", "backward_label",
              "current_pc", "expression"}
NAMED_TERM_KINDS = {"symbol", "local_symbol", "forward_label", "backward_label"}
BINDING_KINDS = {"label", "constant", "procedure", "variable", "enum_member"}
BYTE_MODES = {"immediate", "zeropage", "zeropage_x", "zeropage_y",
              "preindexed_indirect", "postindexed_indirect"}
WORD_MODES = {"absolute", "absolute_x", "absolute_y", "indirect"}


def require(condition, message):
    if not condition:
        raise ValueError("invalid instruction records: " + message)


def one_of(value, allowed):
    """Set membership that refuses JSON lists and objects instead of raising TypeError."""
    return isinstance(value, str) and value in allowed


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
    require(isinstance(value, dict) and one_of(value.get("kind"), KINDS), "unknown expression kind")
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
        require(one_of(value.get("operator"), OPERATORS), "unknown expression operator")
        unary = value["operator"] in {"bit_not", "logical_not", "low_byte", "high_byte", "negate", "bank"}
        require(len(children) == (1 if unary else 2), "invalid operator arity")
    for child in children:
        expression(child, check_source)


def memory_access(record):
    """Checks the shape of memory_access and its consistency with mode and operand value.

    Which mnemonics read or write is xasm's fact; it is not re-derived here.
    """
    access = record.get("memory_access", ...)
    require(access is not ..., "missing memory_access")
    mode, value = record["addressing_mode"], record["operand_value"]
    if access is None:
        require(mode not in POINTER_MODES, "pointer mode without memory_access")
        return
    require(mode in MEMORY_MODES | POINTER_MODES, "memory_access on a mode without a memory operand")
    require(type(value) is int, "memory_access requires an operand value")
    require(isinstance(access, dict) and set(access) == {"data", "pointer"}, "invalid memory_access")
    pointer_mode = mode in {"preindexed_indirect", "postindexed_indirect"}
    data = access["data"]
    if data is not None:
        require(isinstance(data, dict) and one_of(data.get("kind"), DATA_KINDS), "invalid data access kind")
        require(data.get("via_pointer") is pointer_mode, "data via_pointer/mode mismatch")
        require(data.get("address") == (None if pointer_mode else value), "data address must be the operand value")
        require(data.get("index_register") == DATA_INDEX.get(mode), "data index/mode mismatch")
    pointer = access["pointer"]
    require((pointer is not None) == (mode in POINTER_MODES), "pointer/mode mismatch")
    if pointer is not None:
        high = (value & 0xFF00) | ((value + 1) & 0xFF) if mode == "indirect" else (value + 1) & 0xFF
        require(isinstance(pointer, dict) and pointer.get("address") == value
                and pointer.get("high_byte_address") == high
                and pointer.get("index_register") == ("X" if mode == "preindexed_indirect" else None),
                "invalid pointer access")
    require((data is None) == (mode == "indirect"), "data access/mode mismatch")


def truncated_operand(value, mode):
    """xasm truncates an operand that is a constant after translation."""
    if mode in BYTE_MODES:
        return value if -128 <= value <= 255 else value & 0xFF
    if mode in WORD_MODES:
        return value & 0xFFFF if value < 0 or value >= 0x10000 else value
    return value


def additive_terms(record, check_source=None):
    terms = record.get("additive_terms", ...)
    require(terms is not ..., "missing additive_terms")
    if record["expression"] is None:
        require(terms is None, "additive terms for an operandless record")
        return
    require(isinstance(terms, dict) and one_of(terms.get("projection"), {"none", "low", "high"}),
            "invalid additive terms projection")
    items = terms.get("terms")
    require(isinstance(items, list) and items, "additive terms required")
    total = 0
    for term in items:
        require(isinstance(term, dict) and type(term.get("sign")) is int and term["sign"] in (1, -1)
                and one_of(term.get("kind"), TERM_KINDS) and type(term.get("value")) is int,
                "invalid additive term")
        kind = term["kind"]
        require(isinstance(term.get("name"), str) if kind in NAMED_TERM_KINDS else "name" not in term,
                "invalid term name")
        symbols = term.get("referenced_symbols")
        require(isinstance(symbols, list) and all(isinstance(name, str) for name in symbols)
                if kind == "expression" else "referenced_symbols" not in term, "invalid term symbols")
        require(("binding" in term) == (kind in NAMED_TERM_KINDS), "binding presence/kind mismatch")
        binding = term.get("binding")
        if binding is not None:
            require(kind in {"symbol", "local_symbol"} and isinstance(binding, dict)
                    and one_of(binding.get("kind"), BINDING_KINDS) and "definition" in binding,
                    "invalid term binding")
            if binding["definition"] is not None:
                span(binding["definition"], check_source)
            require(isinstance(binding.get("enum"), str) if binding["kind"] == "enum_member"
                    else "enum" not in binding, "invalid enum binding")
        source(term.get("source"), check_source)
        total += term["sign"] * term["value"]
    if terms["projection"] == "low":
        total &= 0xFF
    elif terms["projection"] == "high":
        total = (total >> 8) & 0xFF
    value = record["operand_value"]
    require(value in (total, truncated_operand(total, record["addressing_mode"])),
            "additive terms do not add up to the operand value")


def validate(payload, check_source=None):
    require(isinstance(payload, dict) and payload.get("version") == "2", "version 2 required")
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
        require(one_of(record.get("addressing_mode"), MODES) and one_of(record.get("parsed_addressing_mode"), MODES),
                "unknown addressing mode")
        require(type(record.get("immediate")) is bool, "immediate boolean required")
        require("index_register" in record and record["index_register"] in (None, "X", "Y"),
                "invalid index register")
        require(isinstance(record.get("mnemonic"), str) and record["mnemonic"], "mnemonic required")
        require(one_of(record.get("operand_form"), {"integer_literal", "symbol", "expression", "none"}),
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
                    and type(base.get("displacement")) is int and one_of(base.get("projection"), {"none", "low", "high"}),
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
        memory_access(record)
        additive_terms(record, check_source)
    return records


def check_binary(payload, binary):
    for record in payload["records"]:
        start = record["output_offset"]
        require(binary[start:start + record["size"]] == bytes(record["bytes"]), "instruction bytes differ from output")
