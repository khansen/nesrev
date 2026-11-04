"""Closed wire-shape validation for the pinned source-model schema.

This implements only the vocabulary used by that schema and refuses any other
vocabulary. It does not infer assembler facts or evaluate expressions.
Adapted from XORcyst's schema vocabulary checker (GPL-2.0-or-later).
"""
import base64
import re


def check(value, schema, root=None, path="$", vocabulary=False):
    root = schema if root is None else root
    allowed = {"$schema", "$id", "$defs", "$ref", "title", "description", "type", "const", "enum",
               "properties", "required", "additionalProperties", "items", "maxItems", "minimum", "maximum",
               "pattern", "contentEncoding", "anyOf", "oneOf", "allOf", "if", "then", "else"}
    if set(schema) - allowed:
        raise ValueError("unimplemented schema vocabulary: " + str(set(schema) - allowed))

    def require(condition):
        if not condition:
            raise ValueError("MODEL_SCHEMA: " + path)

    def accepts(part):
        try:
            check(value, part, root, path)
        except ValueError:
            return False
        return True

    if "$ref" in schema:
        require(schema["$ref"].startswith("#/$defs/"))
        check(value, root["$defs"][schema["$ref"].split("/")[-1]], root, path)
    if "type" in schema:
        require({"null": value is None, "object": isinstance(value, dict), "array": isinstance(value, list),
                 "string": isinstance(value, str), "integer": type(value) is int,
                 "boolean": type(value) is bool}[schema["type"]])
    if "const" in schema:
        require(value == schema["const"])
    if "enum" in schema:
        require(value in schema["enum"])
    if isinstance(value, dict):
        require(set(schema.get("required", ())) <= set(value))
        if schema.get("additionalProperties") is False:
            require(set(value) <= set(schema.get("properties", {})))
        for key, part in schema.get("properties", {}).items():
            if key in value:
                check(value[key], part, root, path + "." + key)
    if isinstance(value, list):
        if "maxItems" in schema:
            require(len(value) <= schema["maxItems"])
        if "items" in schema:
            for at, item in enumerate(value):
                check(item, schema["items"], root, path + "[" + str(at) + "]")
    if type(value) is int:
        if "minimum" in schema:
            require(value >= schema["minimum"])
        if "maximum" in schema:
            require(value <= schema["maximum"])
    if isinstance(value, str):
        if "pattern" in schema:
            require(re.search(schema["pattern"], value) is not None)
        if schema.get("contentEncoding") == "base64":
            base64.b64decode(value, validate=True)
    if "allOf" in schema:
        for part in schema["allOf"]:
            check(value, part, root, path)
    if "anyOf" in schema:
        require(any(accepts(part) for part in schema["anyOf"]))
    if "oneOf" in schema:
        require(sum(accepts(part) for part in schema["oneOf"]) == 1)
    if "if" in schema:
        check(value, schema.get("then" if accepts(schema["if"]) else "else", {}), root, path)
