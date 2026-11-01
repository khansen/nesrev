#!/usr/bin/env python3
"""Private launcher entry point; settings and role are operator-owned."""
import sys
from structured_pass.bridge import hook,mcp

if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--hook':hook(sys.argv[2])
    elif len(sys.argv)==5 and sys.argv[1]=='--mcp':mcp(*sys.argv[2:])
    else:raise SystemExit('Usage: structured_pass_bridge.py --hook POLICY | --mcp SESSION ROLE PROFILE')
