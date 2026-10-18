# Source this file before launching a NESrev agent session or capture command.
_nesrev_fceux_root="${NESREV_FCEUX_ROOT:-${XDG_DATA_HOME:-$HOME/.local/share}/nesrev/fceux}"
if ! _nesrev_fceux_root=$(CDPATH= cd -P "$_nesrev_fceux_root" && pwd -P) ||
   [ ! -d "$_nesrev_fceux_root/config" ] ||
   ! _nesrev_fceux_release=$(CDPATH= cd -P "$_nesrev_fceux_root/current" && pwd -P) ||
   ! (cd "$_nesrev_fceux_release" &&
      grep -Eq '^[[:xdigit:]]{64} [ *]bin/fceux$' SHA256SUMS &&
      grep -Eq '^[[:xdigit:]]{64} [ *]bin/tmux-local-fceux$' SHA256SUMS &&
      shasum -a 256 -c --quiet SHA256SUMS) >&2; then
    echo "Local FCEUX is missing or changed; check scripts/patches/fceux/LOCAL_BUILD.md." >&2
    unset _nesrev_fceux_root _nesrev_fceux_release
    return 1
fi
export FCEUX_BIN="$_nesrev_fceux_release/bin/fceux"
export FCEUX_CONFIG_DIR="$_nesrev_fceux_root/config"
export LUA_PATH="$_nesrev_fceux_release/share/luaScripts/?.lua;${LUA_PATH:-;}"
export AGENT_REVIEW_TMUX_BIN="$_nesrev_fceux_release/bin/tmux-local-fceux"
unset _nesrev_fceux_root _nesrev_fceux_release
