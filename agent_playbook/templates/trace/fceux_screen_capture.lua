-- Template: FCEUX screen capture for visual identity evidence.
-- Copy into projects/<slug>/tools/trace/, prepend a `watch` table of
-- symbol-backed addresses from a parity-checked listing, and replace SCENARIO.
-- Each capture() writes <name>.gd (convert with scripts/nes_graphics.py gd2png)
-- and one JSONL milestone holding the four nametable views, the palette, the
-- PPUCTRL shadow and the context bytes named in CONTEXT.

local rb, wb = memory.readbyte, memory.writebyte
local log = assert(io.open(assert(os.getenv('TRACE_OUT'), 'use the supervised capture runner'), 'w'))
local out = assert(os.getenv('TRACE_DIR'), 'use the supervised capture runner')
local limit = assert(tonumber(os.getenv('TRACE_MAX_FRAMES')), 'missing frame limit')
local frame = 0

-- Set true for CHR-RAM games so captures can be rendered without CHR ROM.
local DUMP_PATTERN_TABLES = false
-- Bytes rewritten every frame to reach later screens (for example holding a
-- lives or miss counter). Record every entry in the trace plan; never pin a
-- byte the question itself measures.
local HOLD = {}
-- Context bytes recorded with each capture: { name = address }.
local CONTEXT = {}

local function emit(event, fields)
    log:write('{"event":"' .. event .. '","frame":' .. frame .. (fields or '') .. '}\n')
    log:flush()
end

local function finish(reason)
    emit('done', ',"reason":"' .. reason .. '"')
    log:close()
    emu.exit()
end

local function step(buttons)
    joypad.set(1, buttons or {})
    for address, value in pairs(HOLD) do wb(address, value) end
    emu.frameadvance()
    frame = frame + 1
    if frame > limit then finish('max_frames') end
end

local function wait_until(test, budget, what)
    for _ = 1, budget do
        if test() then return end
        step()
    end
    emit('error', ',"waiting_for":"' .. what .. '"')
    finish('stalled')
end

local function press(button, frames, release)
    for _ = 1, frames do step({ [button] = true }) end
    for _ = 1, release or 12 do step() end
end

local function hex(read, base, count)
    local t = {}
    for i = 0, count - 1 do t[#t + 1] = string.format('%02X', read(base + i)) end
    return table.concat(t)
end

local function capture(name, ppuctrl_shadow)
    local f = assert(io.open(out .. '/' .. name .. '.gd', 'wb'))
    f:write(gui.gdscreenshot())
    f:close()
    local fields = ',"name":"' .. name .. '"'
    if ppuctrl_shadow then fields = fields .. ',"ppuctrl":' .. rb(ppuctrl_shadow) end
    for key, address in pairs(CONTEXT) do fields = fields .. ',"' .. key .. '":' .. rb(address) end
    for index = 0, 3 do
        fields = fields .. ',"nt' .. index .. '":"' .. hex(ppu.readbyte, 0x2000 + index * 0x400, 0x400) .. '"'
    end
    fields = fields .. ',"palette":"' .. hex(ppu.readbyte, 0x3F00, 32) .. '"'
    if DUMP_PATTERN_TABLES then
        fields = fields .. ',"chr":"' .. hex(ppu.readbyte, 0x0000, 0x2000) .. '"'
    end
    emit('milestone', fields)
end

emit('start', ',"scenario":"screens"')
emu.frameadvance()
if movie.active() then movie.stop() end
emu.speedmode('maximum')
emu.poweron()

-- SCENARIO: replace with predicates on symbol-backed watches and one capture()
-- per screen, then declare the same names with the runner's
-- --require-milestone options. The unmodified template stops with 'stalled'.
wait_until(function() return false end, 60, 'replace the template scenario')
capture('first_screen')
finish('scenario_complete')
