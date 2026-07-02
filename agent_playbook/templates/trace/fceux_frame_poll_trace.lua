-- Template: FCEUX frame-poll trace logger.
-- Copy into projects/<slug>/tools/trace/ and replace WATCHES plus milestones.
-- This backend intentionally avoids write callbacks; use Mesen for writer-PC.

local function script_dir()
  local src = (debug.getinfo(1, 'S').source or ''):gsub('^@', '')
  return src:match('^(.*)[/\\][^/\\]+$') or '.'
end

local function default_out()
  local proj = script_dir():gsub('[/\\]tools[/\\]trace$', '')
  return proj .. '/tmp/traces/trace.log'
end

local out_path = os.getenv('TRACE_OUT') or default_out()
local max_frames = tonumber(os.getenv('TRACE_MAX_FRAMES') or '36000')

os.execute('mkdir -p "' .. (out_path:match('^(.*)[/\\][^/\\]+$') or '.') .. '"')

local function rb(addr) return memory.readbyte(addr) end
local function hex2(v) return string.format('%02X', v % 0x100) end
local function hex4(v) return string.format('%04X', v % 0x10000) end

-- Replace with the smallest watch list that proves the scenario.
local WATCHES = {
  { id = 'state0', addr = 0x0000 },
  { id = 'mode',   addr = 0x0000 },
}

-- Add context bytes that let the analyzer reject wrong scenarios.
local CONTEXT = {
  scenario = 0x0000,
  result   = 0x0000,
}

local fh, err = io.open(out_path, 'w')
if not fh then
  local msg = 'TRACE OPEN FAILED: ' .. out_path .. ' (' .. tostring(err) .. ')'
  print(msg)
  if emu.message then emu.message(msg) end
  return
end

local function log(event, payload)
  fh:write(string.format('{"frame":%d,"event":"%s",%s}\n', emu.framecount(), event, payload))
end

local function context_payload()
  local parts = {}
  for name, addr in pairs(CONTEXT) do
    table.insert(parts, string.format('"%s":"%s"', name, hex2(rb(addr))))
  end
  return table.concat(parts, ',')
end

log('start', string.format('"max_frames":%d', max_frames))
if emu.message then emu.message('tracing -> ' .. out_path) end

local prev = {}
for _, watch in ipairs(WATCHES) do
  prev[watch.id] = rb(watch.addr)
end

local seen = {}
local function milestone(name)
  if seen[name] then return end
  seen[name] = true
  log('milestone', string.format('"name":"%s"', name))
end

local frames = 0
local finished = false

local function finish(reason)
  if finished then return end
  finished = true
  log('done', string.format('"final_frame":%d,"reason":"%s"', emu.framecount(), reason))
  if fh then fh:flush(); fh:close(); fh = nil end
end

local function check_milestones()
  -- TODO: replace with project-specific predicates, for example:
  -- if rb(CONTEXT.scenario) ~= 0 then milestone('scenario_started') end
  -- if rb(CONTEXT.result) ~= 0 then milestone('result_resolved') end
end

local function on_frame()
  if finished then return end
  frames = frames + 1
  check_milestones()

  for _, watch in ipairs(WATCHES) do
    local value = rb(watch.addr)
    if value ~= prev[watch.id] then
      local ctx = context_payload()
      if ctx ~= '' then ctx = ',' .. ctx end
      log('watch', string.format(
        '"id":"%s","addr":"%s","old":"%s","new":"%s"%s',
        watch.id, hex4(watch.addr), hex2(prev[watch.id]), hex2(value), ctx))
      prev[watch.id] = value
    end
  end

  if frames % 600 == 0 and fh then fh:flush() end
  if frames >= max_frames then
    finish('max_frames')
    if emu.exit then emu.exit() elseif emu.quit then emu.quit() end
  end
end

emu.registerafter(on_frame)
emu.registerexit(function() finish('exit') end)
