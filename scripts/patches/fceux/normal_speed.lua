local log = assert(io.open(assert(os.getenv("TRACE_OUT")), "w"))
local function emit(line)
    log:write(line .. "\n")
    log:flush()
end

emit("INITIALIZED paused=" .. tostring(emu.paused()))
emu.speedmode("normal")
for frame = 1, 120 do
    emu.frameadvance()
    emit("frame=" .. frame)
end
emit("COMPLETE")
log:close()
while true do emu.frameadvance() end
