local Gc = {}

local Object = {
    TagByte = 1,
    SizeLogByte = 7,
    TableTag = 7,
    ThreadTag = 10,
    ThreadGlobalOffset = 80,
}

local Page = {
    LinkOffset = 8,
    SizeOffset = 32,
    BlockSizeOffset = 36,
    BusyBlocksOffset = 52,
    DataOffset = 64,
    GlobalScanSpan = 0x800,
    MaxPages = 50000,
    SamplesPerPage = 4,
}

local Discovery = {
    Depth = 4,
    Nodes = 6000,
    Span = 0x100,
    MaxCandidates = 6,
    VerifyBudgetMs = 1500,
}

local Defaults = {
    LockIntervalMs = 15,
    LockRefindMs = 5000,
}

local YieldEvery = 2000

local SizeCache = {}

local function readInt(Addr, Kind)
    Addr = math.tointeger(Addr)
    if not Addr or Addr < 0x10000 or Addr > 0x7FFFFFFFFFFF then
        return nil
    end
    local Ok, Value = pcall(memory.read, Addr, Kind)
    if Ok then
        return math.tointeger(Value)
    end
    return nil
end

local function isPointer(Value)
    return Value ~= nil and Value > 0x100000 and Value < 0x7FF000000000 and Value % 8 == 0
end

local function isValidInstance(Inst)
    return Inst ~= nil and Inst ~= nil_instance and Inst:isvalid()
end

local function differs(A, B)
    if type(A) == "number" and type(B) == "number" then
        return math.abs(A - B) > 1e-6
    end
    return A ~= B
end

local function readSnapshot(Address)
    local Ok, Snapshot = pcall(gc.read_table, Address)
    if Ok and type(Snapshot) == "table" then
        return Snapshot
    end
    return nil
end

local function blockHeader(Pos)
    local Value = readInt(Pos, MEMORY_TYPE.int64)
    if not Value then
        return nil, nil
    end
    return (Value >> (Object.TagByte * 8)) & 0xFF, (Value >> (Object.SizeLogByte * 8)) & 0xFF
end

local function pageInfo(PageAddress)
    local Size = readInt(PageAddress + Page.SizeOffset, MEMORY_TYPE.int32)
    local Block = readInt(PageAddress + Page.BlockSizeOffset, MEMORY_TYPE.int32)
    local Busy = readInt(PageAddress + Page.BusyBlocksOffset, MEMORY_TYPE.int32)
    if not (Size and Block and Busy) or Size < 512 or Size > 0x400000 or Block < 8 then
        return nil
    end
    local Capacity = (Size - Page.DataOffset) // Block
    if Capacity < 1 or Busy < 0 or Busy > Capacity then
        return nil
    end
    return Size, Block, Capacity
end

local function toSet(List)
    if not List then
        return nil
    end
    local Set = {}
    for _, Value in ipairs(List) do
        Set[Value] = true
    end
    return Set
end

local function compileQuery(Query)
    if type(Query) == "function" then
        return Query, nil
    end
    if type(Query) == "string" then
        Query = {Query}
    end
    local Required, Equals = {}, {}
    for Key, Value in pairs(Query) do
        if type(Key) == "number" then
            table.insert(Required, Value)
        else
            Equals[Key] = Value
        end
    end
    local IdParts = {}
    for _, Key in ipairs(Required) do
        table.insert(IdParts, tostring(Key))
    end
    for Key, Value in pairs(Equals) do
        table.insert(IdParts, tostring(Key) .. "=" .. tostring(Value))
    end
    table.sort(IdParts)
    local function matches(Snapshot)
        for _, Key in ipairs(Required) do
            if Snapshot[Key] == nil then
                return false
            end
        end
        for Key, Value in pairs(Equals) do
            if Snapshot[Key] ~= Value then
                return false
            end
        end
        return true
    end
    return matches, table.concat(IdParts, ",")
end

local Heap = {}
Heap.__index = Heap

function Heap.new(Global)
    return setmetatable({Global = Global, TableBlockSize = nil}, Heap)
end

function Heap:pages()
    local Pages, Seen = {}, {}
    for Offset = 0, Page.GlobalScanSpan - 8, 8 do
        local Current = readInt(self.Global + Offset, MEMORY_TYPE.int64)
        while isPointer(Current) and not Seen[Current] and #Pages < Page.MaxPages and pageInfo(Current) do
            Seen[Current] = true
            table.insert(Pages, Current)
            Current = readInt(Current + Page.LinkOffset, MEMORY_TYPE.int64)
        end
    end
    return Pages
end

function Heap:calibrate()
    local Votes = {}
    for _, PageAddress in ipairs(self:pages()) do
        local Size, Block, Capacity = pageInfo(PageAddress)
        if Size then
            for Sample = 1, math.min(Page.SamplesPerPage, Capacity) do
                local Pos = PageAddress + Page.DataOffset + Block * (Capacity - Sample)
                if blockHeader(Pos) == Object.TableTag then
                    Votes[Block] = (Votes[Block] or 0) + 1
                end
            end
        end
    end
    local Best, BestVotes = nil, 0
    for Block, Count in pairs(Votes) do
        if Count > BestVotes then
            Best, BestVotes = Block, Count
        end
    end
    self.TableBlockSize = Best
    return Best ~= nil
end

function Heap:forEachTable(Visit, Sizes, Deadline)
    local Visited = 0
    for _, PageAddress in ipairs(self:pages()) do
        local Size, Block, Capacity = pageInfo(PageAddress)
        if Size and Block == self.TableBlockSize then
            local Pos = PageAddress + Page.DataOffset
            for _ = 1, Capacity do
                local Tag, SizeLog = blockHeader(Pos)
                if Tag == Object.TableTag and (not Sizes or Sizes[SizeLog]) and Visit(Pos, SizeLog) then
                    return true
                end
                Visited = Visited + 1
                if Visited % YieldEvery == 0 then
                    if Deadline and get_tickcount() > Deadline then
                        return false
                    end
                    wait(1)
                end
                Pos = Pos + Block
            end
        end
    end
    return false
end

local function defaultRoots()
    local Roots = {}
    local Player = game:get_service("Players").local_player
    if not isValidInstance(Player) then
        return Roots
    end
    local function add(Inst)
        if isValidInstance(Inst) then
            table.insert(Roots, Inst)
        end
    end
    local Character = Player.character
    local Backpack = Player:find_first_child("Backpack")
    local Scripts = Player:find_first_child("PlayerScripts")
    for _, Holder in ipairs({Character, Backpack, Scripts}) do
        if isValidInstance(Holder) then
            add(Holder)
            for _, Child in pairs(Holder:get_children()) do
                if Child.class_name == "Tool" or Child.class_name == "LocalScript" or Child.class_name == "Humanoid" then
                    add(Child)
                end
            end
        end
    end
    return Roots
end

function Gc.candidates(Roots)
    Roots = Roots or defaultRoots()
    local Queue, Head, Visited, Counts = {}, 1, {}, {}
    for _, Root in ipairs(Roots) do
        local Address = math.tointeger(Root.address)
        if Address and not Visited[Address] then
            table.insert(Queue, {Address, 0})
            Visited[Address] = true
        end
    end
    while Head <= #Queue and Head <= Discovery.Nodes do
        local Base, Depth = Queue[Head][1], Queue[Head][2]
        Head = Head + 1
        if Head % YieldEvery == 0 then
            wait(1)
        end
        for Offset = 0, Discovery.Span - 8, 8 do
            local Pointer = readInt(Base + Offset, MEMORY_TYPE.int64)
            if isPointer(Pointer) and not Visited[Pointer] then
                Visited[Pointer] = true
                if readInt(Pointer + Object.TagByte, MEMORY_TYPE.uint8) == Object.ThreadTag then
                    local Global = readInt(Pointer + Object.ThreadGlobalOffset, MEMORY_TYPE.int64)
                    if isPointer(Global) then
                        Counts[Global] = (Counts[Global] or 0) + 1
                    end
                end
                if Depth + 1 < Discovery.Depth then
                    table.insert(Queue, {Pointer, Depth + 1})
                end
            end
        end
    end
    local Ranked = {}
    for Global, Threads in pairs(Counts) do
        table.insert(Ranked, {Global = Global, Threads = Threads})
    end
    table.sort(Ranked, function(A, B) return A.Threads > B.Threads end)
    while #Ranked > Discovery.MaxCandidates do
        table.remove(Ranked)
    end
    return Ranked
end

local function ensureReader()
    local Ok, Layout = pcall(gc.layout)
    if not (Ok and type(Layout) == "table" and Layout.table_calibrated) then
        pcall(gc.diagnose)
    end
end

local function orderForDefault(Heaps)
    local Top = 0
    for _, Entry in ipairs(Heaps) do
        Top = math.max(Top, Entry.Threads)
    end
    table.sort(Heaps, function(A, B)
        local AClose, BClose = A.Threads >= Top / 2, B.Threads >= Top / 2
        if AClose ~= BClose then
            return AClose
        end
        if AClose then
            return A.Pages < B.Pages
        end
        return A.Threads > B.Threads
    end)
end

function Gc.attach(Options)
    Options = Options or {}
    ensureReader()
    local Candidates = {}
    if Options.Global then
        Candidates = {{Global = Options.Global, Threads = 1}}
    else
        Candidates = Gc.candidates(Options.Roots)
    end
    if #Candidates == 0 then
        return false, "no Luau threads found from the roots"
    end
    local Heaps = {}
    for _, Candidate in ipairs(Candidates) do
        local CandidateHeap = Heap.new(Candidate.Global)
        if CandidateHeap:calibrate() then
            table.insert(Heaps, {Heap = CandidateHeap, Threads = Candidate.Threads, Pages = #CandidateHeap:pages()})
        end
    end
    if not Options.Verify then
        orderForDefault(Heaps)
    end
    local Previous = Gc.Heap
    for _, Entry in ipairs(Heaps) do
        Gc.Heap = Entry.Heap
        if not Options.Verify or Options.Verify(Gc) then
            Gc.Options = Options
            return true, Entry.Heap.Global
        end
    end
    Gc.Heap = Previous
    return false, "no candidate VM passed"
end

function Gc.isAttached()
    return Gc.Heap ~= nil
end

function Gc.global()
    return Gc.Heap and Gc.Heap.Global
end

function Gc.ensure()
    if Gc.Heap and #Gc.Heap:pages() > 0 then
        return true
    end
    Gc.Heap = nil
    return Gc.attach(Gc.Options)
end

function Gc.sizeFor(KeyCount)
    local Log = 0
    while (1 << Log) < KeyCount do
        Log = Log + 1
    end
    return {Log, Log + 1}
end

local ProxyAddress = setmetatable({}, {__mode = "k"})
local ProxyMeta = {}

ProxyMeta.__index = function(Proxy, Key)
    local Snapshot = readSnapshot(ProxyAddress[Proxy])
    return Snapshot and Snapshot[Key]
end

ProxyMeta.__newindex = function(Proxy, Key, Value)
    if type(Key) ~= "string" then
        error("GcLib: only string keys can be written", 2)
    end
    local Ok, Err = pcall(gc.set, ProxyAddress[Proxy], Key, Value)
    if not Ok then
        error("GcLib: write failed: " .. tostring(Err), 2)
    end
end

ProxyMeta.__pairs = function(Proxy)
    return next, readSnapshot(ProxyAddress[Proxy]) or {}, nil
end

ProxyMeta.__tostring = function(Proxy)
    return string.format("GcTable: 0x%x", ProxyAddress[Proxy] or 0)
end

function Gc.wrap(Address)
    local Proxy = setmetatable({}, ProxyMeta)
    ProxyAddress[Proxy] = math.tointeger(Address)
    return Proxy
end

function Gc.isProxy(Value)
    return type(Value) == "table" and ProxyAddress[Value] ~= nil
end

function Gc.address(Proxy)
    return ProxyAddress[Proxy]
end

function Gc.snapshot(Proxy)
    return readSnapshot(ProxyAddress[Proxy])
end

function Gc.alive(Proxy, ExpectedKey)
    local Snapshot = readSnapshot(ProxyAddress[Proxy])
    return Snapshot ~= nil and (ExpectedKey == nil or Snapshot[ExpectedKey] ~= nil)
end

function Gc.update(Proxy, Fields)
    local Address = ProxyAddress[Proxy]
    local Written = 0
    for Key, Value in pairs(Fields) do
        if pcall(gc.set, Address, Key, Value) then
            Written = Written + 1
        end
    end
    return Written
end

local function collect(Matches, Sizes, Options)
    local Found, Seen = {}, {}
    local Deadline = Options.BudgetMs and get_tickcount() + Options.BudgetMs or nil
    Gc.Heap:forEachTable(function(Address, SizeLog)
        local Snapshot = readSnapshot(Address)
        if Snapshot and Matches(Snapshot) then
            table.insert(Found, Gc.wrap(Address))
            Seen[SizeLog] = true
            return Options.Limit ~= nil and #Found >= Options.Limit
        end
        return false
    end, Sizes, Deadline)
    return Found, Seen
end

local function hasMatch(Matches)
    return function()
        local Found = collect(Matches, nil, {Limit = 1, BudgetMs = Discovery.VerifyBudgetMs})
        return #Found > 0
    end
end

local function search(Query, Options)
    Options = Options or {}
    local Matches, Id = compileQuery(Query)
    if not Gc.Heap or #Gc.Heap:pages() == 0 then
        Gc.Heap = nil
        if not Gc.attach({Roots = Options.Roots, Verify = hasMatch(Matches)}) then
            return {}
        end
    end
    local Sizes = Options.Sizes and toSet(Options.Sizes) or (not Options.Exhaustive and Id and SizeCache[Id]) or nil
    local Found, Seen = collect(Matches, Sizes, Options)
    if #Found == 0 and Sizes and not Options.Sizes then
        Found, Seen = collect(Matches, nil, Options)
    end
    if #Found == 0 and not Options.Sizes then
        local Before = Gc.global()
        if Gc.attach({Roots = Options.Roots, Verify = hasMatch(Matches)}) and Gc.global() ~= Before then
            Found, Seen = collect(Matches, nil, Options)
        end
    end
    if Id and #Found > 0 and not Options.Limit then
        SizeCache[Id] = Seen
    end
    return Found
end

function Gc.find(Query, Options)
    return search(Query, Options)
end

function Gc.first(Query, Options)
    Options = Options or {}
    local Limited = {}
    for Key, Value in pairs(Options) do
        Limited[Key] = Value
    end
    Limited.Limit = 1
    return search(Query, Limited)[1]
end

function Gc.tables(Options)
    if not Gc.ensure() then
        return {}
    end
    return search(function()
        return true
    end, Options)
end

function Gc.forEachTable(Visit, Options)
    for _, Proxy in ipairs(Gc.tables(Options)) do
        if Visit(Proxy) == true then
            return true
        end
    end
    return false
end

function Gc.read(Query, Field, Options)
    local Values = {}
    for _, Proxy in ipairs(search(Query, Options)) do
        local Snapshot = readSnapshot(ProxyAddress[Proxy])
        if Snapshot then
            if Field then
                table.insert(Values, Snapshot[Field])
            else
                table.insert(Values, Snapshot)
            end
        end
    end
    return Values
end

function Gc.write(Query, Fields, Options)
    local Written = 0
    for _, Proxy in ipairs(search(Query, Options)) do
        local Address = ProxyAddress[Proxy]
        local Snapshot = readSnapshot(Address)
        if Snapshot then
            local Wanted = type(Fields) == "function" and Fields(Snapshot) or Fields
            for Key, Value in pairs(Wanted) do
                if differs(Snapshot[Key], Value) and pcall(gc.set, Address, Key, Value) then
                    Written = Written + 1
                end
            end
        end
    end
    return Written
end

local Lock = {}
Lock.__index = Lock

function Lock:stop(Restore)
    self.Running = false
    if not Restore then
        return
    end
    for Address, Saved in pairs(self.Originals) do
        local Snapshot = readSnapshot(Address)
        if Snapshot and self.Matches(Snapshot) then
            for Key, Value in pairs(Saved) do
                pcall(gc.set, Address, Key, Value)
            end
        end
    end
    self.Originals = {}
end

function Lock:count()
    return #self.Targets
end

function Lock:step()
    local Stale = false
    for _, Address in ipairs(self.Targets) do
        local Snapshot = readSnapshot(Address)
        if Snapshot and self.Matches(Snapshot) then
            local Wanted = type(self.Fields) == "function" and self.Fields(Snapshot) or self.Fields
            for Key, Value in pairs(Wanted) do
                if differs(Snapshot[Key], Value) then
                    local Saved = self.Originals[Address]
                    if not Saved then
                        Saved = {}
                        self.Originals[Address] = Saved
                    end
                    if Saved[Key] == nil then
                        Saved[Key] = Snapshot[Key]
                    end
                    if pcall(gc.set, Address, Key, Value) then
                        self.Writes = self.Writes + 1
                    end
                end
            end
        else
            Stale = true
        end
    end
    return not Stale
end

function Lock:refind()
    local Targets = {}
    for _, Proxy in ipairs(search(self.Query, self.Options)) do
        table.insert(Targets, ProxyAddress[Proxy])
    end
    self.Targets = Targets
    local Live = {}
    for _, Address in ipairs(Targets) do
        Live[Address] = true
    end
    for Address in pairs(self.Originals) do
        if not Live[Address] then
            self.Originals[Address] = nil
        end
    end
end

function Gc.lock(Query, Fields, Options)
    Options = Options or {}
    local Handle = setmetatable({
        Query = Query,
        Fields = Fields,
        Options = Options,
        Matches = compileQuery(Query),
        Targets = {},
        Originals = {},
        Writes = 0,
        Running = true,
    }, Lock)
    spawn(function()
        local LastFind = nil
        while Handle.Running do
            local Now = get_tickcount()
            if LastFind == nil or Now - LastFind >= (Options.RefindMs or Defaults.LockRefindMs) then
                LastFind = Now
                Handle:refind()
            end
            if not Handle:step() then
                LastFind = nil
            end
            wait(Options.IntervalMs or Defaults.LockIntervalMs)
        end
    end)
    return Handle
end

local NativeRawget = rawget

function Gc.getgc(IncludeTables)
    if not IncludeTables then
        return {}
    end
    return Gc.tables()
end

function Gc.rawget(Target, Key)
    if Gc.isProxy(Target) then
        local Snapshot = readSnapshot(ProxyAddress[Target])
        return Snapshot and Snapshot[Key]
    end
    return NativeRawget(Target, Key)
end

Gc.photonGetgc = getgc

function Gc.install()
    _G.getgc = Gc.getgc
    _G.rawget = Gc.rawget
end

function Gc.uninstall()
    _G.getgc = Gc.photonGetgc
    _G.rawget = NativeRawget
end

return Gc
