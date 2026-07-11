--[[ =====================================================================
  MM2 COIN & PLAYER MONITOR  (data logger for reverse-engineering)
  ---------------------------------------------------------------------
  Цель: собрать ПОЛНУЮ картину происходящего с монетами и
  игроками, чтобы сопоставить координаты игроков с сбором/
  изменением свойств монет. Всё пишется в файл JSONL
  (одно JSON-событие на строку) для последующего анализа.

  Типы событий (поле ev):
    header       — метаданные сессии (время, игра, лок. игрок)
    container_bound — найден/привязан контейнер монет (начало раунда)
    coin_spawn   — появление монеты + полное описание + ближайшие
    coin_prop    — изменение Transparency части монеты (сигнал сбора!)
    coin_touch   — физическое касание (кто задел)
    coin_removed — удаление монеты + время жизни + ближайшие
    players      — периодический снимок всех игроков (коорд/скорость/HP)
    coins        — периодический снимок всех монет (коорд + прозрачности)
    stop         — завершение + итоги
  =================================================================== ]]

local Players     = game:GetService("Players")
local RunService  = game:GetService("RunService")
local Workspace   = game:GetService("Workspace")
local HttpService = game:GetService("HttpService")
local UIS         = game:GetService("UserInputService")
local LP = Players.LocalPlayer

----------------------------- КОНФИГ -----------------------------
local CFG = {
	sampleHz       = 15,    -- частота снимков сетки (игроки+монеты) в секунду
	flushEverySec  = 2,     -- как часто сбрасывать буфер в файл
	nearestK       = 4,     -- сколько ближайших игроков логировать на событие монеты
	logPlayers     = true,  -- писать периодические снимки игроков
	logCoins       = true,  -- писать периодические снимки монет
	maxFileMB      = 45,    -- защитный предел размера файла
}
local FILE = "MM2_monitor_" .. tostring(os.time()) .. ".jsonl"

------------------------- ФАЙЛОВЫЙ ВВОД/ВЫВОД -------------------------
local hasWrite  = type(writefile)  == "function"
local hasAppend = type(appendfile) == "function"
local buffer, bufN, totalBytes, partIx = {}, 0, 0, 0
local running = true

local function encode(t)
	local ok, s = pcall(function() return HttpService:JSONEncode(t) end)
	return ok and s or nil
end

local START_CLOCK = os.clock()
local function nowT() return math.floor((os.clock() - START_CLOCK) * 1000) / 1000 end

local function push(ev)
	ev.t = nowT()
	local s = encode(ev)
	if not s then return end
	buffer[#buffer + 1] = s
	bufN = bufN + #s + 1
end

local function flush()
	if #buffer == 0 then return end
	if totalBytes / 1048576 >= CFG.maxFileMB then buffer = {}; bufN = 0; return end
	local data = table.concat(buffer, "\n") .. "\n"
	local wrote = bufN
	buffer = {}; bufN = 0
	pcall(function()
		if hasAppend then
			appendfile(FILE, data)
		elseif hasWrite then
			-- без appendfile: пишем частями, чтобы не раздувать память
			partIx = partIx + 1
			writefile("MM2_monitor_part" .. partIx .. ".jsonl", data)
		end
	end)
	totalBytes = totalBytes + wrote
end

------------------------------- ХЕЛПЕРЫ -------------------------------
local function rnd(n) return math.floor(n * 100 + 0.5) / 100 end
local function v3(p) return { rnd(p.X), rnd(p.Y), rnd(p.Z) } end

local function hrpOf(pl)
	local ch = pl.Character
	if not ch then return nil, nil end
	return ch:FindFirstChild("HumanoidRootPart"), ch:FindFirstChildOfClass("Humanoid")
end

-- полный снимок всех игроков
local function playerList()
	local out = {}
	for _, pl in ipairs(Players:GetPlayers()) do
		local hrp, hum = hrpOf(pl)
		out[#out + 1] = {
			name = pl.Name, uid = pl.UserId,
			pos  = hrp and v3(hrp.Position) or nil,
			vel  = hrp and v3(hrp.AssemblyLinearVelocity) or nil,
			hp   = hum and rnd(hum.Health) or nil,
			alive = (hum ~= nil and hum.Health > 0) or false,
		}
	end
	return out
end

-- K ближайших игроков к точке (с дистанциями) — для сопоставления «кто собрал»
local function nearest(pos, k)
	local arr = {}
	for _, pl in ipairs(Players:GetPlayers()) do
		local hrp = hrpOf(pl)
		if hrp then
			arr[#arr + 1] = { name = pl.Name, uid = pl.UserId, d = rnd((hrp.Position - pos).Magnitude), pos = v3(hrp.Position) }
		end
	end
	table.sort(arr, function(a, b) return a.d < b.d end)
	local out = {}
	for i = 1, math.min(k or 3, #arr) do out[i] = arr[i] end
	return out
end

----------------------------- МОНЕТЫ -----------------------------
local coinSeq = 0
local coins = {}            -- [inst] = { id, spawnT, conns = {} }
local registerCoin, unregisterCoin

local function describeCoin(coin)
	local d = { name = coin.Name, class = coin.ClassName }
	if coin:IsA("BasePart") then
		d.pos = v3(coin.Position); d.size = v3(coin.Size)
		d.transp = coin.Transparency; d.canTouch = coin.CanTouch
	end
	local parts = {}
	for _, ds in ipairs(coin:GetDescendants()) do
		if ds:IsA("BasePart") then parts[ds.Name] = ds.Transparency end
	end
	d.parts = parts
	local attrs = {}
	for k, v in pairs(coin:GetAttributes()) do
		local tv = typeof(v)
		if tv == "number" or tv == "string" or tv == "boolean" then attrs[k] = v else attrs[k] = tostring(v) end
	end
	if next(attrs) then d.attrs = attrs end
	return d
end

registerCoin = function(coin)
	if coins[coin] then return end
	if not coin:IsA("BasePart") then return end
	if coin.Name ~= "Coin_Server" then return end
	coinSeq = coinSeq + 1
	local id = coinSeq
	local rec = { id = id, spawnT = nowT(), conns = {} }
	coins[coin] = rec
	push({ ev = "coin_spawn", id = id, coin = describeCoin(coin), near = nearest(coin.Position, CFG.nearestK) })

	local function keep(c) if c then rec.conns[#rec.conns + 1] = c end end
	-- следим за Transparency ключевых частей (MainCoin 0->1 = надёжный сигнал сбора)
	local function bindTransp(part, tag)
		if not part or not part:IsA("BasePart") then return end
		local ok, conn = pcall(function()
			return part:GetPropertyChangedSignal("Transparency"):Connect(function()
				local p = coin:IsA("BasePart") and coin.Position or part.Position
				push({ ev = "coin_prop", id = id, part = tag, prop = "Transparency",
				       val = part.Transparency, coinPos = v3(p), near = nearest(p, CFG.nearestK) })
			end)
		end)
		if ok then keep(conn) end
	end
	bindTransp(coin:FindFirstChild("MainCoin"), "MainCoin")
	bindTransp(coin:FindFirstChild("CoinVisual"), "CoinVisual")
	bindTransp(coin, "Coin_Server")
	-- поздно добавленные части (MainCoin/CoinVisual могут прийти после Coin_Server)
	local ok1, c1 = pcall(function()
		return coin.ChildAdded:Connect(function(ch)
			if ch.Name == "MainCoin" or ch.Name == "CoinVisual" then bindTransp(ch, ch.Name) end
		end)
	end)
	if ok1 then keep(c1) end
	-- физическое касание
	local ok2, c2 = pcall(function()
		return coin.Touched:Connect(function(hit)
			local pl = hit and hit.Parent and Players:GetPlayerFromCharacter(hit.Parent)
			push({ ev = "coin_touch", id = id, by = pl and pl.Name or (hit and hit.Name),
			       coinPos = coin:IsA("BasePart") and v3(coin.Position) or nil })
		end)
	end)
	if ok2 then keep(c2) end
	-- уничтожение/вынос из иерархии
	local ok3, c3 = pcall(function()
		return coin.AncestryChanged:Connect(function(_, parent)
			if not parent then unregisterCoin(coin, "ancestry") end
		end)
	end)
	if ok3 then keep(c3) end
end

unregisterCoin = function(coin, reason)
	local rec = coins[coin]
	if not rec then return end
	coins[coin] = nil
	for _, c in ipairs(rec.conns) do pcall(function() c:Disconnect() end) end
	local pos
	pcall(function() if coin:IsA("BasePart") then pos = coin.Position end end)
	push({ ev = "coin_removed", id = rec.id, reason = reason,
	       life = rnd(nowT() - rec.spawnT),
	       coinPos = pos and v3(pos) or nil,
	       near = pos and nearest(pos, CFG.nearestK) or nil })
end

--------------------- ПРИВЯЗКА КОНТЕЙНЕРОВ ---------------------
local bound = {}
local masterConns = {}
local function keepM(c) if c then masterConns[#masterConns + 1] = c end end

local function bindContainer(cc)
	if bound[cc] then return end
	bound[cc] = true
	push({ ev = "container_bound", path = cc:GetFullName() })
	for _, ch in ipairs(cc:GetChildren()) do task.defer(registerCoin, ch) end
	keepM(cc.ChildAdded:Connect(function(ch) task.defer(registerCoin, ch) end))
	keepM(cc.ChildRemoved:Connect(function(ch) if coins[ch] then unregisterCoin(ch, "removed") end end))
end

local function scanContainers()
	for _, child in ipairs(Workspace:GetChildren()) do
		local cc = child:FindFirstChild("CoinContainer")
		if cc then bindContainer(cc) end
	end
end

-- новая карта/раунд — пересканировать
keepM(Workspace.ChildAdded:Connect(function() task.defer(scanContainers) end))
scanContainers()

----------------------------- СНИМКИ СЕТКИ -----------------------------
local acc, sampleDT = 0, 1 / CFG.sampleHz
keepM(RunService.Heartbeat:Connect(function(dt)
	acc = acc + dt
	if acc < sampleDT then return end
	acc = 0
	if CFG.logPlayers then push({ ev = "players", list = playerList() }) end
	if CFG.logCoins then
		local snap = {}
		for coin, rec in pairs(coins) do
			if coin and coin.Parent then
				local e = { id = rec.id }
				pcall(function()
					e.pos = v3(coin.Position)
					local mc = coin:FindFirstChild("MainCoin");  if mc then e.mt = mc.Transparency end
					local cv = coin:FindFirstChild("CoinVisual"); if cv then e.ct = cv.Transparency end
				end)
				snap[#snap + 1] = e
			end
		end
		if #snap > 0 then push({ ev = "coins", list = snap }) end
	end
end))

------------------------------- СТАРТ -------------------------------
push({ ev = "header", unix = os.time(), placeId = game.PlaceId, jobId = game.JobId,
       localPlayer = LP and LP.Name, cfg = CFG, file = FILE })
if setclipboard then pcall(function() setclipboard(FILE) end) end

local function stopAll(reason)
	if not running then return end
	running = false
	push({ ev = "stop", reason = reason, coinsSeen = coinSeq, durSec = rnd(nowT()) })
	for _, c in ipairs(masterConns) do pcall(function() c:Disconnect() end) end
	for coin, rec in pairs(coins) do for _, c in ipairs(rec.conns) do pcall(function() c:Disconnect() end) end end
	flush()
end

-- периодический сброс в файл
task.spawn(function()
	while running do task.wait(CFG.flushEverySec); flush() end
end)

------------------------------- МИНИ-GUI -------------------------------
local sg = Instance.new("ScreenGui")
sg.Name = "MM2Monitor"; sg.ResetOnSpawn = false; sg.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
pcall(function() sg.Parent = game:GetService("CoreGui") end)
if not sg.Parent then sg.Parent = LP:WaitForChild("PlayerGui") end

local fr = Instance.new("Frame"); fr.Size = UDim2.new(0, 240, 0, 96)
fr.Position = UDim2.new(0, 16, 0, 120); fr.BackgroundColor3 = Color3.fromRGB(18, 18, 22)
fr.BorderSizePixel = 0; fr.Parent = sg
Instance.new("UICorner", fr).CornerRadius = UDim.new(0, 8)

local lbl = Instance.new("TextLabel"); lbl.Size = UDim2.new(1, -16, 1, -44)
lbl.Position = UDim2.new(0, 8, 0, 6); lbl.BackgroundTransparency = 1
lbl.TextColor3 = Color3.fromRGB(220, 220, 220); lbl.Font = Enum.Font.Code
lbl.TextSize = 12; lbl.TextXAlignment = Enum.TextXAlignment.Left
lbl.TextYAlignment = Enum.TextYAlignment.Top; lbl.Text = "MM2 Monitor\nзапуск..."; lbl.Parent = fr

local btn = Instance.new("TextButton"); btn.Size = UDim2.new(1, -16, 0, 28)
btn.Position = UDim2.new(0, 8, 1, -34); btn.BackgroundColor3 = Color3.fromRGB(120, 40, 40)
btn.BorderSizePixel = 0; btn.Text = "STOP + SAVE"; btn.TextColor3 = Color3.fromRGB(255, 235, 235)
btn.Font = Enum.Font.GothamBold; btn.TextSize = 13; btn.Parent = fr
Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 6)
btn.MouseButton1Click:Connect(function()
	stopAll("button"); lbl.Text = "СОХРАНЕНО:\n" .. FILE; btn.Text = "DONE"; btn.BackgroundColor3 = Color3.fromRGB(40, 100, 40)
end)

-- обновление статуса
task.spawn(function()
	while running do
		local live = 0; for _ in pairs(coins) do live = live + 1 end
		lbl.Text = string.format("MM2 Monitor  %.0fs\nмонет всего: %d  сейчас: %d\nзаписано: %.2f MB\nфайл: %s",
			nowT(), coinSeq, live, totalBytes / 1048576, FILE)
		task.wait(0.5)
	end
end)

-- стоп при выходе из игры
pcall(function() game:BindToClose(function() stopAll("bindToClose") end) end)

return { stop = function() stopAll("api") end, file = FILE }
