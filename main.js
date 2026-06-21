const canvas = document.querySelector("#gameCanvas");
const ctx = canvas.getContext("2d");

const levelStatus = document.querySelector("#levelStatus");
const jumpStatus = document.querySelector("#jumpStatus");
const radarStatus = document.querySelector("#radarStatus");
const gunStatus = document.querySelector("#gunStatus");
const oniStatus = document.querySelector("#oniStatus");
const timer = document.querySelector("#timer");
const message = document.querySelector("#message");
const gameMenu = document.querySelector("#gameMenu");
const gameMenuText = document.querySelector("#gameMenuText");
const retryLevelButton = document.querySelector("#retryLevelButton");
const menuRestartButton = document.querySelector("#menuRestartButton");
const pauseButton = document.querySelector("#pauseButton");
const restartButton = document.querySelector("#restartButton");
const touchPad = document.querySelector("#touchPad");
const touchKnob = document.querySelector("#touchKnob");
const mobileControls = document.querySelector(".mobile-controls");
const topbar = document.querySelector(".topbar");
const hud = document.querySelector(".hud");

const DESKTOP_STAGE = { cols: 25, rows: 19, mode: "desktop" };
const MOBILE_STAGE = { cols: 17, rows: 27, mode: "mobile" };
let COLS = DESKTOP_STAGE.cols;
let ROWS = DESKTOP_STAGE.rows;
const PLAYER_STEP_MS = 112;
const BASE_ONI_STEP_MS = 470;
const ONI_SPEEDUP_PER_LEVEL = 20;
const ONI_SPAWN_DELAY_MS = 950;
const LEVEL_ADVANCE_DELAY_MS = 1900;
const MAX_ONI = 8;
const ONI_ALERT_DISTANCE = 6;
const LIGHT_RADIUS_CELLS = 4.2;
const GOAL_REVEAL_DISTANCE = 3.9;
const RADAR_DURATION_MS = 9000;
const GUN_START_LEVEL = 15;
const RADAR_START_LEVEL = 5;
const GUN_INITIAL_BULLETS = 1;
const AMMO_ITEM_COUNT = 2;
const AMMO_PER_ITEM = 1;
const TOUCH_DEAD_ZONE = 12;
const WALL = 1;
const FLOOR = 0;

const dirs = {
  up: { dx: 0, dy: -1, name: "up" },
  down: { dx: 0, dy: 1, name: "down" },
  left: { dx: -1, dy: 0, name: "left" },
  right: { dx: 1, dy: 0, name: "right" },
};

const keyDirs = {
  ArrowUp: dirs.up,
  KeyW: dirs.up,
  ArrowDown: dirs.down,
  KeyS: dirs.down,
  ArrowLeft: dirs.left,
  KeyA: dirs.left,
  ArrowRight: dirs.right,
  KeyD: dirs.right,
};

function isMobileStage() {
  return window.matchMedia("(max-width: 820px)").matches;
}

function applyStageLayout() {
  const nextStage = isMobileStage() ? MOBILE_STAGE : DESKTOP_STAGE;
  const changed = stageMode !== nextStage.mode;
  COLS = nextStage.cols;
  ROWS = nextStage.rows;
  stageMode = nextStage.mode;
  return changed;
}

let maze;
let floors;
let player;
let goal;
let jumpItem;
let radarItem;
let gunItem;
let ammoItems;
let oniList;
let gameState;
let level;
let wallJumpAvailable;
let wallJumpUsed;
let lastDir;
let activeDir;
let heldKeys;
let startedAt;
let finalTime;
let nextPlayerStep;
let levelAdvanceAt;
let pausedAt;
let radarActiveUntil;
let gunBullets;
let shotEffects;
let cellSize;
let boardWidth;
let boardHeight;
let noticeText;
let noticeUntil;
let animationId;
let textureMarks;
let stageMode = "";
let touchPointerId = null;
let touchDir = null;

function shuffle(items) {
  const result = [...items];
  for (let i = result.length - 1; i > 0; i -= 1) {
    const j = Math.floor(Math.random() * (i + 1));
    [result[i], result[j]] = [result[j], result[i]];
  }
  return result;
}

function inBounds(x, y) {
  return x >= 0 && y >= 0 && x < COLS && y < ROWS;
}

function isFloor(x, y) {
  return inBounds(x, y) && maze[y][x] === FLOOR;
}

function sameCell(a, b) {
  return a.x === b.x && a.y === b.y;
}

function cellKey(cell) {
  return `${cell.x},${cell.y}`;
}

function makeMaze() {
  const grid = Array.from({ length: ROWS }, () => Array(COLS).fill(WALL));
  const carveDirs = [
    { dx: 2, dy: 0 },
    { dx: -2, dy: 0 },
    { dx: 0, dy: 2 },
    { dx: 0, dy: -2 },
  ];

  function carve(x, y) {
    grid[y][x] = FLOOR;

    for (const dir of shuffle(carveDirs)) {
      const nx = x + dir.dx;
      const ny = y + dir.dy;
      if (nx <= 0 || ny <= 0 || nx >= COLS - 1 || ny >= ROWS - 1) {
        continue;
      }
      if (grid[ny][nx] === WALL) {
        grid[y + dir.dy / 2][x + dir.dx / 2] = FLOOR;
        carve(nx, ny);
      }
    }
  }

  carve(1, 1);

  for (let y = 2; y < ROWS - 2; y += 1) {
    for (let x = 2; x < COLS - 2; x += 1) {
      if (grid[y][x] !== WALL || Math.random() > 0.14) {
        continue;
      }

      const horizontal = grid[y][x - 1] === FLOOR && grid[y][x + 1] === FLOOR;
      const vertical = grid[y - 1][x] === FLOOR && grid[y + 1][x] === FLOOR;
      if (horizontal || vertical) {
        grid[y][x] = FLOOR;
      }
    }
  }

  return grid;
}

function collectFloors(grid) {
  const result = [];
  for (let y = 0; y < ROWS; y += 1) {
    for (let x = 0; x < COLS; x += 1) {
      if (grid[y][x] === FLOOR) {
        result.push({ x, y });
      }
    }
  }
  return result;
}

function pickPlayerSpawn() {
  const candidates = floors.filter((cell) => {
    const openNeighbors = Object.values(dirs).filter((dir) => isFloor(cell.x + dir.dx, cell.y + dir.dy)).length;
    return openNeighbors >= 1;
  });
  const pool = candidates.length > 0 ? candidates : floors;
  return { ...pool[Math.floor(Math.random() * pool.length)] };
}

function bfsDistances(from) {
  const distances = Array.from({ length: ROWS }, () => Array(COLS).fill(Infinity));
  const queue = [from];
  let head = 0;
  distances[from.y][from.x] = 0;

  while (head < queue.length) {
    const current = queue[head];
    head += 1;

    for (const dir of Object.values(dirs)) {
      const nx = current.x + dir.dx;
      const ny = current.y + dir.dy;
      if (!isFloor(nx, ny) || distances[ny][nx] !== Infinity) {
        continue;
      }

      distances[ny][nx] = distances[current.y][current.x] + 1;
      queue.push({ x: nx, y: ny });
    }
  }

  return distances;
}

function pickJumpItem(blockedCells = []) {
  const blocked = new Set([cellKey(player), cellKey(goal), ...blockedCells.map((cell) => cellKey(cell))]);
  const distances = bfsDistances(player);
  const goalDistance = distances[goal.y][goal.x];
  const targetDistance = Number.isFinite(goalDistance) ? goalDistance * 0.46 : 8;
  let candidates = floors
    .filter((cell) => {
      const distance = distances[cell.y][cell.x];
      return (
        Number.isFinite(distance) &&
        distance >= 5 &&
        distance <= Math.max(6, goalDistance - 5) &&
        !blocked.has(cellKey(cell))
      );
    })
    .sort((a, b) => {
      const aScore = Math.abs(distances[a.y][a.x] - targetDistance);
      const bScore = Math.abs(distances[b.y][b.x] - targetDistance);
      return aScore - bScore;
    });

  if (candidates.length === 0) {
    candidates = floors.filter((cell) => {
      const distance = distances[cell.y][cell.x];
      return Number.isFinite(distance) && !blocked.has(cellKey(cell));
    });
  }

  const pool = candidates.slice(0, Math.max(1, Math.min(18, candidates.length)));
  const picked = pool[Math.floor(Math.random() * pool.length)] || floors.find((cell) => !sameCell(cell, player)) || player;
  return { ...picked, collected: false };
}

function pickRadarItem(blockedCells = []) {
  const blocked = new Set([cellKey(player), cellKey(goal), ...blockedCells.map((cell) => cellKey(cell))]);
  const distances = bfsDistances(player);
  const candidates = floors
    .filter((cell) => {
      const distance = distances[cell.y][cell.x];
      return Number.isFinite(distance) && distance >= 7 && !blocked.has(cellKey(cell));
    })
    .sort((a, b) => distances[b.y][b.x] - distances[a.y][a.x]);

  const pool = candidates.slice(0, Math.max(1, Math.min(24, candidates.length)));
  const picked = pool[Math.floor(Math.random() * pool.length)] || floors.find((cell) => !blocked.has(cellKey(cell))) || player;
  return { ...picked, collected: false };
}

function pickGunItem(blockedCells = []) {
  const blocked = new Set([cellKey(player), cellKey(goal), ...blockedCells.map((cell) => cellKey(cell))]);
  const distances = bfsDistances(player);
  const candidates = floors
    .filter((cell) => {
      const distance = distances[cell.y][cell.x];
      return Number.isFinite(distance) && distance >= 6 && !blocked.has(cellKey(cell));
    })
    .sort((a, b) => {
      const aScore = Math.abs(distances[a.y][a.x] - 10);
      const bScore = Math.abs(distances[b.y][b.x] - 10);
      return aScore - bScore;
    });

  const pool = candidates.slice(0, Math.max(1, Math.min(20, candidates.length)));
  const picked = pool[Math.floor(Math.random() * pool.length)] || floors.find((cell) => !blocked.has(cellKey(cell))) || player;
  return { ...picked, collected: false };
}

function pickAmmoItems(blockedCells = []) {
  const blocked = new Set([cellKey(player), cellKey(goal), ...blockedCells.map((cell) => cellKey(cell))]);
  const distances = bfsDistances(player);
  const candidates = shuffle(
    floors.filter((cell) => {
      const distance = distances[cell.y][cell.x];
      return Number.isFinite(distance) && distance >= 5 && !blocked.has(cellKey(cell));
    }),
  );
  const picked = [];

  for (const spread of [7, 5, 3, 0]) {
    for (const cell of candidates) {
      if (picked.length >= AMMO_ITEM_COUNT) {
        break;
      }
      if (picked.some((existing) => sameCell(existing, cell))) {
        continue;
      }
      const farEnough = picked.every((existing) => Math.abs(existing.x - cell.x) + Math.abs(existing.y - cell.y) >= spread);
      if (farEnough) {
        picked.push({ ...cell, collected: false });
      }
    }
  }

  return picked.slice(0, AMMO_ITEM_COUNT);
}

function getOniCountForLevel(targetLevel) {
  return Math.min(1 + Math.floor(targetLevel / 5), MAX_ONI);
}

function getOniSpeedTier(targetLevel) {
  const levelInBlock = targetLevel % 5;
  return levelInBlock === 0 ? 0 : levelInBlock - 1;
}

function getOniBaseStepForLevel(targetLevel) {
  return Math.max(235, BASE_ONI_STEP_MS - getOniSpeedTier(targetLevel) * ONI_SPEEDUP_PER_LEVEL);
}

function pickOniSpawnPoints(count) {
  const distances = bfsDistances(player);
  const minDistance = Math.min(12, 7 + Math.floor(level / 2));
  let candidates = floors.filter((cell) => {
    const distance = distances[cell.y][cell.x];
    return Number.isFinite(distance) && distance >= minDistance && !sameCell(cell, player);
  });

  if (candidates.length < count) {
    candidates = floors.filter((cell) => {
      const distance = distances[cell.y][cell.x];
      return Number.isFinite(distance) && distance >= 5 && !sameCell(cell, player);
    });
  }

  if (candidates.length === 0) {
    candidates = floors.filter((cell) => !sameCell(cell, player));
  }

  const shuffled = shuffle(candidates);
  const picked = [];
  for (const spread of [8, 6, 4, 2, 0]) {
    for (const cell of shuffled) {
      if (picked.length >= count) {
        break;
      }
      if (picked.some((existing) => sameCell(existing, cell))) {
        continue;
      }
      const farEnough = picked.every((existing) => Math.abs(existing.x - cell.x) + Math.abs(existing.y - cell.y) >= spread);
      if (farEnough) {
        picked.push({ x: cell.x, y: cell.y });
      }
    }
  }

  return picked.slice(0, count);
}

function buildOniList(now, spawnPoints) {
  const count = spawnPoints.length;
  const baseStep = getOniBaseStepForLevel(level);

  return Array.from({ length: count }, (_, index) => {
    const spawn = spawnPoints[index % spawnPoints.length];
    const spawnAt = now + ONI_SPAWN_DELAY_MS + index * 420;
    return {
      id: index,
      spawnX: spawn.x,
      spawnY: spawn.y,
      x: spawn.x,
      y: spawn.y,
      visible: false,
      defeated: false,
      alerted: false,
      spawnAt,
      nextStep: spawnAt + 220 + index * 65,
      stepMs: baseStep + (index % 3) * 36,
      hue: index / Math.max(1, count - 1),
    };
  });
}

function buildTextureMarks() {
  const marks = [];
  for (let i = 0; i < 180; i += 1) {
    const source = i % 3 === 0 ? floors : null;
    const cell = source ? source[Math.floor(Math.random() * source.length)] : randomCell();
    marks.push({
      x: cell.x + Math.random(),
      y: cell.y + Math.random(),
      length: 0.08 + Math.random() * 0.42,
      width: 0.012 + Math.random() * 0.025,
      angle: Math.random() * Math.PI,
      alpha: 0.05 + Math.random() * 0.11,
      light: source ? 1 : 0,
    });
  }
  return marks;
}

function randomCell() {
  return {
    x: Math.floor(Math.random() * COLS),
    y: Math.floor(Math.random() * ROWS),
  };
}

function startRun() {
  level = 1;
  startLevel(level);
}

function startLevel(nextLevel) {
  cancelAnimationFrame(animationId);
  hideGameMenu();
  applyStageLayout();

  level = nextLevel;
  maze = makeMaze();
  floors = collectFloors(maze);
  player = pickPlayerSpawn();
  maze[player.y][player.x] = FLOOR;

  const oniSpawnPoints = pickOniSpawnPoints(getOniCountForLevel(level));
  goal = { ...oniSpawnPoints[Math.floor(Math.random() * oniSpawnPoints.length)] };
  jumpItem = pickJumpItem(oniSpawnPoints);
  const itemBlocks = [...oniSpawnPoints, jumpItem];
  radarItem = level >= RADAR_START_LEVEL ? pickRadarItem(itemBlocks) : null;
  if (radarItem) {
    itemBlocks.push(radarItem);
  }
  gunItem = null;
  ammoItems = [];
  if (level >= GUN_START_LEVEL) {
    gunItem = pickGunItem(itemBlocks);
    itemBlocks.push(gunItem);
    ammoItems = pickAmmoItems(itemBlocks);
  }

  gameState = "playing";
  wallJumpAvailable = false;
  wallJumpUsed = false;
  lastDir = dirs.right;
  activeDir = null;
  heldKeys = new Map();
  startedAt = performance.now();
  finalTime = 0;
  nextPlayerStep = startedAt;
  levelAdvanceAt = 0;
  pausedAt = 0;
  radarActiveUntil = 0;
  gunBullets = 0;
  shotEffects = [];
  oniList = buildOniList(startedAt, oniSpawnPoints);
  textureMarks = buildTextureMarks();
  noticeText = `LEVEL ${level}: 鬼は近づくまで待機します。出現地点のどこかが隠しゴールです。`;
  noticeUntil = startedAt + 2800;

  resizeCanvas();
  updateHud(startedAt);
  updatePauseButton();
  animationId = requestAnimationFrame(update);
}

function setNotice(text, duration = 1200) {
  noticeText = text;
  noticeUntil = performance.now() + duration;
}

function togglePause() {
  if (gameState === "playing") {
    gameState = "paused";
    pausedAt = performance.now();
    activeDir = null;
    heldKeys.clear();
    setNotice("一時停止中", 100000);
    updatePauseButton();
    return;
  }

  if (gameState !== "paused") {
    return;
  }

  const now = performance.now();
  const pausedDuration = now - pausedAt;
  startedAt += pausedDuration;
  nextPlayerStep += pausedDuration;
  noticeUntil = now + 900;
  oniList.forEach((oni) => {
    oni.spawnAt += pausedDuration;
    oni.nextStep += pausedDuration;
  });
  if (radarActiveUntil > pausedAt) {
    radarActiveUntil += pausedDuration;
  }
  gameState = "playing";
  pausedAt = 0;
  setNotice("再開", 900);
  updatePauseButton();
}

function updatePauseButton() {
  const paused = gameState === "paused";
  pauseButton.textContent = paused ? "再開" : "一時停止";
  pauseButton.setAttribute("aria-pressed", String(paused));
}

function showGameMenu() {
  gameMenu.hidden = false;
  gameMenuText.textContent = `LEVEL ${level} でゲームオーバー`;
  retryLevelButton.textContent = `LEVEL ${level}から再開`;
}

function hideGameMenu() {
  gameMenu.hidden = true;
}

function tryMove(dir) {
  if (gameState !== "playing") {
    return;
  }

  lastDir = dir;
  const nx = player.x + dir.dx;
  const ny = player.y + dir.dy;

  if (isFloor(nx, ny)) {
    player = { x: nx, y: ny };
    collectItems();
    checkOutcome();
    return;
  }

  if (!wallJumpAvailable) {
    setNotice("青いアイテムを拾うと、壁越えが使えるようになります。", 1100);
  } else if (!wallJumpUsed) {
    setNotice("スペースキーで向いている方向の壁を1回だけ乗り越えられます。", 1000);
  }
}

function collectItems() {
  if (!jumpItem.collected && sameCell(player, jumpItem)) {
    jumpItem.collected = true;
    wallJumpAvailable = true;
    setNotice("壁越えアイテムを取得。スペースキーで1回だけ使用できます。", 1500);
  }

  if (radarItem && !radarItem.collected && sameCell(player, radarItem)) {
    radarItem.collected = true;
    radarActiveUntil = performance.now() + RADAR_DURATION_MS;
    setNotice("鬼探知アイテムを取得。しばらく鬼の位置が見えます。", 1700);
  }

  for (const ammoItem of ammoItems) {
    if (!ammoItem.collected && sameCell(player, ammoItem)) {
      ammoItem.collected = true;
      gunBullets += AMMO_PER_ITEM;
      setNotice(`弾を${AMMO_PER_ITEM}発取得。現在${gunBullets}発。`, 1400);
    }
  }

  if (gunItem && !gunItem.collected && sameCell(player, gunItem)) {
    gunItem.collected = true;
    gunBullets += GUN_INITIAL_BULLETS;
    setNotice(`拳銃を取得。1発装填済み、現在${gunBullets}発。`, 1700);
  }
}

function tryWallJump() {
  if (gameState !== "playing") {
    return;
  }

  if (!wallJumpAvailable) {
    setNotice("壁越えには、迷路内の青いアイテムが必要です。", 1200);
    return;
  }

  if (wallJumpUsed) {
    setNotice("壁越えはこのレベルではもう使えません。", 1000);
    return;
  }

  const wall = {
    x: player.x + lastDir.dx,
    y: player.y + lastDir.dy,
  };
  const landing = {
    x: player.x + lastDir.dx * 2,
    y: player.y + lastDir.dy * 2,
  };

  if (!inBounds(wall.x, wall.y) || maze[wall.y][wall.x] !== WALL || !isFloor(landing.x, landing.y)) {
    setNotice("その方向には乗り越えられる壁がありません。", 1000);
    return;
  }

  player = landing;
  wallJumpUsed = true;
  setNotice("壁を乗り越えた。次のレベルまで再使用できません。", 1300);
  collectItems();
  checkOutcome();
}

function tryShoot() {
  if (gameState !== "playing") {
    return;
  }

  if (!gunItem || !gunItem.collected) {
    setNotice("拳銃アイテムが必要です。LV15以降に出現します。", 1100);
    return;
  }

  if (gunBullets <= 0) {
    setNotice("弾切れです。", 900);
    return;
  }

  gunBullets -= 1;
  const start = {
    x: player.x * cellSize + cellSize / 2,
    y: player.y * cellSize + cellSize / 2,
  };
  let endCell = player;
  let target = null;
  let x = player.x + lastDir.dx;
  let y = player.y + lastDir.dy;

  while (isFloor(x, y)) {
    endCell = { x, y };
    target = oniList.find((oni) => !oni.defeated && oni.visible && oni.x === x && oni.y === y);
    if (target) {
      break;
    }
    x += lastDir.dx;
    y += lastDir.dy;
  }

  const end = {
    x: endCell.x * cellSize + cellSize / 2,
    y: endCell.y * cellSize + cellSize / 2,
  };
  shotEffects.push({ start, end, until: performance.now() + 180 });

  if (target) {
    target.defeated = true;
    target.visible = false;
    setNotice(`鬼を撃退。残り${gunBullets}発。`, 1100);
  } else {
    setNotice(`外れた。残り${gunBullets}発。`, 900);
  }
}

function checkOutcome() {
  if (hasOniCollision()) {
    gameState = "lost";
    finalTime = performance.now() - startedAt;
    activeDir = null;
    heldKeys.clear();
    setNotice("鬼に追いつかれた。同じレベルから再開できます。", 100000);
    showGameMenu();
    return;
  }

  if (sameCell(player, goal)) {
    gameState = "won";
    finalTime = performance.now() - startedAt;
    levelAdvanceAt = performance.now() + LEVEL_ADVANCE_DELAY_MS;
    setNotice(`LEVEL ${level} CLEAR。次は鬼が${getOniCountForLevel(level + 1)}体です。`, 100000);
  }
}

function hasOniCollision() {
  return oniList.some((oni) => !oni.defeated && oni.visible && sameCell(player, oni));
}

function update(now) {
  if (gameState === "won" && now >= levelAdvanceAt) {
    startLevel(level + 1);
    return;
  }

  if (gameState === "playing") {
    updateOniSpawn(now);

    if (activeDir && now >= nextPlayerStep) {
      tryMove(activeDir);
      nextPlayerStep = now + PLAYER_STEP_MS;
    }

    updateOniMovement(now);
  }

  updateHud(now);
  draw(now);
  animationId = requestAnimationFrame(update);
}

function updateOniSpawn(now) {
  for (const oni of oniList) {
    if (!oni.defeated && !oni.visible && now >= oni.spawnAt) {
      oni.visible = true;
      setNotice("鬼が迷路内に出現しました。近づくと追跡されます。", 1450);
    }
  }
}

function updateOniMovement(now) {
  const playerDistances = bfsDistances(player);
  for (const oni of oniList) {
    if (oni.defeated || !oni.visible) {
      continue;
    }

    if (!oni.alerted) {
      const distance = playerDistances[oni.y][oni.x];
      if (distance <= ONI_ALERT_DISTANCE) {
        oni.alerted = true;
        setNotice("鬼がこちらに気づいた。", 1000);
      } else {
        continue;
      }
    }

    if (now < oni.nextStep) {
      continue;
    }

    moveOni(oni, playerDistances);
    oni.nextStep = now + oni.stepMs;
  }
  checkOutcome();
}

function moveOni(oni, distances = bfsDistances(player)) {
  const occupied = new Set(
    oniList.filter((other) => !other.defeated && other.visible && other.id !== oni.id).map((other) => cellKey(other)),
  );
  const candidates = Object.values(dirs)
    .map((dir) => ({ x: oni.x + dir.dx, y: oni.y + dir.dy }))
    .filter((cell) => isFloor(cell.x, cell.y) && Number.isFinite(distances[cell.y][cell.x]))
    .map((cell) => ({
      ...cell,
      score: distances[cell.y][cell.x] + (occupied.has(cellKey(cell)) ? 4 : 0) + Math.random() * 0.18,
    }));

  if (candidates.length === 0) {
    return;
  }

  candidates.sort((a, b) => a.score - b.score);

  const next = candidates[0];
  oni.x = next.x;
  oni.y = next.y;
}

function updateHud(now) {
  levelStatus.textContent = `LEVEL ${level}`;

  if (wallJumpUsed) {
    jumpStatus.textContent = "使用済み";
    jumpStatus.style.color = "#d5d9d3";
  } else if (wallJumpAvailable) {
    jumpStatus.textContent = "使用可能";
    jumpStatus.style.color = "#72f0ff";
  } else {
    jumpStatus.textContent = "アイテム未取得";
    jumpStatus.style.color = "#f6c356";
  }

  const statusNow = gameState === "paused" ? pausedAt : now;
  if (!radarItem) {
    radarStatus.textContent = "LV5から";
    radarStatus.style.color = "#d5d9d3";
  } else if (isRadarActive(statusNow)) {
    radarStatus.textContent = `${Math.ceil((radarActiveUntil - statusNow) / 1000)}秒`;
    radarStatus.style.color = "#ff7f9a";
  } else if (radarItem.collected) {
    radarStatus.textContent = "終了";
    radarStatus.style.color = "#d5d9d3";
  } else {
    radarStatus.textContent = "未取得";
    radarStatus.style.color = "#f6c356";
  }

  if (!gunItem) {
    gunStatus.textContent = "LV15から";
    gunStatus.style.color = "#d5d9d3";
  } else if (gunItem.collected) {
    gunStatus.textContent = `${gunBullets}発`;
    gunStatus.style.color = gunBullets > 0 ? "#ffe08a" : "#d5d9d3";
  } else if (gunBullets > 0) {
    gunStatus.textContent = `弾${gunBullets}発`;
    gunStatus.style.color = "#ffe08a";
  } else {
    gunStatus.textContent = "未取得";
    gunStatus.style.color = "#f6c356";
  }

  const activeOni = oniList.filter((oni) => !oni.defeated).length;
  const visibleOni = oniList.filter((oni) => !oni.defeated && oni.visible).length;
  const chasingOni = oniList.filter((oni) => !oni.defeated && oni.visible && oni.alerted).length;
  if (gameState === "won") {
    oniStatus.textContent = "逃げ切り";
  } else if (gameState === "lost") {
    oniStatus.textContent = "接触";
  } else if (gameState === "paused") {
    oniStatus.textContent = "停止中";
  } else {
    oniStatus.textContent = activeOni > 0 ? `追${chasingOni} 出${visibleOni}/${activeOni}` : "撃退";
  }

  const elapsed = gameState === "playing" ? now - startedAt : gameState === "paused" ? pausedAt - startedAt : finalTime;
  timer.textContent = formatTime(elapsed);
}

function formatTime(ms) {
  return `${(ms / 1000).toFixed(1)}秒`;
}

function resizeCanvas() {
  const viewportHeight = window.visualViewport?.height || window.innerHeight;
  const mobile = stageMode === MOBILE_STAGE.mode;
  const mobileControlsHeight = mobile ? mobileControls.getBoundingClientRect().height || 126 : 0;
  const chromeHeight = mobile
    ? topbar.getBoundingClientRect().height + hud.getBoundingClientRect().height + mobileControlsHeight + 50
    : 255;
  const availableWidth = mobile ? Math.max(280, window.innerWidth - 2) : Math.min(window.innerWidth - 28, 1120);
  const availableHeight = mobile ? Math.max(420, viewportHeight - chromeHeight) : Math.max(360, window.innerHeight - chromeHeight);
  const minCellSize = mobile ? 14 : 18;
  const fittedCellSize = mobile ? availableWidth / COLS : Math.floor(Math.min(availableWidth / COLS, availableHeight / ROWS));
  cellSize = Math.max(minCellSize, fittedCellSize);
  boardWidth = cellSize * COLS;
  boardHeight = cellSize * ROWS;

  const dpr = window.devicePixelRatio || 1;
  canvas.style.width = `${boardWidth}px`;
  canvas.style.height = `${boardHeight}px`;
  canvas.width = Math.floor(boardWidth * dpr);
  canvas.height = Math.floor(boardHeight * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.imageSmoothingEnabled = false;
}

function draw(now) {
  const displayNow = gameState === "paused" ? pausedAt : now;
  ctx.clearRect(0, 0, boardWidth, boardHeight);
  drawMazeShell();
  drawFloorTexture();
  drawTextureMarks();
  drawWallEdges();
  if (isGoalVisible()) {
    drawGoal(displayNow);
  }
  if (!jumpItem.collected) {
    drawJumpItem(displayNow);
  }
  if (radarItem && !radarItem.collected) {
    drawRadarItem(displayNow);
  }
  if (gunItem && !gunItem.collected) {
    drawGunItem(displayNow);
  }
  ammoItems.forEach((ammoItem, index) => {
    if (!ammoItem.collected) {
      drawAmmoItem(ammoItem, index, displayNow);
    }
  });
  oniList.forEach((oni, index) => {
    if (!oni.defeated && oni.visible) {
      drawOni(oni, index, displayNow);
    }
  });
  drawPlayer(displayNow);
  drawDarkness();
  if (isRadarActive(displayNow)) {
    drawOniRadar(displayNow);
  }
  drawShotEffects(displayNow);
  drawOverlay();
  updateMessage(now);
}

function drawMazeShell() {
  const wallGradient = ctx.createLinearGradient(0, 0, boardWidth, boardHeight);
  wallGradient.addColorStop(0, "#17201d");
  wallGradient.addColorStop(0.55, "#202a26");
  wallGradient.addColorStop(1, "#101515");
  ctx.fillStyle = wallGradient;
  ctx.fillRect(0, 0, boardWidth, boardHeight);
}

function drawFloorTexture() {
  const floorGradient = ctx.createLinearGradient(0, 0, boardWidth, boardHeight);
  floorGradient.addColorStop(0, "#657065");
  floorGradient.addColorStop(0.48, "#48534c");
  floorGradient.addColorStop(1, "#333c38");
  ctx.fillStyle = floorGradient;

  for (const cell of floors) {
    ctx.fillRect(cell.x * cellSize, cell.y * cellSize, cellSize, cellSize);
  }
}

function drawTextureMarks() {
  ctx.save();
  ctx.lineCap = "round";
  for (const mark of textureMarks) {
    const x = mark.x * cellSize;
    const y = mark.y * cellSize;
    const length = mark.length * cellSize;
    ctx.globalAlpha = mark.alpha;
    ctx.strokeStyle = mark.light ? "#c3cbbf" : "#050807";
    ctx.lineWidth = Math.max(1, mark.width * cellSize);
    ctx.beginPath();
    ctx.moveTo(x, y);
    ctx.lineTo(x + Math.cos(mark.angle) * length, y + Math.sin(mark.angle) * length);
    ctx.stroke();
  }
  ctx.restore();
}

function drawWallEdges() {
  ctx.save();
  for (const cell of floors) {
    const x = cell.x * cellSize;
    const y = cell.y * cellSize;
    const shadow = Math.max(3, cellSize * 0.13);
    const glow = Math.max(1, cellSize * 0.04);

    if (!isFloor(cell.x, cell.y - 1)) {
      drawEdgeShadow(x, y, cellSize, shadow, "top");
    }
    if (!isFloor(cell.x, cell.y + 1)) {
      drawEdgeShadow(x, y + cellSize - shadow, cellSize, shadow, "bottom");
    }
    if (!isFloor(cell.x - 1, cell.y)) {
      drawEdgeShadow(x, y, shadow, cellSize, "left");
    }
    if (!isFloor(cell.x + 1, cell.y)) {
      drawEdgeShadow(x + cellSize - shadow, y, shadow, cellSize, "right");
    }

    ctx.fillStyle = "rgba(255, 255, 255, 0.025)";
    if (!isFloor(cell.x, cell.y + 1)) {
      ctx.fillRect(x, y + cellSize - glow, cellSize, glow);
    }
  }
  ctx.restore();
}

function drawEdgeShadow(x, y, width, height, side) {
  const gradient =
    side === "left" || side === "right"
      ? ctx.createLinearGradient(x, y, x + width, y)
      : ctx.createLinearGradient(x, y, x, y + height);

  if (side === "bottom" || side === "right") {
    gradient.addColorStop(0, "rgba(0, 0, 0, 0)");
    gradient.addColorStop(1, "rgba(0, 0, 0, 0.42)");
  } else {
    gradient.addColorStop(0, "rgba(0, 0, 0, 0.48)");
    gradient.addColorStop(1, "rgba(0, 0, 0, 0)");
  }
  ctx.fillStyle = gradient;
  ctx.fillRect(x, y, width, height);
}

function isGoalVisible() {
  const dx = goal.x - player.x;
  const dy = goal.y - player.y;
  return Math.hypot(dx, dy) <= GOAL_REVEAL_DISTANCE;
}

function isRadarActive(now = performance.now()) {
  return radarActiveUntil > now;
}

function drawGoal(now) {
  const cx = goal.x * cellSize + cellSize / 2;
  const cy = goal.y * cellSize + cellSize / 2;
  const pulse = 0.92 + Math.sin(now / 220) * 0.08;
  const radius = cellSize * 0.38 * pulse;

  drawGlow(cx, cy, cellSize * 1.05, "rgba(88, 255, 156, 0.32)");
  ctx.save();
  ctx.translate(cx, cy);
  ctx.rotate(Math.PI / 4);
  ctx.strokeStyle = "rgba(148, 255, 190, 0.98)";
  ctx.lineWidth = Math.max(2, cellSize * 0.07);
  ctx.strokeRect(-radius, -radius, radius * 2, radius * 2);
  ctx.restore();

  ctx.fillStyle = "#dfffe7";
  ctx.font = `900 ${Math.max(8, cellSize * 0.22)}px system-ui`;
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillText("GOAL", cx, cy + 1);
}

function drawJumpItem(now) {
  const cx = jumpItem.x * cellSize + cellSize / 2;
  const cy = jumpItem.y * cellSize + cellSize / 2 + Math.sin(now / 180) * cellSize * 0.05;
  const radius = cellSize * 0.24;

  drawGlow(cx, cy, cellSize * 1.05, "rgba(75, 214, 255, 0.34)");
  ctx.fillStyle = "#d9fbff";
  ctx.beginPath();
  ctx.arc(cx, cy, radius, 0, Math.PI * 2);
  ctx.fill();
  ctx.strokeStyle = "#44d8ff";
  ctx.lineWidth = Math.max(2, cellSize * 0.06);
  ctx.stroke();

  ctx.fillStyle = "#0a4f60";
  ctx.beginPath();
  ctx.moveTo(cx, cy - radius * 0.7);
  ctx.lineTo(cx + radius * 0.48, cy);
  ctx.lineTo(cx, cy + radius * 0.7);
  ctx.lineTo(cx - radius * 0.48, cy);
  ctx.closePath();
  ctx.fill();
}

function drawRadarItem(now) {
  const cx = radarItem.x * cellSize + cellSize / 2;
  const cy = radarItem.y * cellSize + cellSize / 2 + Math.sin(now / 170) * cellSize * 0.05;
  const radius = cellSize * 0.25;
  const sweep = (now / 420) % (Math.PI * 2);

  drawGlow(cx, cy, cellSize * 1.08, "rgba(255, 52, 95, 0.34)");
  ctx.strokeStyle = "#ff496d";
  ctx.lineWidth = Math.max(2, cellSize * 0.06);
  ctx.beginPath();
  ctx.arc(cx, cy, radius, 0, Math.PI * 2);
  ctx.stroke();

  ctx.fillStyle = "#ffd9e1";
  ctx.beginPath();
  ctx.arc(cx, cy, radius * 0.38, 0, Math.PI * 2);
  ctx.fill();

  ctx.strokeStyle = "#ff9aad";
  ctx.lineWidth = Math.max(1, cellSize * 0.035);
  ctx.beginPath();
  ctx.moveTo(cx, cy);
  ctx.lineTo(cx + Math.cos(sweep) * radius * 1.35, cy + Math.sin(sweep) * radius * 1.35);
  ctx.stroke();
}

function drawGunItem(now) {
  const cx = gunItem.x * cellSize + cellSize / 2;
  const cy = gunItem.y * cellSize + cellSize / 2 + Math.sin(now / 190) * cellSize * 0.04;
  const size = cellSize * 0.36;

  drawGlow(cx, cy, cellSize * 1.08, "rgba(255, 214, 92, 0.3)");
  ctx.save();
  ctx.translate(cx, cy);
  ctx.rotate(-0.22);
  ctx.fillStyle = "#ffe08a";
  ctx.fillRect(-size * 0.62, -size * 0.22, size * 1.1, size * 0.28);
  ctx.fillRect(size * 0.18, -size * 0.16, size * 0.58, size * 0.18);
  ctx.fillStyle = "#6b4d20";
  ctx.fillRect(-size * 0.42, size * 0.02, size * 0.24, size * 0.54);
  ctx.fillStyle = "#1a1411";
  ctx.fillRect(-size * 0.04, size * 0.02, size * 0.22, size * 0.18);
  ctx.restore();
}

function drawAmmoItem(ammoItem, index, now) {
  const cx = ammoItem.x * cellSize + cellSize / 2;
  const cy = ammoItem.y * cellSize + cellSize / 2 + Math.sin(now / 175 + index) * cellSize * 0.05;
  const size = cellSize * 0.28;

  drawGlow(cx, cy, cellSize * 0.92, "rgba(255, 184, 67, 0.28)");
  ctx.save();
  ctx.translate(cx, cy);
  ctx.rotate(-0.36);
  ctx.fillStyle = "#ffdf7c";
  ctx.fillRect(-size * 0.28, -size * 0.55, size * 0.56, size * 1.1);
  ctx.fillStyle = "#c9822e";
  ctx.fillRect(-size * 0.28, size * 0.2, size * 0.56, size * 0.32);
  ctx.fillStyle = "#fff6c8";
  ctx.beginPath();
  ctx.moveTo(-size * 0.28, -size * 0.55);
  ctx.lineTo(0, -size * 0.9);
  ctx.lineTo(size * 0.28, -size * 0.55);
  ctx.closePath();
  ctx.fill();
  ctx.restore();
}

function drawPlayer(now) {
  const cx = player.x * cellSize + cellSize / 2;
  const cy = player.y * cellSize + cellSize / 2;
  const radius = cellSize * 0.32;
  const breath = 1 + Math.sin(now / 220) * 0.03;

  drawGlow(cx, cy, cellSize * 1.1, "rgba(82, 224, 255, 0.23)");
  ctx.save();
  ctx.translate(cx, cy);
  ctx.rotate(directionAngle(lastDir));

  ctx.fillStyle = "rgba(0, 0, 0, 0.34)";
  ctx.beginPath();
  ctx.ellipse(0, radius * 0.22, radius * 0.9, radius * 0.55, 0, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = "#1dd5d2";
  ctx.beginPath();
  ctx.ellipse(0, 0, radius * 0.62 * breath, radius * 1.02 * breath, 0, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = "#ebffff";
  ctx.beginPath();
  ctx.arc(0, -radius * 0.38, radius * 0.28, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = "#0b4f55";
  ctx.fillRect(-radius * 0.14, radius * 0.12, radius * 0.28, radius * 0.72);
  ctx.restore();
}

function drawOni(oni, index, now) {
  const stackOffset = stackOffsetFor(oni, index);
  const cx = oni.x * cellSize + cellSize / 2 + stackOffset.x;
  const cy = oni.y * cellSize + cellSize / 2 + stackOffset.y;
  const radius = cellSize * 0.35;
  const pulse = 1 + Math.sin(now / 170 + index) * 0.05;

  drawGlow(cx, cy, cellSize * 1.2, "rgba(255, 34, 72, 0.3)");

  ctx.fillStyle = "rgba(0, 0, 0, 0.42)";
  ctx.beginPath();
  ctx.ellipse(cx, cy + radius * 0.25, radius * 0.9, radius * 0.56, 0, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = index % 2 === 0 ? "#e41e45" : "#b91635";
  ctx.beginPath();
  ctx.arc(cx, cy, radius * pulse, 0, Math.PI * 2);
  ctx.fill();

  ctx.fillStyle = "#f2d36b";
  ctx.beginPath();
  ctx.moveTo(cx - radius * 0.56, cy - radius * 0.68);
  ctx.lineTo(cx - radius * 0.18, cy - radius * 1.16);
  ctx.lineTo(cx - radius * 0.02, cy - radius * 0.55);
  ctx.closePath();
  ctx.fill();
  ctx.beginPath();
  ctx.moveTo(cx + radius * 0.56, cy - radius * 0.68);
  ctx.lineTo(cx + radius * 0.18, cy - radius * 1.16);
  ctx.lineTo(cx + radius * 0.02, cy - radius * 0.55);
  ctx.closePath();
  ctx.fill();

  ctx.fillStyle = "#13080b";
  ctx.beginPath();
  ctx.arc(cx - radius * 0.24, cy - radius * 0.05, radius * 0.1, 0, Math.PI * 2);
  ctx.arc(cx + radius * 0.24, cy - radius * 0.05, radius * 0.1, 0, Math.PI * 2);
  ctx.fill();
}

function stackOffsetFor(oni, index) {
  const stacked = oniList.filter((other) => other.visible && sameCell(other, oni));
  if (stacked.length <= 1) {
    return { x: 0, y: 0 };
  }

  const stackIndex = stacked.findIndex((other) => other.id === oni.id);
  const angle = (Math.PI * 2 * stackIndex) / stacked.length + index * 0.2;
  return {
    x: Math.cos(angle) * cellSize * 0.14,
    y: Math.sin(angle) * cellSize * 0.14,
  };
}

function drawGlow(cx, cy, radius, color) {
  const gradient = ctx.createRadialGradient(cx, cy, 0, cx, cy, radius);
  gradient.addColorStop(0, color);
  gradient.addColorStop(1, "rgba(0, 0, 0, 0)");
  ctx.fillStyle = gradient;
  ctx.beginPath();
  ctx.arc(cx, cy, radius, 0, Math.PI * 2);
  ctx.fill();
}

function drawDarkness() {
  const cx = player.x * cellSize + cellSize / 2;
  const cy = player.y * cellSize + cellSize / 2;
  const radius = cellSize * LIGHT_RADIUS_CELLS;

  const light = ctx.createRadialGradient(cx, cy, 0, cx, cy, radius);
  light.addColorStop(0, "rgba(0, 0, 0, 0)");
  light.addColorStop(0.48, "rgba(0, 0, 0, 0)");
  light.addColorStop(0.72, "rgba(0, 0, 0, 0.42)");
  light.addColorStop(1, "rgba(0, 0, 0, 0.98)");
  ctx.fillStyle = light;
  ctx.fillRect(0, 0, boardWidth, boardHeight);
}

function drawOniRadar(now) {
  ctx.save();
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  oniList.forEach((oni, index) => {
    if (oni.defeated || !oni.visible) {
      return;
    }

    const stackOffset = stackOffsetFor(oni, index);
    const cx = oni.x * cellSize + cellSize / 2 + stackOffset.x;
    const cy = oni.y * cellSize + cellSize / 2 + stackOffset.y;
    const pulse = (Math.sin(now / 180 + index) + 1) / 2;
    const radius = cellSize * (0.42 + pulse * 0.24);

    drawGlow(cx, cy, cellSize * 1.05, "rgba(255, 30, 70, 0.24)");
    ctx.strokeStyle = "rgba(255, 78, 110, 0.95)";
    ctx.lineWidth = Math.max(2, cellSize * 0.06);
    ctx.beginPath();
    ctx.arc(cx, cy, radius, 0, Math.PI * 2);
    ctx.stroke();

    ctx.fillStyle = "#ff4e6e";
    ctx.beginPath();
    ctx.arc(cx, cy, Math.max(3, cellSize * 0.11), 0, Math.PI * 2);
    ctx.fill();
  });
  ctx.restore();
}

function drawShotEffects(now) {
  shotEffects = shotEffects.filter((effect) => effect.until > now);
  ctx.save();
  ctx.lineCap = "round";
  shotEffects.forEach((effect) => {
    const alpha = Math.max(0, (effect.until - now) / 180);
    ctx.strokeStyle = `rgba(255, 226, 134, ${alpha})`;
    ctx.lineWidth = Math.max(2, cellSize * 0.08);
    ctx.beginPath();
    ctx.moveTo(effect.start.x, effect.start.y);
    ctx.lineTo(effect.end.x, effect.end.y);
    ctx.stroke();

    ctx.fillStyle = `rgba(255, 246, 196, ${alpha})`;
    ctx.beginPath();
    ctx.arc(effect.end.x, effect.end.y, cellSize * 0.12, 0, Math.PI * 2);
    ctx.fill();
  });
  ctx.restore();
}

function drawOverlay() {
  if (gameState === "playing") {
    return;
  }

  ctx.fillStyle = gameState === "paused" ? "rgba(5, 7, 8, 0.34)" : "rgba(5, 7, 8, 0.62)";
  ctx.fillRect(0, 0, boardWidth, boardHeight);

  ctx.fillStyle = "#f4f7f1";
  ctx.font = `900 ${Math.max(24, cellSize * 0.9)}px system-ui`;
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  const title = gameState === "won" ? "LEVEL CLEAR" : gameState === "paused" ? "PAUSED" : "CAUGHT";
  ctx.fillText(title, boardWidth / 2, boardHeight / 2 - cellSize * 0.42);

  ctx.fillStyle = gameState === "won" ? "#8fffb5" : gameState === "paused" ? "#fff2c7" : "#ff8ba1";
  ctx.font = `800 ${Math.max(15, cellSize * 0.36)}px system-ui`;
  ctx.fillText(
    gameState === "won" ? "次のレベルをロード中" : gameState === "paused" ? "再開ボタンまたはPキーで続行" : "メニューから同じレベルで再開",
    boardWidth / 2,
    boardHeight / 2 + cellSize * 0.42,
  );
}

function updateMessage(now) {
  if (now < noticeUntil) {
    message.textContent = noticeText;
    message.classList.add("visible");
  } else {
    message.classList.remove("visible");
  }
}

function directionAngle(dir) {
  if (dir === dirs.down) {
    return Math.PI;
  }
  if (dir === dirs.left) {
    return -Math.PI / 2;
  }
  if (dir === dirs.right) {
    return Math.PI / 2;
  }
  return 0;
}

function directionFromVector(dx, dy) {
  if (Math.hypot(dx, dy) < TOUCH_DEAD_ZONE) {
    return null;
  }
  if (Math.abs(dx) > Math.abs(dy)) {
    return dx > 0 ? dirs.right : dirs.left;
  }
  return dy > 0 ? dirs.down : dirs.up;
}

function moveTouchKnob(dx, dy) {
  const maxDistance = Math.min(42, touchPad.getBoundingClientRect().width * 0.3);
  const distance = Math.hypot(dx, dy);
  const scale = distance > maxDistance ? maxDistance / distance : 1;
  touchKnob.style.transform = `translate(-50%, -50%) translate(${dx * scale}px, ${dy * scale}px)`;
}

function clearTouchMove() {
  touchDir = null;
  touchPointerId = null;
  touchKnob.style.transform = "translate(-50%, -50%)";
  const remaining = Array.from(heldKeys.values());
  activeDir = remaining.length > 0 ? remaining[remaining.length - 1] : null;
}

function updateTouchMove(event) {
  if (touchPointerId !== event.pointerId) {
    return;
  }

  event.preventDefault();
  const rect = touchPad.getBoundingClientRect();
  const dx = event.clientX - (rect.left + rect.width / 2);
  const dy = event.clientY - (rect.top + rect.height / 2);
  moveTouchKnob(dx, dy);

  const dir = directionFromVector(dx, dy);
  if (!dir) {
    return;
  }

  activeDir = dir;
  if (touchDir !== dir) {
    touchDir = dir;
    tryMove(dir);
    nextPlayerStep = performance.now() + PLAYER_STEP_MS;
  }
}

function beginTouchMove(event) {
  event.preventDefault();
  touchPointerId = event.pointerId;
  touchPad.setPointerCapture(event.pointerId);
  updateTouchMove(event);
}

window.addEventListener("keydown", (event) => {
  if (event.code === "KeyP" || event.code === "Escape") {
    event.preventDefault();
    togglePause();
    return;
  }

  if (gameState === "paused") {
    event.preventDefault();
    return;
  }

  if (event.code === "KeyF" || event.code === "Enter") {
    event.preventDefault();
    tryShoot();
    return;
  }

  if (event.code === "Space") {
    event.preventDefault();
    tryWallJump();
    return;
  }

  const dir = keyDirs[event.code];
  if (!dir) {
    return;
  }

  event.preventDefault();
  heldKeys.set(event.code, dir);
  activeDir = dir;

  if (!event.repeat) {
    tryMove(dir);
    nextPlayerStep = performance.now() + PLAYER_STEP_MS;
  }
});

window.addEventListener("keyup", (event) => {
  if (!keyDirs[event.code]) {
    return;
  }

  heldKeys.delete(event.code);
  const remaining = Array.from(heldKeys.values());
  activeDir = remaining.length > 0 ? remaining[remaining.length - 1] : null;
});

window.addEventListener("resize", () => {
  if (applyStageLayout() && level) {
    startLevel(level);
    return;
  }
  resizeCanvas();
});

restartButton.addEventListener("click", startRun);
pauseButton.addEventListener("click", togglePause);
retryLevelButton.addEventListener("click", () => startLevel(level));
menuRestartButton.addEventListener("click", startRun);

document.querySelectorAll("[data-move]").forEach((button) => {
  button.addEventListener("click", () => {
    const dir = dirs[button.dataset.move];
    tryMove(dir);
  });
});

document.querySelectorAll("[data-action='jump']").forEach((button) => {
  button.addEventListener("click", tryWallJump);
});
document.querySelectorAll("[data-action='shoot']").forEach((button) => {
  button.addEventListener("click", tryShoot);
});

touchPad.addEventListener("pointerdown", beginTouchMove);
touchPad.addEventListener("pointermove", updateTouchMove);
touchPad.addEventListener("pointerup", clearTouchMove);
touchPad.addEventListener("pointercancel", clearTouchMove);

startRun();
