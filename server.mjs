import http from 'node:http';
import path from 'node:path';
import fs from 'node:fs';
import { mkdir, readFile, rename, unlink, stat } from 'node:fs/promises';
import { createReadStream, createWriteStream } from 'node:fs';
import { finished } from 'node:stream/promises';
import { DatabaseSync } from 'node:sqlite';
import {
  createHash, createHmac, randomBytes, randomUUID, timingSafeEqual, scrypt
} from 'node:crypto';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const PUBLIC_DIR = path.join(__dirname, 'public');
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(__dirname, 'data'));
const UPLOAD_DIR = path.resolve(process.env.UPLOAD_DIR || path.join(DATA_DIR, 'uploads'));
const DB_PATH = path.resolve(process.env.DB_PATH || path.join(DATA_DIR, 'mirafriends.sqlite'));
const PORT = Number(process.env.PORT || 3000);
const NODE_ENV = process.env.NODE_ENV || 'development';
const SESSION_DAYS = 30;
const MAX_JSON_BYTES = 1024 * 1024;
const MAX_IMAGE_BYTES = 12 * 1024 * 1024;
const MAX_VIDEO_BYTES = 80 * 1024 * 1024;
const scryptAsync = promisify(scrypt);

await mkdir(DATA_DIR, { recursive: true });
await mkdir(UPLOAD_DIR, { recursive: true });

const db = new DatabaseSync(DB_PATH);
db.exec(`
  PRAGMA journal_mode = WAL;
  PRAGMA foreign_keys = ON;
  CREATE TABLE IF NOT EXISTS users (
    id TEXT PRIMARY KEY,
    miracode TEXT NOT NULL UNIQUE,
    name TEXT NOT NULL,
    about TEXT NOT NULL DEFAULT '',
    miraculous_id TEXT,
    visibility TEXT NOT NULL DEFAULT 'private' CHECK (visibility IN ('public','private')),
    password_salt TEXT NOT NULL,
    password_hash TEXT NOT NULL,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
  );
  CREATE TABLE IF NOT EXISTS sessions (
    token_hash TEXT PRIMARY KEY,
    user_id TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL,
    created_at INTEGER NOT NULL
  );
  CREATE INDEX IF NOT EXISTS sessions_user_idx ON sessions(user_id);
  CREATE TABLE IF NOT EXISTS friendships (
    id TEXT PRIMARY KEY,
    user_a TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    user_b TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    status TEXT NOT NULL CHECK (status IN ('pending','accepted')),
    requested_by TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    UNIQUE(user_a,user_b),
    CHECK(user_a < user_b)
  );
  CREATE INDEX IF NOT EXISTS friendship_a_idx ON friendships(user_a,status);
  CREATE INDEX IF NOT EXISTS friendship_b_idx ON friendships(user_b,status);
  CREATE TABLE IF NOT EXISTS posts (
    id TEXT PRIMARY KEY,
    author_id TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    text TEXT NOT NULL DEFAULT '',
    visibility TEXT NOT NULL CHECK (visibility IN ('public','friends')),
    media_url TEXT,
    media_type TEXT,
    created_at INTEGER NOT NULL
  );
  CREATE INDEX IF NOT EXISTS posts_created_idx ON posts(created_at DESC);
  CREATE INDEX IF NOT EXISTS posts_author_idx ON posts(author_id,created_at DESC);
  CREATE TABLE IF NOT EXISTS reactions (
    post_id TEXT NOT NULL REFERENCES posts(id) ON DELETE CASCADE,
    user_id TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    emoji TEXT NOT NULL,
    created_at INTEGER NOT NULL,
    PRIMARY KEY(post_id,user_id,emoji)
  );
  CREATE TABLE IF NOT EXISTS comments (
    id TEXT PRIMARY KEY,
    post_id TEXT NOT NULL REFERENCES posts(id) ON DELETE CASCADE,
    user_id TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    text TEXT NOT NULL,
    created_at INTEGER NOT NULL
  );
  CREATE INDEX IF NOT EXISTS comments_post_idx ON comments(post_id,created_at DESC);
  CREATE TABLE IF NOT EXISTS reports (
    id TEXT PRIMARY KEY,
    reporter_id TEXT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    target_type TEXT NOT NULL CHECK(target_type IN ('user','post')),
    target_id TEXT NOT NULL,
    reason TEXT NOT NULL,
    created_at INTEGER NOT NULL
  );
`);

class HttpError extends Error {
  constructor(status, message) { super(message); this.status = status; }
}
const now = () => Date.now();
const hashToken = token => createHash('sha256').update(token).digest('hex');
const cleanText = (value, max) => String(value ?? '').trim().slice(0, max);
const normalizeCode = value => cleanText(value, 24).toUpperCase().replace(/\s+/g, '');
const safeUser = user => ({
  id: user.id, miracode: user.miracode, name: user.name, about: user.about || '',
  miraculousId: user.miraculous_id || null, visibility: user.visibility,
  createdAt: user.created_at
});
const statements = {
  userById: db.prepare('SELECT * FROM users WHERE id = ?'),
  userByCode: db.prepare('SELECT * FROM users WHERE miracode = ?'),
  session: db.prepare('SELECT s.user_id, s.expires_at, u.* FROM sessions s JOIN users u ON u.id=s.user_id WHERE s.token_hash=?'),
  relation: db.prepare('SELECT * FROM friendships WHERE user_a=? AND user_b=?'),
  friends: db.prepare(`SELECT u.*, f.created_at AS friendship_created_at FROM friendships f JOIN users u ON u.id=CASE WHEN f.user_a=? THEN f.user_b ELSE f.user_a END WHERE (f.user_a=? OR f.user_b=?) AND f.status='accepted' ORDER BY u.name COLLATE NOCASE`),
  incoming: db.prepare(`SELECT f.id AS request_id, f.created_at, u.id, u.miracode, u.name, u.about, u.miraculous_id, u.visibility FROM friendships f JOIN users u ON u.id=f.requested_by WHERE (f.user_a=? OR f.user_b=?) AND f.status='pending' AND f.requested_by<>? ORDER BY f.created_at DESC`),
  outgoing: db.prepare(`SELECT f.id AS request_id, f.created_at, u.id, u.miracode, u.name, u.about, u.miraculous_id, u.visibility FROM friendships f JOIN users u ON u.id=CASE WHEN f.user_a=? THEN f.user_b ELSE f.user_a END WHERE (f.user_a=? OR f.user_b=?) AND f.status='pending' AND f.requested_by=? ORDER BY f.created_at DESC`)
};

function makeMiracode() {
  for (let i = 0; i < 30; i++) {
    const code = `MIRA-${randomBytes(9).toString('hex').toUpperCase()}`;
    if (!statements.userByCode.get(code)) return code;
  }
  throw new Error('Não foi possível gerar um Miracode único.');
}
function comparePair(a, b) { return a < b ? [a, b] : [b, a]; }
function friendshipBetween(a, b) {
  const [x, y] = comparePair(a, b);
  return statements.relation.get(x, y) || null;
}
function areFriends(a, b) { return Boolean(friendshipBetween(a, b)?.status === 'accepted'); }
function parseCookies(header = '') {
  const result = {};
  for (const part of header.split(';')) {
    const index = part.indexOf('=');
    if (index < 0) continue;
    const key = part.slice(0, index).trim();
    try { result[key] = decodeURIComponent(part.slice(index + 1).trim()); } catch { /* ignore malformed cookie */ }
  }
  return result;
}
function setSessionCookie(res, token) {
  const secure = NODE_ENV === 'production' ? '; Secure' : '';
  res.setHeader('Set-Cookie', `mf_session=${encodeURIComponent(token)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${SESSION_DAYS * 86400}${secure}`);
}
function clearSessionCookie(res) {
  const secure = NODE_ENV === 'production' ? '; Secure' : '';
  res.setHeader('Set-Cookie', `mf_session=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0${secure}`);
}
function json(res, status, payload, extraHeaders = {}) {
  const body = Buffer.from(JSON.stringify(payload));
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Content-Length': body.length, 'Cache-Control': 'no-store', ...extraHeaders });
  res.end(body);
}
function noContent(res) { res.writeHead(204, { 'Cache-Control': 'no-store' }); res.end(); }
async function readJson(req, maxBytes = MAX_JSON_BYTES) {
  const chunks = []; let size = 0;
  for await (const chunk of req) {
    size += chunk.length;
    if (size > maxBytes) throw new HttpError(413, 'Dados enviados excedem o limite permitido.');
    chunks.push(chunk);
  }
  if (!size) return {};
  try { return JSON.parse(Buffer.concat(chunks).toString('utf8')); }
  catch { throw new HttpError(400, 'JSON inválido.'); }
}
async function currentUser(req) {
  const token = parseCookies(req.headers.cookie).mf_session;
  if (!token) return null;
  const session = statements.session.get(hashToken(token));
  if (!session || session.expires_at < now()) {
    if (session) db.prepare('DELETE FROM sessions WHERE token_hash=?').run(hashToken(token));
    return null;
  }
  return session;
}
function requireUser(user) { if (!user) throw new HttpError(401, 'Entre na sua conta Mirafriends para continuar.'); return user; }
function sameOrigin(req) {
  const origin = req.headers.origin;
  if (!origin) return;
  let host;
  try { host = new URL(origin).host; } catch { throw new HttpError(403, 'Origem da solicitação inválida.'); }
  const expectedHost = req.headers['x-forwarded-host'] || req.headers.host;
  if (host !== expectedHost) throw new HttpError(403, 'Solicitação de outra origem bloqueada.');
}
const rateBuckets = new Map();
function rateLimit(req, key, limit, windowMs) {
  const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'local').split(',')[0].trim();
  const id = `${key}:${ip}`; const time = now();
  let bucket = rateBuckets.get(id);
  if (!bucket || bucket.until < time) bucket = { count: 0, until: time + windowMs };
  bucket.count += 1; rateBuckets.set(id, bucket);
  if (bucket.count > limit) throw new HttpError(429, 'Muitas tentativas. Aguarde um pouco e tente novamente.');
  if (rateBuckets.size > 5000) for (const [k, v] of rateBuckets) if (v.until < time) rateBuckets.delete(k);
}
async function hashPassword(password, salt = randomBytes(16).toString('hex')) {
  const derived = await scryptAsync(password, salt, 64, { N: 1 << 15, r: 8, p: 1, maxmem: 64 * 1024 * 1024 });
  return { salt, hash: Buffer.from(derived).toString('hex') };
}
async function verifyPassword(password, salt, expectedHex) {
  const derived = await scryptAsync(password, salt, 64, { N: 1 << 15, r: 8, p: 1, maxmem: 64 * 1024 * 1024 });
  const actual = Buffer.from(derived); const expected = Buffer.from(expectedHex, 'hex');
  return actual.length === expected.length && timingSafeEqual(actual, expected);
}
function createSession(userId, res) {
  const token = randomBytes(32).toString('base64url');
  db.prepare('INSERT INTO sessions(token_hash,user_id,expires_at,created_at) VALUES(?,?,?,?)').run(hashToken(token), userId, now() + SESSION_DAYS * 86400000, now());
  setSessionCookie(res, token);
}
function mediaTypeFromContentType(value) {
  const type = String(value || '').split(';')[0].trim().toLowerCase();
  const map = new Map([
    ['image/jpeg', ['jpg', MAX_IMAGE_BYTES]], ['image/png', ['png', MAX_IMAGE_BYTES]], ['image/webp', ['webp', MAX_IMAGE_BYTES]],
    ['video/mp4', ['mp4', MAX_VIDEO_BYTES]], ['video/quicktime', ['mov', MAX_VIDEO_BYTES]], ['video/webm', ['webm', MAX_VIDEO_BYTES]]
  ]);
  return map.get(type) ? { type, ext: map.get(type)[0], limit: map.get(type)[1], mediaType: type.startsWith('image/') ? 'image' : 'video' } : null;
}
function validMediaMagic(header, type) {
  if (type === 'image/jpeg') return header.length >= 3 && header[0] === 0xff && header[1] === 0xd8 && header[2] === 0xff;
  if (type === 'image/png') return header.subarray(0, 8).equals(Buffer.from([137,80,78,71,13,10,26,10]));
  if (type === 'image/webp') return header.length >= 12 && header.toString('ascii', 0, 4) === 'RIFF' && header.toString('ascii', 8, 12) === 'WEBP';
  if (type === 'video/mp4' || type === 'video/quicktime') return header.length >= 12 && header.toString('ascii', 4, 8) === 'ftyp';
  if (type === 'video/webm') return header.length >= 4 && header.subarray(0, 4).equals(Buffer.from([0x1a,0x45,0xdf,0xa3]));
  return false;
}
async function saveRawUpload(req, typeInfo) {
  const tempName = `${randomUUID()}.upload`;
  const tempPath = path.join(UPLOAD_DIR, tempName);
  const output = createWriteStream(tempPath, { flags: 'wx', mode: 0o640 });
  let total = 0; let head = Buffer.alloc(0);
  try {
    for await (const raw of req) {
      const chunk = Buffer.from(raw); total += chunk.length;
      if (total > typeInfo.limit) throw new HttpError(413, typeInfo.mediaType === 'video' ? 'Vídeo excede o limite de 80 MB.' : 'Imagem excede o limite de 12 MB.');
      if (head.length < 32) head = Buffer.concat([head, chunk.subarray(0, 32 - head.length)]);
      if (!output.write(chunk)) await new Promise((resolve, reject) => { output.once('drain', resolve); output.once('error', reject); });
    }
    output.end(); await finished(output);
    if (!total || !validMediaMagic(head, typeInfo.type)) throw new HttpError(415, 'O arquivo não corresponde ao tipo de mídia informado.');
    const fileName = `${randomUUID()}.${typeInfo.ext}`;
    await rename(tempPath, path.join(UPLOAD_DIR, fileName));
    return { url: `/uploads/${fileName}`, mediaType: typeInfo.mediaType, size: total };
  } catch (error) {
    output.destroy(); await unlink(tempPath).catch(() => {}); throw error;
  }
}
function isPostVisible(post, viewerId) {
  if (post.author_id === viewerId) return true;
  if (post.visibility === 'public') {
    const author = statements.userById.get(post.author_id);
    if (author?.visibility === 'public') return true;
  }
  return areFriends(post.author_id, viewerId);
}
function postView(post, viewerId) {
  const author = statements.userById.get(post.author_id);
  const reactionCount = db.prepare('SELECT COUNT(*) AS count FROM reactions WHERE post_id=?').get(post.id).count;
  const reacted = Boolean(db.prepare('SELECT 1 FROM reactions WHERE post_id=? AND user_id=? AND emoji=?').get(post.id, viewerId, '❤️'));
  const viewerCanSeeFriendsComments = post.author_id === viewerId || areFriends(post.author_id, viewerId);
  const comments = viewerCanSeeFriendsComments
    ? db.prepare(`SELECT c.id,c.text,c.created_at,u.id AS user_id,u.name,u.miracode FROM comments c JOIN users u ON u.id=c.user_id WHERE c.post_id=? AND (c.user_id=? OR EXISTS(SELECT 1 FROM friendships f WHERE f.status='accepted' AND ((f.user_a=c.user_id AND f.user_b=?) OR (f.user_b=c.user_id AND f.user_a=?)))) ORDER BY c.created_at DESC LIMIT 8`).all(post.id, post.author_id, post.author_id, post.author_id).reverse().map(c => ({ id: c.id, text: c.text, createdAt: c.created_at, author: { id: c.user_id, name: c.name, miracode: c.miracode } }))
    : []; 
  return { id: post.id, author: author ? { id: author.id, miracode: author.miracode, name: author.name, miraculousId: author.miraculous_id } : null, text: post.text, visibility: post.visibility, mediaUrl: post.media_url, mediaType: post.media_type, createdAt: post.created_at, reactionCount, reacted, comments, commentCount: viewerCanSeeFriendsComments ? db.prepare('SELECT COUNT(*) AS count FROM comments WHERE post_id=?').get(post.id).count : 0, own: post.author_id === viewerId };
}
function createFriendship(a, b, status, requestedBy) {
  const [user_a, user_b] = comparePair(a, b);
  const old = statements.relation.get(user_a, user_b);
  if (old) {
    if (old.status === 'pending' && status === 'accepted') db.prepare('UPDATE friendships SET status=\'accepted\', updated_at=? WHERE id=?').run(now(), old.id);
    return statements.relation.get(user_a, user_b);
  }
  const id = randomUUID(); const time = now();
  db.prepare('INSERT INTO friendships(id,user_a,user_b,status,requested_by,created_at,updated_at) VALUES(?,?,?,?,?,?,?)').run(id, user_a, user_b, status, requestedBy, time, time);
  return statements.relation.get(user_a, user_b);
}
function checkAndGetFriendship(postId, userId) {
  const post = db.prepare('SELECT * FROM posts WHERE id=?').get(postId);
  if (!post) throw new HttpError(404, 'Publicação não encontrada.');
  if (!isPostVisible(post, userId)) throw new HttpError(403, 'Você não tem permissão para ver esta publicação.');
  if (post.author_id !== userId && !areFriends(post.author_id, userId)) throw new HttpError(403, 'Somente amigos aceitos podem reagir ou comentar.');
  return post;
}

const MIME = new Map([
  ['.html','text/html; charset=utf-8'],['.css','text/css; charset=utf-8'],['.js','text/javascript; charset=utf-8'],['.mjs','text/javascript; charset=utf-8'],['.json','application/json; charset=utf-8'],['.webmanifest','application/manifest+json'],['.svg','image/svg+xml'],['.png','image/png'],['.jpg','image/jpeg'],['.jpeg','image/jpeg'],['.webp','image/webp'],['.mp4','video/mp4'],['.mov','video/quicktime'],['.webm','video/webm'],['.txt','text/plain; charset=utf-8'],['.md','text/markdown; charset=utf-8']
]);
async function serveFile(req, res, filePath, isUpload = false) {
  let info;
  try { info = await stat(filePath); } catch { throw new HttpError(404, 'Arquivo não encontrado.'); }
  if (!info.isFile()) throw new HttpError(404, 'Arquivo não encontrado.');
  const ext = path.extname(filePath).toLowerCase();
  const headers = {
    'Content-Type': MIME.get(ext) || 'application/octet-stream',
    'X-Content-Type-Options': 'nosniff',
    'Accept-Ranges': 'bytes',
    'Cache-Control': isUpload ? 'private, no-store' : (ext === '.html' ? 'no-store' : 'public, max-age=3600'),
    ...(isUpload ? { 'Vary': 'Cookie' } : {})
  };
  if (req.headers.range && isUpload) {
    const match = /^bytes=(\d*)-(\d*)$/.exec(req.headers.range);
    if (!match) { res.writeHead(416, { 'Content-Range': `bytes */${info.size}` }); res.end(); return; }
    let start = match[1] ? Number(match[1]) : 0;
    let end = match[2] ? Number(match[2]) : info.size - 1;
    if (!match[1] && match[2]) { const suffix = Number(match[2]); start = Math.max(0, info.size - suffix); end = info.size - 1; }
    if (start > end || end >= info.size) { res.writeHead(416, { 'Content-Range': `bytes */${info.size}` }); res.end(); return; }
    headers['Content-Range'] = `bytes ${start}-${end}/${info.size}`;
    headers['Content-Length'] = end - start + 1;
    res.writeHead(206, headers);
    if (req.method === 'HEAD') return res.end();
    createReadStream(filePath, { start, end }).pipe(res); return;
  }
  headers['Content-Length'] = info.size;
  res.writeHead(200, headers);
  if (req.method === 'HEAD') return res.end();
  createReadStream(filePath).pipe(res);
}

async function handleApi(req, res, url) {
  const pathname = url.pathname;
  const method = req.method;
  if (method !== 'GET' && method !== 'HEAD') sameOrigin(req);

  if (method === 'GET' && pathname === '/api/health') return json(res, 200, { ok: true, service: 'mirafriends-node', version: '2.3.0', time: now() });

  if (method === 'POST' && pathname === '/api/auth/register') {
    rateLimit(req, 'register', 6, 60 * 60 * 1000);
    const body = await readJson(req);
    const name = cleanText(body.name, 24); const password = String(body.password || '');
    const visibility = body.visibility === 'public' ? 'public' : 'private';
    if (name.length < 2) throw new HttpError(400, 'Digite um nome com pelo menos 2 caracteres.');
    if (password.length < 8 || password.length > 128) throw new HttpError(400, 'A senha deve ter entre 8 e 128 caracteres.');
    const id = `usr_${randomUUID()}`; const miracode = makeMiracode(); const { salt, hash } = await hashPassword(password);
    const time = now();
    db.prepare('INSERT INTO users(id,miracode,name,about,miraculous_id,visibility,password_salt,password_hash,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?)').run(id, miracode, name, cleanText(body.about,120), cleanText(body.miraculousId,32) || null, visibility, salt, hash, time, time);
    createSession(id, res);
    return json(res, 201, { user: safeUser(statements.userById.get(id)) });
  }

  if (method === 'POST' && pathname === '/api/auth/login') {
    rateLimit(req, 'login', 12, 15 * 60 * 1000);
    const body = await readJson(req); const code = normalizeCode(body.miracode); const password = String(body.password || '');
    const user = statements.userByCode.get(code);
    if (!user || !(await verifyPassword(password, user.password_salt, user.password_hash))) throw new HttpError(401, 'Miracode ou senha incorretos.');
    createSession(user.id, res);
    return json(res, 200, { user: safeUser(user) });
  }

  const user = requireUser(await currentUser(req));
  if (method === 'GET' && pathname === '/api/me') return json(res, 200, { user: safeUser(user) });
  if (method === 'POST' && pathname === '/api/auth/logout') {
    const token = parseCookies(req.headers.cookie).mf_session;
    if (token) db.prepare('DELETE FROM sessions WHERE token_hash=?').run(hashToken(token));
    clearSessionCookie(res); return noContent(res);
  }
  if (method === 'PATCH' && pathname === '/api/me') {
    const body = await readJson(req);
    const name = body.name === undefined ? user.name : cleanText(body.name,24);
    const about = body.about === undefined ? user.about : cleanText(body.about,120);
    const visibility = body.visibility === 'public' || body.visibility === 'private' ? body.visibility : user.visibility;
    const miraculousId = body.miraculousId === undefined ? user.miraculous_id : cleanText(body.miraculousId,32) || null;
    if (name.length < 2) throw new HttpError(400, 'O nome precisa ter pelo menos 2 caracteres.');
    db.prepare('UPDATE users SET name=?,about=?,visibility=?,miraculous_id=?,updated_at=? WHERE id=?').run(name,about,visibility,miraculousId,now(),user.id);
    return json(res,200,{user:safeUser(statements.userById.get(user.id))});
  }

  const lookupMatch = pathname.match(/^\/api\/users\/by-code\/([^/]+)$/);
  if (method === 'GET' && lookupMatch) {
    rateLimit(req, 'lookup-code', 120, 60 * 60 * 1000);
    const code = normalizeCode(decodeURIComponent(lookupMatch[1])); const target = statements.userByCode.get(code);
    if (!target) throw new HttpError(404,'Nenhuma conta foi encontrada com esse Miracode.');
    if (target.id === user.id) return json(res,200,{user:safeUser(target),relation:'self'});
    const rel = friendshipBetween(user.id,target.id);
    return json(res,200,{user:{id:target.id,miracode:target.miracode,name:target.name,visibility:target.visibility,miraculousId:target.miraculous_id,about:target.visibility==='public'||rel?.status==='accepted'?target.about:''},relation:rel?.status||'none',requestedBy:rel?.requested_by||null});
  }

  const connectMatch = pathname.match(/^\/api\/friendships\/by-code\/([^/]+)$/);
  if (method === 'POST' && connectMatch) {
    rateLimit(req, 'friend-add', 40, 60 * 60 * 1000);
    const code = normalizeCode(decodeURIComponent(connectMatch[1])); const target = statements.userByCode.get(code);
    if (!target) throw new HttpError(404,'Miracode não encontrado.');
    if (target.id === user.id) throw new HttpError(400,'Este é o seu próprio Miracode.');
    const old = friendshipBetween(user.id,target.id);
    if (old?.status === 'accepted') return json(res,200,{status:'accepted',message:'Esta pessoa já está na sua lista de amigos.'});
    if (old?.status === 'pending') {
      if (target.visibility === 'public' || old.requested_by !== user.id) {
        db.prepare('UPDATE friendships SET status=\'accepted\',updated_at=? WHERE id=?').run(now(),old.id);
        return json(res,200,{status:'accepted',message:'Solicitação recíproca aceita; vocês agora são amigos.'});
      }
      return json(res,200,{status:'pending',message:'Sua solicitação já foi enviada.'});
    }
    const status = target.visibility === 'public' ? 'accepted' : 'pending';
    createFriendship(user.id,target.id,status,user.id);
    return json(res,status==='accepted'?201:202,{status,message:status==='accepted'?'Conta pública adicionada aos seus amigos.':'Solicitação enviada; a pessoa precisa aceitar.'});
  }

  if (method === 'GET' && pathname === '/api/friendships') {
    const rows = statements.friends.all(user.id,user.id,user.id);
    return json(res,200,{friends:rows.map(row=>({id:row.id,miracode:row.miracode,name:row.name,about:row.about,miraculousId:row.miraculous_id,visibility:row.visibility,addedAt:row.friendship_created_at}))});
  }
  if (method === 'GET' && pathname === '/api/friend-requests') {
    const incoming = statements.incoming.all(user.id,user.id,user.id).map(row=>({id:row.request_id,createdAt:row.created_at,user:{id:row.id,miracode:row.miracode,name:row.name,about:row.about,miraculousId:row.miraculous_id,visibility:row.visibility}}));
    const outgoing = statements.outgoing.all(user.id,user.id,user.id,user.id).map(row=>({id:row.request_id,createdAt:row.created_at,user:{id:row.id,miracode:row.miracode,name:row.name,about:row.about,miraculousId:row.miraculous_id,visibility:row.visibility}}));
    return json(res,200,{incoming,outgoing});
  }
  const requestMatch = pathname.match(/^\/api\/friend-requests\/([^/]+)\/(accept|decline)$/);
  if (method === 'POST' && requestMatch) {
    const [,requestId,decision] = requestMatch;
    const request = db.prepare('SELECT * FROM friendships WHERE id=? AND status=\'pending\'').get(requestId);
    if (!request || (request.user_a!==user.id && request.user_b!==user.id) || request.requested_by===user.id) throw new HttpError(404,'Solicitação não encontrada.');
    if (decision==='accept') db.prepare('UPDATE friendships SET status=\'accepted\',updated_at=? WHERE id=?').run(now(),requestId);
    else db.prepare('DELETE FROM friendships WHERE id=?').run(requestId);
    return json(res,200,{status:decision==='accept'?'accepted':'declined'});
  }
  const removeFriendMatch = pathname.match(/^\/api\/friendships\/([^/]+)$/);
  if (method === 'DELETE' && removeFriendMatch) {
    const target = removeFriendMatch[1]; const [a,b] = comparePair(user.id,target);
    db.prepare('DELETE FROM friendships WHERE user_a=? AND user_b=?').run(a,b);
    return noContent(res);
  }

  if (method === 'GET' && pathname === '/api/feed') {
    const limit = Math.max(1,Math.min(40,Number(url.searchParams.get('limit'))||25));
    const before = Number(url.searchParams.get('before'))||now()+1;
    const rows = db.prepare(`SELECT p.* FROM posts p JOIN users author ON author.id=p.author_id
      WHERE p.created_at < ? AND (
        p.author_id=? OR
        (p.visibility='public' AND author.visibility='public') OR
        EXISTS(SELECT 1 FROM friendships f WHERE f.status='accepted' AND ((f.user_a=p.author_id AND f.user_b=?) OR (f.user_b=p.author_id AND f.user_a=?)))
      ) ORDER BY p.created_at DESC LIMIT ?`).all(before,user.id,user.id,user.id,limit);
    return json(res,200,{posts:rows.map(post=>postView(post,user.id))});
  }
  if (method === 'POST' && pathname === '/api/posts') {
    rateLimit(req, `post:${user.id}`, 30, 60 * 60 * 1000);
    const body = await readJson(req); const text = cleanText(body.text,600);
    if (!text && !body.wantsMedia) throw new HttpError(400,'Escreva algo ou adicione uma mídia.');
    let visibility = body.visibility === 'public' ? 'public' : 'friends';
    if (user.visibility !== 'public') visibility = 'friends';
    const id = `pst_${randomUUID()}`;
    db.prepare('INSERT INTO posts(id,author_id,text,visibility,created_at) VALUES(?,?,?,?,?)').run(id,user.id,text,visibility,now());
    return json(res,201,{post:postView(db.prepare('SELECT * FROM posts WHERE id=?').get(id),user.id)});
  }
  const mediaMatch = pathname.match(/^\/api\/posts\/([^/]+)\/media$/);
  if ((method==='POST'||method==='PUT') && mediaMatch) {
    const post = db.prepare('SELECT * FROM posts WHERE id=? AND author_id=?').get(mediaMatch[1],user.id);
    if (!post) throw new HttpError(404,'Publicação não encontrada.');
    if (post.media_url) throw new HttpError(409,'Esta publicação já tem uma mídia.');
    rateLimit(req, `upload:${user.id}`, 25, 24 * 60 * 60 * 1000);
    const typeInfo = mediaTypeFromContentType(req.headers['content-type']);
    if (!typeInfo) throw new HttpError(415,'Formato não permitido. Use JPG, PNG, WebP, MP4, MOV ou WebM.');
    const saved = await saveRawUpload(req,typeInfo);
    db.prepare('UPDATE posts SET media_url=?,media_type=? WHERE id=?').run(saved.url,saved.mediaType,post.id);
    return json(res,201,{post:postView(db.prepare('SELECT * FROM posts WHERE id=?').get(post.id),user.id),media:saved});
  }
  const reactionMatch = pathname.match(/^\/api\/posts\/([^/]+)\/reactions$/);
  if (method==='POST' && reactionMatch) {
    const post = checkAndGetFriendship(reactionMatch[1],user.id); const body = await readJson(req); const emoji = body.emoji === '✨' ? '✨' : '❤️';
    const old = db.prepare('SELECT 1 FROM reactions WHERE post_id=? AND user_id=? AND emoji=?').get(post.id,user.id,emoji);
    if (old) db.prepare('DELETE FROM reactions WHERE post_id=? AND user_id=? AND emoji=?').run(post.id,user.id,emoji);
    else db.prepare('INSERT INTO reactions(post_id,user_id,emoji,created_at) VALUES(?,?,?,?)').run(post.id,user.id,emoji,now());
    return json(res,200,{post:postView(db.prepare('SELECT * FROM posts WHERE id=?').get(post.id),user.id)});
  }
  const commentMatch = pathname.match(/^\/api\/posts\/([^/]+)\/comments$/);
  if (method==='POST' && commentMatch) {
    const post = checkAndGetFriendship(commentMatch[1],user.id); const body = await readJson(req); const text = cleanText(body.text,240);
    if (text.length<1) throw new HttpError(400,'O comentário não pode ficar vazio.');
    const id = `cmt_${randomUUID()}`; db.prepare('INSERT INTO comments(id,post_id,user_id,text,created_at) VALUES(?,?,?,?,?)').run(id,post.id,user.id,text,now());
    return json(res,201,{post:postView(db.prepare('SELECT * FROM posts WHERE id=?').get(post.id),user.id)});
  }
  const deletePostMatch = pathname.match(/^\/api\/posts\/([^/]+)$/);
  if (method==='DELETE' && deletePostMatch) {
    const post = db.prepare('SELECT * FROM posts WHERE id=? AND author_id=?').get(deletePostMatch[1],user.id);
    if (!post) throw new HttpError(404,'Publicação não encontrada.');
    if (post.media_url?.startsWith('/uploads/')) await unlink(path.join(UPLOAD_DIR,path.basename(post.media_url))).catch(()=>{});
    db.prepare('DELETE FROM posts WHERE id=?').run(post.id); return noContent(res);
  }

  if (method === 'POST' && pathname === '/api/reports') {
    const body = await readJson(req); const targetType = body.targetType === 'post' ? 'post' : 'user';
    const targetId = cleanText(body.targetId,80); const reason = cleanText(body.reason,240);
    if (!targetId || reason.length < 4) throw new HttpError(400,'Informe o conteúdo e uma razão breve para a denúncia.');
    db.prepare('INSERT INTO reports(id,reporter_id,target_type,target_id,reason,created_at) VALUES(?,?,?,?,?,?)').run(randomUUID(),user.id,targetType,targetId,reason,now());
    return json(res,201,{submitted:true});
  }

  throw new HttpError(404,'Rota da API não encontrada.');
}

function setSecurityHeaders(res) {
  res.setHeader('X-Content-Type-Options','nosniff');
  res.setHeader('Referrer-Policy','strict-origin-when-cross-origin');
  res.setHeader('X-Frame-Options','DENY');
  res.setHeader('Permissions-Policy','camera=(self), microphone=(self), geolocation=()');
  res.setHeader('Content-Security-Policy',"default-src 'self'; img-src 'self' data: blob:; media-src 'self' blob:; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src 'self' data: https://fonts.gstatic.com; connect-src 'self'; object-src 'none'; base-uri 'self'; frame-ancestors 'none'");
}

const server = http.createServer(async (req,res) => {
  setSecurityHeaders(res);
  try {
    const url = new URL(req.url,'http://localhost');
    if (url.pathname.startsWith('/api/')) return await handleApi(req,res,url);
    if (req.method !== 'GET' && req.method !== 'HEAD') throw new HttpError(405,'Método não permitido.');
    if (url.pathname.startsWith('/uploads/')) {
      const name = path.basename(decodeURIComponent(url.pathname.slice('/uploads/'.length)));
      if (!/^[a-f0-9-]+\.(?:jpg|png|webp|mp4|mov|webm)$/i.test(name)) throw new HttpError(404,'Arquivo não encontrado.');
      const mediaPath=`/uploads/${name}`;
      const post=db.prepare('SELECT * FROM posts WHERE media_url=?').get(mediaPath);
      if(!post)throw new HttpError(404,'Mídia não encontrada.');
      const viewer=await currentUser(req);
      if(!viewer)throw new HttpError(401,'Entre na sua conta para visualizar esta mídia.');
      if(!isPostVisible(post,viewer.id))throw new HttpError(403,'Você não tem permissão para visualizar esta mídia.');
      return await serveFile(req,res,path.join(UPLOAD_DIR,name),true);
    }
    let relative = decodeURIComponent(url.pathname);
    if (relative === '/') relative = '/index.html';
    const resolved = path.resolve(PUBLIC_DIR, `.${relative}`);
    if (!resolved.startsWith(PUBLIC_DIR + path.sep) && resolved !== path.join(PUBLIC_DIR,'index.html')) throw new HttpError(403,'Caminho inválido.');
    return await serveFile(req,res,resolved,false);
  } catch (error) {
    if (res.headersSent) { res.destroy(); return; }
    const status = error instanceof HttpError ? error.status : 500;
    if (status >= 500) console.error(error);
    return json(res,status,{error:status>=500?'Erro interno do servidor.':error.message});
  }
});

server.listen(PORT,'0.0.0.0',()=>console.log(`Mirafriends Node online em http://localhost:${PORT}`));
for (const signal of ['SIGINT','SIGTERM']) process.on(signal,()=>{ console.log(`Recebido ${signal}; encerrando.`); server.close(()=>{ db.close(); process.exit(0); }); });
