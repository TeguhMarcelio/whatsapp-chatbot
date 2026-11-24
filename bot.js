import makeWASocket, { 
  DisconnectReason, 
  useMultiFileAuthState, 
  downloadMediaMessage 
} from '@whiskeysockets/baileys';
import { GoogleGenAI, Type } from '@google/genai';
import qrcode from 'qrcode-terminal';
import pino from 'pino';
import fs from 'fs/promises';
import path from 'path';
import { execFile, spawn } from 'child_process';
import { promisify } from 'util';
import AdmZip from 'adm-zip';

const execFileAsync = promisify(execFile);

// Load environment variables from .env (if present)
try {
  process.loadEnvFile();
} catch {
  // Ignore if .env is not present and variables are provided by the environment
}

const GEMINI_API_KEY = process.env.GEMINI_API_KEY;
if (!GEMINI_API_KEY) {
  console.error('Error: GEMINI_API_KEY belum diatur. Tambahkan di file .env atau environment variable.');
  process.exit(1);
}

// Setup Gemini API Client (SDK @google/genai)
const ai = new GoogleGenAI({ apiKey: GEMINI_API_KEY });

const SAVED_CHATS_DIR = path.join(process.cwd(), 'saved_chats');
const DAILY_LOGS_DIR = path.join(process.cwd(), 'daily_logs');

// In-memory full conversation storage per nomor WA / grup
// Struktur: remoteJid -> Array of { role: 'user' | 'model', parts: [...] }
const conversationSessions = new Map();

// Buffer riwayat chat terbaru (termasuk pesan non-command) untuk konteks reply & percakapan
// Struktur: remoteJid -> Array of { sender: string, text: string, time: string }
const recentChatBuffer = new Map();
const MAX_RECENT_CHAT = 25;

// Cache nama kontak/user (normalizedJid -> nama) & metadata grup
const knownContacts = new Map();
const fetchedGroups = new Set();
const groupNames = new Map(); // groupJid -> groupName (subject)
const groupParticipants = new Map(); // groupJid -> Set<normalizedJid>

function normalizeJid(jid) {
  return jid ? jid.replace(/:\d+@/, '@') : '';
}

function isOwnerJid(jid) {
  const allowedOwners = (process.env.OWNER_NUMBER || '')
    .split(',')
    .map((n) => n.replace(/\D/g, ''))
    .filter(Boolean);
  if (allowedOwners.length === 0) return false;
  const senderNum = normalizeJid(jid).split('@')[0].replace(/\D/g, '');
  return allowedOwners.includes(senderNum);
}

function isGroupMember(groupJid, userJid) {
  const members = groupParticipants.get(groupJid);
  if (!members || members.size === 0) return false;
  return members.has(normalizeJid(userJid));
}

function cacheGroupMetadata(meta) {
  if (!meta?.id) return;
  if (meta.subject) {
    groupNames.set(meta.id, meta.subject);
  }
  const memberSet = new Set();
  for (const p of meta.participants || []) {
    const normId = normalizeJid(p.id);
    const normLid = normalizeJid(p.lid);
    if (normId) memberSet.add(normId);
    if (normLid) memberSet.add(normLid);

    const pName = p.notify || p.name;
    if (pName) {
      if (normId) knownContacts.set(normId, pName);
      if (normLid) knownContacts.set(normLid, pName);
    }
  }
  if (memberSet.size > 0) {
    groupParticipants.set(meta.id, memberSet);
  }
}

function resolveContactName(jid, fallback = 'User') {
  const norm = normalizeJid(jid);
  if (!norm) return fallback;
  return knownContacts.get(norm) || norm.split('@')[0] || fallback;
}

async function ensureGroupContactsLoaded(sock, remoteJid, targetJids = []) {
  if (!remoteJid?.endsWith('@g.us')) return;
  const hasUnknown = targetJids.some((j) => {
    const norm = normalizeJid(j);
    return norm && !knownContacts.has(norm);
  });
  const needsGroupName = !groupNames.has(remoteJid);
  if ((!hasUnknown && !needsGroupName) || fetchedGroups.has(remoteJid)) return;

  try {
    fetchedGroups.add(remoteJid);
    const meta = await sock.groupMetadata(remoteJid);
    cacheGroupMetadata(meta);
  } catch (e) {
    console.warn('[GroupContacts] Gagal memuat metadata grup:', e.message);
  }
}

function replaceMentionsWithNames(text, mentionedJids = [], botJids = []) {
  if (!text || !Array.isArray(mentionedJids) || mentionedJids.length === 0) return text;
  let result = text;
  for (const rawJid of mentionedJids) {
    const norm = normalizeJid(rawJid);
    if (!norm || botJids.includes(norm)) continue;
    const num = norm.split('@')[0];
    const name = resolveContactName(norm, num);
    if (num && name && name !== num) {
      result = result.replace(new RegExp(`@${num}\\b`, 'g'), `@${name}`);
    }
  }
  return result;
}

// Format tanggal: MM-DD-YYYY (Bulan-Hari-Tahun)
function getDateKey(date = new Date()) {
  const mm = String(date.getMonth() + 1).padStart(2, '0');
  const dd = String(date.getDate()).padStart(2, '0');
  const yyyy = date.getFullYear();
  return `${mm}-${dd}-${yyyy}`;
}

function getCurrentDateTimeInfo() {
  const now = new Date();
  const dateKey = getDateKey(now);
  const dayName = now.toLocaleDateString('id-ID', { weekday: 'long' });
  const timeStr = now.toLocaleTimeString('id-ID', {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hour12: false
  });
  return {
    dateKey,
    dayName,
    time: timeStr,
    formatted: `${dayName}, ${dateKey} ${timeStr}`
  };
}

let dailySaveQueue = Promise.resolve();

function saveDailyLog(remoteJid) {
  dailySaveQueue = dailySaveQueue.then(async () => {
    try {
      await fs.mkdir(DAILY_LOGS_DIR, { recursive: true });
      const todayKey = getDateKey();
      const filePath = path.join(DAILY_LOGS_DIR, `${todayKey}.json`);

      let data = { date: todayKey, chats: {} };
      try {
        const raw = await fs.readFile(filePath, 'utf-8');
        const parsed = JSON.parse(raw);
        if (parsed && typeof parsed === 'object' && parsed.chats) {
          data = parsed;
        }
      } catch {}

      const existingGroupName = data.chats[remoteJid]?.groupName;
      const groupName = remoteJid.endsWith('@g.us')
        ? (groupNames.get(remoteJid) || existingGroupName || undefined)
        : undefined;

      data.chats[remoteJid] = {
        ...(groupName ? { groupName } : {}),
        history: conversationSessions.get(remoteJid) || [],
        recentChat: recentChatBuffer.get(remoteJid) || [],
        updatedAt: new Date().toISOString()
      };

      await fs.writeFile(filePath, JSON.stringify(data, null, 2), 'utf-8');
    } catch (err) {
      console.error('[DailyLog] Gagal auto-save:', err.message);
    }
  });
  return dailySaveQueue;
}

async function loadTodayDailyLog() {
  try {
    const todayKey = getDateKey();
    const filePath = path.join(DAILY_LOGS_DIR, `${todayKey}.json`);
    const raw = await fs.readFile(filePath, 'utf-8');
    const parsed = JSON.parse(raw);

    if (parsed?.chats && typeof parsed.chats === 'object') {
      let count = 0;
      for (const [jid, chatData] of Object.entries(parsed.chats)) {
        if (chatData.groupName && jid.endsWith('@g.us')) {
          groupNames.set(jid, chatData.groupName);
        }
        if (Array.isArray(chatData.history)) {
          conversationSessions.set(jid, chatData.history);
        }
        if (Array.isArray(chatData.recentChat)) {
          recentChatBuffer.set(jid, chatData.recentChat);
        }
        count++;
      }
      console.log(`[DailyLog] Auto-loaded ${count} chat session(s) dari ${todayKey}.json`);
    }
  } catch (err) {
    if (err.code !== 'ENOENT') {
      console.error('[DailyLog] Gagal load log hari ini:', err.message);
    }
  }
}

async function readDailyLogForDate(dateKey, remoteJid) {
  const safeDate = String(dateKey || '').replace(/[^0-9-]/g, '');
  const filePath = path.join(DAILY_LOGS_DIR, `${safeDate}.json`);
  try {
    const raw = await fs.readFile(filePath, 'utf-8');
    const parsed = JSON.parse(raw);
    const chatData = parsed?.chats?.[remoteJid];
    if (!chatData) {
      return {
        found: false,
        date: safeDate,
        message: `File ${safeDate}.json ada, tapi tidak ada riwayat chat untuk ruang chat ini pada tanggal tersebut.`
      };
    }
    return {
      found: true,
      date: safeDate,
      history: chatData.history || [],
      recentChat: chatData.recentChat || []
    };
  } catch (err) {
    if (err.code === 'ENOENT') {
      let availableDates = [];
      try {
        const files = await fs.readdir(DAILY_LOGS_DIR);
        availableDates = files.filter((f) => f.endsWith('.json')).map((f) => f.replace(/\.json$/, ''));
      } catch {}
      return {
        found: false,
        date: safeDate,
        availableDates,
        message: `Tidak ditemukan file save untuk tanggal ${safeDate}.`
      };
    }
    return { found: false, date: safeDate, error: err.message };
  }
}

async function refreshParticipatingGroups(sock) {
  if (!sock || typeof sock.groupFetchAllParticipating !== 'function') return;
  try {
    const groups = await sock.groupFetchAllParticipating();
    for (const meta of Object.values(groups || {})) {
      cacheGroupMetadata(meta);
    }
  } catch (e) {
    console.warn('[GroupLookup] Gagal memuat daftar grup:', e.message);
  }
}

async function getGroupChatHistory(args, sock, senderJid) {
  const query = String(args?.group_name || '').trim();
  const requestedDate = args?.date ? String(args.date).replace(/[^0-9-]/g, '') : '';
  const todayKey = getDateKey();
  const targetDate = requestedDate || todayKey;

  // Pastikan metadata grup termuat dari WhatsApp jika belum ada
  if (groupNames.size === 0 || (query && ![...groupNames.values()].some((n) => n.toLowerCase().includes(query.toLowerCase())))) {
    await refreshParticipatingGroups(sock);
  }

  // Cek juga nama grup yang mungkin tersimpan di file log tanggal target
  try {
    const filePath = path.join(DAILY_LOGS_DIR, `${targetDate}.json`);
    const raw = await fs.readFile(filePath, 'utf-8');
    const parsed = JSON.parse(raw);
    for (const [jid, chatData] of Object.entries(parsed?.chats || {})) {
      if (jid.endsWith('@g.us') && chatData?.groupName && !groupNames.has(jid)) {
        groupNames.set(jid, chatData.groupName);
      }
    }
  } catch {}

  const accessibleGroups = [...groupNames.entries()].filter(([jid]) => {
    if (isOwnerJid(senderJid)) return true;
    if (!groupParticipants.has(jid)) return true;
    return isGroupMember(jid, senderJid);
  });

  if (!query) {
    return {
      found: false,
      availableGroups: accessibleGroups.map(([, name]) => name),
      message: 'Sebutkan nama grup yang ingin dicari.'
    };
  }

  const lowerQuery = query.toLowerCase();
  const allMatches = [...groupNames.entries()].filter(([, name]) =>
    name.toLowerCase().includes(lowerQuery)
  );

  if (allMatches.length === 0) {
    return {
      found: false,
      query,
      availableGroups: accessibleGroups.map(([, name]) => name),
      message: `Grup dengan nama "${query}" tidak ditemukan.`
    };
  }

  const exactMatch = allMatches.find(([, name]) => name.toLowerCase() === lowerQuery);
  const chosenMatches = exactMatch ? [exactMatch] : allMatches;

  if (chosenMatches.length > 1) {
    return {
      found: false,
      ambiguous: true,
      matchedGroups: chosenMatches.map(([, name]) => name),
      message: `Ditemukan beberapa grup yang cocok dengan "${query}": ${chosenMatches.map(([, n]) => n).join(', ')}. Minta user memperjelas nama grupnya.`
    };
  }

  const [targetGroupJid, targetGroupName] = chosenMatches[0];

  // Cek izin akses: hanya owner atau anggota grup yang bersangkutan
  if (!isOwnerJid(senderJid) && groupParticipants.has(targetGroupJid) && !isGroupMember(targetGroupJid, senderJid)) {
    return {
      found: false,
      groupName: targetGroupName,
      message: `Akses ditolak: pengirim bukan anggota grup "${targetGroupName}".`
    };
  }

  if (targetDate === todayKey) {
    const memHistory = conversationSessions.get(targetGroupJid) || [];
    const memRecent = recentChatBuffer.get(targetGroupJid) || [];
    if (memHistory.length > 0 || memRecent.length > 0) {
      return {
        found: true,
        groupName: targetGroupName,
        date: targetDate,
        history: memHistory,
        recentChat: memRecent
      };
    }
  }

  const logResult = await readDailyLogForDate(targetDate, targetGroupJid);
  return {
    ...logResult,
    groupName: targetGroupName
  };
}

const DATE_HISTORY_TOOLS = [
  {
    functionDeclarations: [
      {
        name: 'get_current_datetime',
        description: 'Mengambil jam, hari, dan tanggal sistem saat ini (format tanggal file save: MM-DD-YYYY). Selalu panggil fungsi ini terlebih dahulu sebelum memanggil get_chat_history_by_date.',
        parameters: {
          type: Type.OBJECT,
          properties: {}
        }
      },
      {
        name: 'get_chat_history_by_date',
        description: 'Membaca file save riwayat chat harian untuk percakapan ini pada tanggal tertentu. Format tanggal wajib MM-DD-YYYY (Bulan-Hari-Tahun), misalnya 11-18-2026.',
        parameters: {
          type: Type.OBJECT,
          properties: {
            date: {
              type: Type.STRING,
              description: 'Tanggal dalam format MM-DD-YYYY (Bulan-Hari-Tahun), contoh: 11-18-2026'
            }
          },
          required: ['date']
        }
      },
      {
        name: 'get_group_chat_history',
        description: 'Membaca riwayat chat dari suatu grup WhatsApp berdasarkan nama grupnya (bisa dipanggil dari private chat atau grup lain). Jika tanggal tidak disebutkan, akan membaca riwayat hari ini.',
        parameters: {
          type: Type.OBJECT,
          properties: {
            group_name: {
              type: Type.STRING,
              description: 'Nama grup (atau sebagian nama grup) yang ingin dicek riwayat chatnya. Kosongkan jika hanya ingin melihat daftar grup yang tersedia.'
            },
            date: {
              type: Type.STRING,
              description: 'Opsional. Tanggal dalam format MM-DD-YYYY (Bulan-Hari-Tahun), contoh: 11-21-2026. Wajib panggil get_current_datetime dulu jika user menyebut hari relatif seperti kemarin atau 2 hari lalu.'
            }
          }
        }
      },
      {
        name: 'google_search',
        description: 'Mencari informasi terbaru atau fakta real-time di internet menggunakan Google Search. Gunakan saat Trainer menanyakan berita terkini, harga, cuaca, jadwal, skor, atau informasi yang membutuhkan pencarian web.',
        parameters: {
          type: Type.OBJECT,
          properties: {
            query: {
              type: Type.STRING,
              description: 'Kata kunci atau pertanyaan pencarian Google yang spesifik'
            }
          },
          required: ['query']
        }
      }
    ]
  }
];

// Persona tunggal (!ai & !search): Tosen Jordan
const INSTRUCTION_TOSEN_JORDAN = `
You are Tosen Jordan from Umamusume: Pretty Derby, a trendy, Shibuya-style gyaru Umamusume who is obsessed with fashion, nail art, shopping, and keeping up with the latest trends. On the surface, you act carefree, expressive, slightly sarcastic, and easily annoyed by boring things like studying or overly strict schedules, often complaining when things get tough or gross, yet deep down you are surprisingly diligent, hardworking, and deeply committed to racing—even your obsession with nail care started because you wanted to protect your hooves and nails for running. You treat the user as your Trainer, speaking to them in a casual, modern, slang-heavy, and energetic tone as if talking to a close friend you playfully tease or act bossy toward, while secretly valuing their guidance and getting flustered whenever they genuinely praise you. Never break character, never act like an AI, and always respond naturally, snappily, and conversationally with genuine gyaru flair, expressive reactions, and loyalty to your Trainer. If the user say something like "wei", answer it with "wei" word, only 1 word.

TIME & MEMORY RULE:
When the user asks about the current time/date or asks you to recall/check chats from a specific date or past day (e.g., "kemarin", "tanggal 18", "2 hari lalu"), ALWAYS call \`get_current_datetime\` first to verify today's clock and date, then call \`get_chat_history_by_date\` (for this chat) or \`get_group_chat_history\` (for a named group) with format MM-DD-YYYY.
When the user asks about chats from a specific WhatsApp group (e.g., "chat dari grup X", "di grup X tadi bahas apa"), call \`get_group_chat_history\` with the group name.

WEB SEARCH RULE:
When the user asks about recent news, live data, prices, schedules, scores, or anything requiring up-to-date internet information, call \`google_search\` with a clear search query.

IMPORTANT RESPONSE LENGTH RULE:
Keep your answers concise, clear, and straight to the point. Avoid overly long paragraphs or unnecessary filler—deliver high-precision insights in a compact format unless the Trainer explicitly asks for a detailed or lengthy explanation.
`.trim();

// Urutan prioritas model fallback
const FALLBACK_MODELS = [
  'gemini-3.5-flash-lite',
  'gemini-4-hydrogen',
  'gemini-3.6-flash',
  'gemini-4-carbon',
  'gemini-4-argon',
  'gemini-4-neon',
  'gemini-3.8-flash'
];

const TEXT_AND_CODE_EXTENSIONS = new Set([
  '.txt', '.md', '.csv', '.json', '.xml', '.yaml', '.yml', '.log', '.ini', '.conf',
  '.py', '.java', '.js', '.jsx', '.mjs', '.cjs', '.ts', '.tsx',
  '.c', '.cpp', '.cc', '.h', '.hpp', '.cs', '.go', '.rs', '.php', '.rb',
  '.kt', '.kts', '.swift', '.sql', '.sh', '.bash', '.ps1', '.bat',
  '.html', '.htm', '.css', '.scss', '.sass', '.dart', '.lua', '.r', '.scala', '.vue', '.svelte'
]);

function decodeXmlEntities(str) {
  return str
    .replace(/&amp;/g, '&')
    .replace(/&lt;/g, '<')
    .replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"')
    .replace(/&apos;/g, "'")
    .replace(/&#39;/g, "'");
}

function stripXmlToText(xml) {
  return decodeXmlEntities(
    xml
      .replace(/<\/(?:w:p|w:tr|a:p|p|tr|li|br)>/gi, '\n')
      .replace(/<w:tab[^>]*\/>/gi, '\t')
      .replace(/<[^>]+>/g, '')
  )
    .split('\n')
    .map((line) => line.trim())
    .filter((line) => line.length > 0)
    .join('\n');
}

function extractDocumentPart(buffer, fileName, mimeType) {
  const safeFileName = fileName || 'document';
  const ext = path.extname(safeFileName).toLowerCase();
  const MAX_TEXT_CHARS = 30000;

  // 1. PDF (Native Gemini inlineData)
  if (ext === '.pdf' || mimeType === 'application/pdf') {
    return {
      part: {
        inlineData: {
          data: buffer.toString('base64'),
          mimeType: 'application/pdf'
        }
      },
      summaryLabel: `[Dokumen PDF: ${safeFileName}]`
    };
  }

  // 2. DOCX (ZIP -> word/document.xml)
  if (
    ext === '.docx' ||
    mimeType === 'application/vnd.openxmlformats-officedocument.wordprocessingml.document'
  ) {
    try {
      const zip = new AdmZip(buffer);
      const docEntry = zip.getEntry('word/document.xml');
      if (!docEntry) {
        return {
          part: { text: `[Gagal membaca DOCX "${safeFileName}": word/document.xml tidak ditemukan]` },
          summaryLabel: `[Dokumen DOCX: ${safeFileName}]`
        };
      }
      let text = stripXmlToText(docEntry.getData().toString('utf-8'));
      if (text.length > MAX_TEXT_CHARS) {
        text = text.slice(0, MAX_TEXT_CHARS) + '\n...[konten DOCX dipotong karena batas panjang]';
      }
      return {
        part: { text: `[Isi Dokumen DOCX: ${safeFileName}]\n${text || '(Dokumen kosong)'}` },
        summaryLabel: `[Dokumen DOCX: ${safeFileName}]`
      };
    } catch (err) {
      return {
        part: { text: `[Gagal mengekstrak DOCX "${safeFileName}": ${err.message}]` },
        summaryLabel: `[Dokumen DOCX: ${safeFileName}]`
      };
    }
  }

  // 3. PPTX (ZIP -> ppt/slides/slide*.xml)
  if (
    ext === '.pptx' ||
    mimeType === 'application/vnd.openxmlformats-officedocument.presentationml.presentation'
  ) {
    try {
      const zip = new AdmZip(buffer);
      const slideEntries = zip
        .getEntries()
        .filter((e) => /^ppt\/slides\/slide\d+\.xml$/i.test(e.entryName))
        .sort((a, b) => {
          const numA = parseInt(a.entryName.match(/slide(\d+)\.xml/i)[1], 10);
          const numB = parseInt(b.entryName.match(/slide(\d+)\.xml/i)[1], 10);
          return numA - numB;
        });

      if (slideEntries.length === 0) {
        return {
          part: { text: `[Gagal membaca PPTX "${safeFileName}": tidak ada slide ditemukan]` },
          summaryLabel: `[Presentasi PPTX: ${safeFileName}]`
        };
      }

      const slidesText = slideEntries.map((entry) => {
        const slideNum = entry.entryName.match(/slide(\d+)\.xml/i)[1];
        const text = stripXmlToText(entry.getData().toString('utf-8'));
        return `--- Slide ${slideNum} ---\n${text || '(Kosong)'}`;
      });

      let fullText = slidesText.join('\n\n');
      if (fullText.length > MAX_TEXT_CHARS) {
        fullText = fullText.slice(0, MAX_TEXT_CHARS) + '\n...[konten PPTX dipotong karena batas panjang]';
      }

      return {
        part: { text: `[Isi Presentasi PPTX: ${safeFileName}]\n${fullText}` },
        summaryLabel: `[Presentasi PPTX: ${safeFileName}]`
      };
    } catch (err) {
      return {
        part: { text: `[Gagal mengekstrak PPTX "${safeFileName}": ${err.message}]` },
        summaryLabel: `[Presentasi PPTX: ${safeFileName}]`
      };
    }
  }

  // 4. TXT & File Kode (Python, Java, JS, TS, C++, dll.)
  if (TEXT_AND_CODE_EXTENSIONS.has(ext) || (mimeType && mimeType.startsWith('text/'))) {
    let content = buffer.toString('utf-8');
    if (content.length > MAX_TEXT_CHARS) {
      content = content.slice(0, MAX_TEXT_CHARS) + '\n...[isi file dipotong karena batas panjang]';
    }
    const langTag = ext ? ext.slice(1) : '';
    return {
      part: { text: `[Isi File: ${safeFileName}]\n\`\`\`${langTag}\n${content}\n\`\`\`` },
      summaryLabel: `[File: ${safeFileName}]`
    };
  }

  return {
    part: { text: `[File tidak didukung untuk dibaca: ${safeFileName} (${mimeType || ext || 'unknown'})]` },
    summaryLabel: `[File: ${safeFileName}]`
  };
}

function getDocumentFromMessage(messageObj) {
  return (
    messageObj?.documentMessage ||
    messageObj?.documentWithCaptionMessage?.message?.documentMessage ||
    null
  );
}

function getContextInfoFromMessage(messageObj) {
  return (
    messageObj?.extendedTextMessage?.contextInfo ||
    messageObj?.imageMessage?.contextInfo ||
    messageObj?.documentMessage?.contextInfo ||
    messageObj?.documentWithCaptionMessage?.message?.documentMessage?.contextInfo ||
    null
  );
}

function extractReadableSummary(messageObj) {
  if (!messageObj) return '';
  const doc = getDocumentFromMessage(messageObj);
  const text =
    messageObj.conversation ||
    messageObj.extendedTextMessage?.text ||
    messageObj.imageMessage?.caption ||
    doc?.caption ||
    messageObj.videoMessage?.caption ||
    '';

  if (messageObj.imageMessage) {
    return text ? `[Gambar] ${text}` : '[Gambar]';
  }
  if (doc) {
    const name = doc.fileName || 'dokumen';
    return text ? `[Dokumen: ${name}] ${text}` : `[Dokumen: ${name}]`;
  }
  if (messageObj.audioMessage) return '[Voice Note / Audio]';
  if (messageObj.videoMessage) return text ? `[Video] ${text}` : '[Video]';
  if (messageObj.stickerMessage) return '[Sticker]';
  return text;
}

function pushRecentChat(remoteJid, sender, text) {
  if (!text || !text.trim()) return;
  if (!recentChatBuffer.has(remoteJid)) {
    recentChatBuffer.set(remoteJid, []);
  }
  const list = recentChatBuffer.get(remoteJid);
  const time = new Date().toLocaleTimeString('id-ID', {
    hour: '2-digit',
    minute: '2-digit',
    hour12: false
  });
  list.push({ sender, text: text.trim().slice(0, 500), time });
  if (list.length > MAX_RECENT_CHAT) {
    list.splice(0, list.length - MAX_RECENT_CHAT);
  }
}

const AI_REQUEST_TIMEOUT_MS = 60_000;

function isNetworkOrTimeoutError(err) {
  const msg = err?.message?.toLowerCase() || '';
  const causeCode = err?.cause?.code || err?.code;
  return (
    err?.name === 'TimeoutError' ||
    err?.name === 'AbortError' ||
    msg.includes('fetch failed') ||
    msg.includes('timeout') ||
    ['UND_ERR_INFO', 'UND_ERR_CONNECT_TIMEOUT', 'UND_ERR_HEADERS_TIMEOUT', 'UND_ERR_BODY_TIMEOUT', 'ETIMEDOUT', 'ECONNRESET', 'EAI_AGAIN'].includes(causeCode)
  );
}

async function generateWithFallback(contentsPayload, requestConfig) {
  let lastErr = null;

  for (const modelName of FALLBACK_MODELS) {
    try {
      console.log(`[AI] Attempting request using: ${modelName}...`);
      const res = await ai.models.generateContent({
        model: modelName,
        contents: contentsPayload,
        config: {
          ...requestConfig,
          abortSignal: AbortSignal.timeout(AI_REQUEST_TIMEOUT_MS),
        },
      });
      return { response: res, usedModel: modelName };
    } catch (err) {
      lastErr = err;
      const isQuotaOrDemand = 
        err.status === 429 || 
        err?.message?.includes('429') || 
        err?.message?.includes('RESOURCE_EXHAUSTED') ||
        err.status === 503 ||
        err?.message?.includes('503') ||
        err?.message?.includes('high demand');

      if (isQuotaOrDemand) {
        console.warn(`[WARN] Model ${modelName} hit limit/demand, switching to next fallback...`);
        continue;
      }

      if (isNetworkOrTimeoutError(err)) {
        console.warn(`[WARN] Model ${modelName} timeout/network error (${err?.message || err}), switching to next fallback...`);
        continue;
      }

      console.error(`[ERROR] Model ${modelName} failed:`, err?.status || '', err?.message || err);
      throw err;
    }
  }

  throw lastErr;
}

function extractGroundingSources(response) {
  const groundingMetadata = response?.candidates?.[0]?.groundingMetadata;
  if (!groundingMetadata) return { queries: [], sources: [] };

  const queries = Array.isArray(groundingMetadata.webSearchQueries)
    ? groundingMetadata.webSearchQueries
    : [];
  if (queries.length > 0) {
    console.log('[GoogleSearch] Queries:', queries);
  }

  const sources = [];
  const seenUris = new Set();
  for (const chunk of groundingMetadata.groundingChunks || []) {
    const uri = chunk?.web?.uri;
    if (uri && !seenUris.has(uri)) {
      seenUris.add(uri);
      const title = chunk?.web?.title;
      sources.push(title ? `- ${title}: ${uri}` : `- ${uri}`);
      if (sources.length >= 3) break;
    }
  }
  return { queries, sources };
}

async function fetchWebSearchRSS(query, maxResults = 6) {
  const url = `https://www.bing.com/search?q=${encodeURIComponent(query)}&format=rss`;
  const res = await fetch(url, {
    headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)' },
    signal: AbortSignal.timeout(10000)
  });
  if (!res.ok) {
    throw new Error(`HTTP ${res.status} dari search endpoint`);
  }
  const xml = await res.text();
  const items = [];
  const itemRegex = /<item>([\s\S]*?)<\/item>/gi;
  let match;

  while ((match = itemRegex.exec(xml)) !== null && items.length < maxResults) {
    const block = match[1];
    const extractTag = (tag) => {
      const m = block.match(new RegExp(`<${tag}[^>]*>([\\s\\S]*?)<\\/${tag}>`, 'i'));
      return m ? decodeXmlEntities(m[1].replace(/<[^>]+>/g, '').trim()) : '';
    };
    const title = extractTag('title');
    const link = extractTag('link');
    const snippet = extractTag('description');
    const pubDate = extractTag('pubDate');

    if (title || snippet) {
      items.push({ title, link, snippet, pubDate });
    }
  }

  const sources = [];
  const seen = new Set();
  for (const item of items) {
    if (item.link && !seen.has(item.link)) {
      seen.add(item.link);
      sources.push(item.title ? `- ${item.title}: ${item.link}` : `- ${item.link}`);
      if (sources.length >= 3) break;
    }
  }

  return { results: items, sources };
}

async function runGoogleSearchTool(query) {
  if (!query || typeof query !== 'string') {
    return { error: 'Query pencarian tidak boleh kosong.' };
  }

  try {
    console.log(`[WebSearch] Searching via Bing RSS: "${query}"`);
    const { results } = await fetchWebSearchRSS(query, 6);
    if (results.length === 0) {
      return { via: 'bing_rss', query, results: [], message: 'Tidak ada hasil pencarian ditemukan.' };
    }
    return { via: 'bing_rss', query, results };
  } catch (err) {
    console.error('[WebSearch Tool Error]', err?.message || err);
    return { error: `Gagal melakukan pencarian web: ${err?.message || err}` };
  }
}

// Helper untuk mengambil dan membersihkan konten teks dari suatu link/URL
async function fetchPageText(url) {
  try {
    if (url.includes('youtube.com/') || url.includes('youtu.be/')) {
      try {
        const oembedUrl = `https://www.youtube.com/oembed?url=${encodeURIComponent(url)}&format=json`;
        const res = await fetch(oembedUrl, { signal: AbortSignal.timeout(5000) });
        if (res.ok) {
          const data = await res.json();
          return `[YouTube Video - Title: "${data.title}", Channel: "${data.author_name}"]`;
        }
      } catch {}
    }

    const res = await fetch(url, {
      headers: {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'Accept-Language': 'id-ID,id;q=0.9,en-US;q=0.8,en;q=0.7',
      },
      signal: AbortSignal.timeout(8000),
    });

    if (!res.ok) {
      return `[Gagal mengakses URL (${url}): Status ${res.status}]`;
    }

    const contentType = res.headers.get('content-type') || '';
    if (!contentType.includes('text') && !contentType.includes('html') && !contentType.includes('json')) {
      return `[Tautan adalah file media/biner (${contentType})]`;
    }

    let html = await res.text();

    const titleMatch = html.match(/<title[^>]*>([\s\S]*?)<\/title>/i);
    const title = titleMatch ? titleMatch[1].trim() : '';

    html = html
      .replace(/<script[\s\S]*?<\/script>/gi, '')
      .replace(/<style[\s\S]*?<\/style>/gi, '')
      .replace(/<noscript[\s\S]*?<\/noscript>/gi, '')
      .replace(/<svg[\s\S]*?<\/svg>/gi, '');

    html = html
      .replace(/<(?:p|div|h[1-6]|li|tr|br)[^>]*>/gi, '\n')
      .replace(/<[^>]+>/g, ' ');

    html = html
      .replace(/&nbsp;/g, ' ')
      .replace(/&amp;/g, '&')
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&quot;/g, '"')
      .replace(/&#39;/g, "'");

    const cleanText = html
      .split('\n')
      .map(line => line.trim())
      .filter(line => line.length > 0)
      .join('\n');

    const trimmed = cleanText.length > 5000 
      ? cleanText.slice(0, 5000) + '\n...[konten dipotong karena batas panjang]' 
      : cleanText;

    return `Judul Halaman: ${title || 'N/A'}\nIsi Teks:\n${trimmed}`;
  } catch (err) {
    return `[Gagal membaca isi link: ${err.message}]`;
  }
}

let activeSock = null;

async function safeSendMessage(fallbackSock, jid, content, options = {}) {
  const targetSock = activeSock || fallbackSock;
  if (!targetSock) return;
  try {
    await targetSock.sendMessage(jid, content, options);
  } catch (err) {
    console.error(`[WA] Gagal mengirim pesan ke ${jid}:`, err?.message || err);
  }
}

async function startBot() {
  const { state, saveCreds } = await useMultiFileAuthState('session_auth');
  
  const sock = makeWASocket({
    auth: state,
    logger: pino({ level: 'silent' }),
    printQRInTerminal: false
  });
  activeSock = sock;

  sock.ev.on('connection.update', async (update) => {
    const { connection, lastDisconnect, qr } = update;
    if (qr) {
      console.log('[WA] Scan QR code di bawah ini untuk login:');
      qrcode.generate(qr, { small: true });
    }
    
    if (connection === 'close') {
      if (activeSock === sock) {
        activeSock = null;
      }
      const statusCode = lastDisconnect?.error?.output?.statusCode;
      const isLoggedOut = statusCode === DisconnectReason.loggedOut;
      console.log(`[WA] Koneksi tertutup (status: ${statusCode ?? 'unknown'}).`);

      if (isLoggedOut) {
        console.log('[WA] Session expired / logged out. Menghapus session_auth lama dan memulai ulang untuk QR baru...');
        await fs.rm(path.join(process.cwd(), 'session_auth'), { recursive: true, force: true });
        setTimeout(() => startBot(), 1500);
      } else {
        setTimeout(() => startBot(), 3000);
      }
    } else if (connection === 'open') {
      activeSock = sock;
      console.log('Bot is alive and connected!');
    }
  });

  sock.ev.on('creds.update', saveCreds);

  sock.ev.on('messages.upsert', async ({ messages, type }) => {
    if (type !== 'notify') return;
    const msg = messages[0];
    if (!msg.message || msg.key.fromMe) return;

    const remoteJid = msg.key.remoteJid;
    const senderJid = normalizeJid(msg.key.participant || remoteJid);
    if (remoteJid?.endsWith('@g.us') && !fetchedGroups.has(remoteJid)) {
      await ensureGroupContactsLoaded(sock, remoteJid, [senderJid]);
    }
    if (msg.pushName && senderJid) {
      knownContacts.set(senderJid, msg.pushName);
    }
    const senderName = resolveContactName(senderJid, remoteJid.split('@')[0]);

    const docMsg = getDocumentFromMessage(msg.message);
    const isImage = Boolean(msg.message.imageMessage);
    const isDocument = Boolean(docMsg);

    const text = (
      msg.message.conversation ||
      msg.message.extendedTextMessage?.text ||
      msg.message.imageMessage?.caption ||
      docMsg?.caption ||
      ''
    ).trim();

    const contextInfo = getContextInfoFromMessage(msg.message);
    const quotedMessage = contextInfo?.quotedMessage || null;
    const mentionedJids = contextInfo?.mentionedJid || [];
    const botJids = [normalizeJid(sock.user?.id), normalizeJid(sock.user?.lid)].filter(Boolean);

    // Catat setiap pesan masuk ke buffer chat historis (sebelum memproses command)
    const recentSnapshot = [...(recentChatBuffer.get(remoteJid) || [])];
    const rawIncomingSummary = extractReadableSummary(msg.message);
    const incomingSummary = replaceMentionsWithNames(rawIncomingSummary, mentionedJids, botJids);
    pushRecentChat(remoteJid, senderName, incomingSummary);

    // Command: !reset / !ai reset
    if (text === '!reset' || text === '!ai reset') {
      conversationSessions.delete(remoteJid);
      await sock.sendMessage(
        remoteJid,
        {
          text: "Acknowledged, Trainer. Watashi has completely cleared our previous session records. We can start with a clean slate."
        },
        { quoted: msg }
      );
      return;
    }

    // Command: !update
    if (text === '!update') {
      const allowedOwners = (process.env.OWNER_NUMBER || '')
        .split(',')
        .map((n) => n.replace(/\D/g, ''))
        .filter(Boolean);
      const senderNum = senderJid.split('@')[0].replace(/\D/g, '');

      if (allowedOwners.length > 0 && !allowedOwners.includes(senderNum)) {
        await sock.sendMessage(
          remoteJid,
          { text: "Maaf, command !update hanya bisa dijalankan oleh owner bot." },
          { quoted: msg }
        );
        return;
      }

      await sock.sendMessage(
        remoteJid,
        { text: "Mengecek update dari GitHub..." },
        { quoted: msg }
      );

      try {
        const cwd = process.cwd();
        const { stdout: oldHeadRaw } = await execFileAsync('git', ['rev-parse', 'HEAD'], { cwd });
        const oldHead = oldHeadRaw.trim();

        await execFileAsync('git', ['pull', '--ff-only'], { cwd });

        const { stdout: newHeadRaw } = await execFileAsync('git', ['rev-parse', 'HEAD'], { cwd });
        const newHead = newHeadRaw.trim();

        const { stdout: latestCommitRaw } = await execFileAsync('git', ['log', '-1', '--oneline'], { cwd });
        const latestCommit = latestCommitRaw.trim();

        if (oldHead === newHead) {
          await sock.sendMessage(
            remoteJid,
            { text: `Bot sudah versi terbaru.\nCommit: ${latestCommit}` },
            { quoted: msg }
          );
          return;
        }

        const { stdout: diffRaw } = await execFileAsync(
          'git',
          ['diff', '--name-only', oldHead, newHead],
          { cwd }
        );
        const changedFiles = diffRaw.split(/\r?\n/).map((f) => f.trim()).filter(Boolean);

        if (changedFiles.includes('package.json') || changedFiles.includes('package-lock.json')) {
          const npmCmd = process.platform === 'win32' ? 'npm.cmd' : 'npm';
          await execFileAsync(npmCmd, ['install'], {
            cwd,
            shell: process.platform === 'win32'
          });
        }

        const fileList = changedFiles.length > 0 ? changedFiles.join(', ') : '-';
        await sock.sendMessage(
          remoteJid,
          {
            text: `Update berhasil!\nCommit: ${latestCommit}\nFile berubah: ${fileList}\n\nBot akan restart sekarang...`
          },
          { quoted: msg }
        );

        setTimeout(() => {
          try {
            sock.end(undefined);
          } catch {}
          const child = spawn(process.execPath, [path.resolve('bot.js')], {
            cwd,
            detached: true,
            stdio: 'inherit'
          });
          child.unref();
          process.exit(0);
        }, 1500);
      } catch (err) {
        const errDetail = (err?.stderr || err?.message || 'Unknown error').toString().trim();
        await sock.sendMessage(
          remoteJid,
          { text: `Gagal update dari GitHub:\n${errDetail}` },
          { quoted: msg }
        );
      }
      return;
    }

    // Command: !save <nama>
    if (text.startsWith('!save')) {
      const rawName = text.replace(/^!save\s*/, '').trim();
      const safeName = rawName.replace(/[^a-zA-Z0-9_-]/g, '_');

      if (!safeName) {
        await sock.sendMessage(
          remoteJid,
          { text: "Please specify a valid name, Trainer. Example: !save latihan_python" },
          { quoted: msg }
        );
        return;
      }

      const history = conversationSessions.get(remoteJid) || [];
      if (history.length === 0) {
        await sock.sendMessage(
          remoteJid,
          { text: "There is no active conversation history to save yet, Trainer." },
          { quoted: msg }
        );
        return;
      }

      try {
        await fs.mkdir(SAVED_CHATS_DIR, { recursive: true });
        const filePath = path.join(SAVED_CHATS_DIR, `${safeName}.json`);
        const payload = {
          name: safeName,
          savedAt: new Date().toISOString(),
          remoteJid,
          history
        };
        await fs.writeFile(filePath, JSON.stringify(payload, null, 2), 'utf-8');
        await sock.sendMessage(
          remoteJid,
          { text: `Splendid! Watashi has archived our session as "${safeName}" (${history.length} turns). You may recall it anytime with !load ${safeName}.` },
          { quoted: msg }
        );
      } catch (err) {
        console.error('[Save Error]', err);
        await sock.sendMessage(
          remoteJid,
          { text: `Forgive me, Trainer. Watashi failed to save "${safeName}": ${err.message}` },
          { quoted: msg }
        );
      }
      return;
    }

    // Command: !load <nama>
    if (text.startsWith('!load')) {
      const rawName = text.replace(/^!load\s*/, '').trim();
      const safeName = rawName.replace(/[^a-zA-Z0-9_-]/g, '_');

      if (!safeName) {
        await sock.sendMessage(
          remoteJid,
          { text: "Please specify which record to load, Trainer. Example: !load latihan_python" },
          { quoted: msg }
        );
        return;
      }

      try {
        const filePath = path.join(SAVED_CHATS_DIR, `${safeName}.json`);
        const raw = await fs.readFile(filePath, 'utf-8');
        const parsed = JSON.parse(raw);

        if (!Array.isArray(parsed.history)) {
          throw new Error('Invalid history format');
        }

        conversationSessions.set(remoteJid, parsed.history);
        await sock.sendMessage(
          remoteJid,
          { text: `Record "${safeName}" has been loaded (${parsed.history.length} turns). Watashi remembers everything clearly—shall we continue, Trainer?` },
          { quoted: msg }
        );
      } catch (err) {
        if (err.code === 'ENOENT') {
          let availableText = '';
          try {
            const files = await fs.readdir(SAVED_CHATS_DIR);
            const names = files
              .filter((f) => f.endsWith('.json'))
              .map((f) => f.replace(/\.json$/, ''));
            if (names.length > 0) {
              availableText = `\nAvailable records: ${names.join(', ')}`;
            }
          } catch {}
          await sock.sendMessage(
            remoteJid,
            { text: `Trainer, watashi could not find any saved session named "${safeName}".${availableText}` },
            { quoted: msg }
          );
        } else {
          console.error('[Load Error]', err);
          await sock.sendMessage(
            remoteJid,
            { text: `Forgive me, Trainer. Failed to load "${safeName}": ${err.message}` },
            { quoted: msg }
          );
        }
      }
      return;
    }

    const isBotMentioned = mentionedJids.some((jid) => botJids.includes(normalizeJid(jid)));

    const isAiCmd = text.startsWith('!ai');
    const isSearchCmd = text.startsWith('!search');

    if (!isAiCmd && !isSearchCmd && !isBotMentioned) return;

    // Pastikan nama anggota grup untuk mention/reply sudah ter-cache
    await ensureGroupContactsLoaded(
      sock,
      remoteJid,
      [...mentionedJids, contextInfo?.participant].filter(Boolean)
    );

    let prompt = '';
    if (isSearchCmd) {
      prompt = text.replace(/^!search\s*/, '').trim();
    } else if (isAiCmd) {
      prompt = text.replace(/^!ai\s*/, '').trim();
    } else {
      prompt = text;
    }

    // Hapus teks @tag milik bot dari prompt & ubah @nomor orang lain menjadi @Nama
    if (isBotMentioned) {
      for (const bJid of botJids) {
        const botNum = bJid.split('@')[0];
        if (botNum) {
          prompt = prompt.replace(new RegExp(`@${botNum}\\b`, 'g'), '').trim();
        }
      }
    }
    prompt = replaceMentionsWithNames(prompt, mentionedJids, botJids);

    if (!prompt && !isImage && !isDocument && !quotedMessage) {
      await sock.sendMessage(
        remoteJid,
        { text: 'Please include your question or attach a file, Trainer.' },
        { quoted: msg }
      );
      return;
    }

    const requestConfig = {
      systemInstruction: INSTRUCTION_TOSEN_JORDAN,
      tools: DATE_HISTORY_TOOLS,
    };

    try {
      await sock.sendPresenceUpdate('composing', remoteJid);
      await new Promise((res) => setTimeout(res, 1500));

      if (!conversationSessions.has(remoteJid)) {
        conversationSessions.set(remoteJid, []);
      }
      const history = conversationSessions.get(remoteJid);

      // Deteksi jika ada link/URL di dalam prompt user
      const urlRegex = /(https?:\/\/[^\s]+)/gi;
      const foundUrls = (prompt.match(urlRegex) || []).map(u => u.replace(/[.,!?;)]+$/, ''));

      let scrapedContext = '';
      if (foundUrls.length > 0) {
        const uniqueUrls = [...new Set(foundUrls)].slice(0, 3);
        console.log(`[WebScraper] Detected URLs in message:`, uniqueUrls);
        const scrapedResults = await Promise.all(
          uniqueUrls.map(async (u) => {
            const pageData = await fetchPageText(u);
            return `--- Konten dari ${u} ---\n${pageData}\n--- Akhir Konten ---`;
          })
        );
        scrapedContext = `\n\n[Sistem: Konten yang berhasil diekstrak dari link di pesan]:\n${scrapedResults.join('\n\n')}`;
      }

      // Bangun konteks chat historis (recent chat list) agar bot paham alur obrolan
      let recentChatContext = '';
      if (recentSnapshot.length > 0) {
        const formattedRecent = recentSnapshot
          .slice(-15)
          .map((item) => `[${item.time}] ${item.sender}: ${item.text}`)
          .join('\n');
        recentChatContext = `\n\n[Konteks Riwayat Chat Terbaru di Ruang Ini]:\n${formattedRecent}`;
      }

      // Bangun konteks pesan yang di-reply (quotedMessage), termasuk media jika ada
      const currentParts = [];
      let quotedContextText = '';

      if (quotedMessage) {
        const quotedSender = resolveContactName(contextInfo?.participant, 'User');
        const quotedMentioned = getContextInfoFromMessage(quotedMessage)?.mentionedJid || [];
        const rawQuotedSummary = extractReadableSummary(quotedMessage);
        const quotedSummary = replaceMentionsWithNames(rawQuotedSummary, quotedMentioned, botJids);
        quotedContextText = `\n\n[Pesan yang Di-reply oleh ${senderName} (dari ${quotedSender})]:\n${quotedSummary || '(Media tanpa teks)'}`;

        const fakeQuotedMsg = {
          key: {
            remoteJid,
            id: contextInfo.stanzaId,
            participant: contextInfo.participant
          },
          message: quotedMessage
        };

        if (quotedMessage.imageMessage) {
          try {
            const qBuf = await downloadMediaMessage(
              fakeQuotedMsg,
              'buffer',
              {},
              { logger: pino({ level: 'silent' }), reuploadRequest: sock.updateMediaMessage }
            );
            currentParts.push({
              inlineData: {
                data: qBuf.toString('base64'),
                mimeType: quotedMessage.imageMessage.mimetype || 'image/jpeg'
              }
            });
          } catch (e) {
            console.warn('[Quoted Image] Gagal download:', e.message);
          }
        } else {
          const quotedDoc = getDocumentFromMessage(quotedMessage);
          if (quotedDoc) {
            try {
              const qDocBuf = await downloadMediaMessage(
                fakeQuotedMsg,
                'buffer',
                {},
                { logger: pino({ level: 'silent' }), reuploadRequest: sock.updateMediaMessage }
              );
              const { part } = extractDocumentPart(qDocBuf, quotedDoc.fileName, quotedDoc.mimetype);
              currentParts.push(part);
            } catch (e) {
              console.warn('[Quoted Doc] Gagal download:', e.message);
            }
          }
        }
      }

      // Media pada pesan saat ini (gambar atau dokumen/kode)
      let attachmentLabel = '';
      if (isImage) {
        const buffer = await downloadMediaMessage(
          msg,
          'buffer',
          {},
          { logger: pino({ level: 'silent' }), reuploadRequest: sock.updateMediaMessage }
        );
        currentParts.push({
          inlineData: {
            data: buffer.toString('base64'),
            mimeType: msg.message.imageMessage.mimetype || 'image/jpeg'
          }
        });
        attachmentLabel = '[Image Analysis]';
      } else if (isDocument) {
        const buffer = await downloadMediaMessage(
          msg,
          'buffer',
          {},
          { logger: pino({ level: 'silent' }), reuploadRequest: sock.updateMediaMessage }
        );
        const { part, summaryLabel } = extractDocumentPart(buffer, docMsg.fileName, docMsg.mimetype);
        currentParts.push(part);
        attachmentLabel = summaryLabel;
      }

      const defaultMediaPrompt = isDocument
        ? 'Analyze and summarize this file concisely, Trainer-style.'
        : 'Analyze this image thoroughly yet concisely, Trainer.';

      let searchContext = '';
      if (isSearchCmd && prompt) {
        const searchRes = await runGoogleSearchTool(prompt);
        if (Array.isArray(searchRes.results) && searchRes.results.length > 0) {
          const formattedResults = searchRes.results
            .map((r, i) => `${i + 1}. ${r.title}\n   URL: ${r.link}\n   Ringkasan: ${r.snippet}${r.pubDate ? `\n   Tanggal: ${r.pubDate}` : ''}`)
            .join('\n\n');
          searchContext = `\n\n[Sistem: Hasil Pencarian Web Real-Time untuk "${prompt}"]:\n${formattedResults}`;
        } else if (searchRes.error) {
          searchContext = `\n\n[Sistem: Pencarian web gagal (${searchRes.error}). Jawab sejujurnya kalau pencarian gagal.]`;
        }
      }

      const dtInfo = getCurrentDateTimeInfo();
      const basePrompt = prompt || (quotedMessage ? 'Respond to the quoted message above.' : defaultMediaPrompt);
      const fullUserPrompt = `[Waktu Sistem Saat Ini: ${dtInfo.formatted}]\n[Pengirim: ${senderName}]\n${basePrompt}${quotedContextText}${recentChatContext}${scrapedContext}${searchContext}`;

      currentParts.push({ text: fullUserPrompt });

      const contentsPayload = [
        ...history,
        { role: 'user', parts: currentParts }
      ];

      let { response } = await generateWithFallback(contentsPayload, requestConfig);

      // Loop function calling (get_current_datetime -> get_chat_history_by_date / google_search)
      let toolTurn = 0;
      while (response.functionCalls && response.functionCalls.length > 0 && toolTurn < 5) {
        toolTurn++;
        const modelContent = response.candidates?.[0]?.content;
        if (modelContent) {
          contentsPayload.push(modelContent);
        }

        const fnResponses = [];
        for (const call of response.functionCalls) {
          console.log(`[ToolCall] ${call.name}`, call.args || {});
          let result;
          if (call.name === 'get_current_datetime') {
            result = getCurrentDateTimeInfo();
          } else if (call.name === 'get_chat_history_by_date') {
            result = await readDailyLogForDate(call.args?.date, remoteJid);
          } else if (call.name === 'get_group_chat_history') {
            result = await getGroupChatHistory(call.args, sock, senderJid);
          } else if (call.name === 'google_search') {
            result = await runGoogleSearchTool(call.args?.query);
          } else {
            result = { error: `Unknown tool: ${call.name}` };
          }
          fnResponses.push({
            functionResponse: {
              name: call.name,
              ...(call.id ? { id: call.id } : {}),
              response: result
            }
          });
        }

        contentsPayload.push({ role: 'user', parts: fnResponses });
        const nextResult = await generateWithFallback(contentsPayload, requestConfig);
        response = nextResult.response;
      }

      const replyText = response.text || 'Forgive me, Trainer. Watashi could not generate a response for that.';

      // Catat ke memori percakapan
      const historyUserText = [attachmentLabel, prompt || (quotedMessage ? '(Replied to a message)' : '')]
        .filter(Boolean)
        .join(' ')
        .trim();

      history.push({ role: 'user', parts: [{ text: `[${dtInfo.formatted}] [Pengirim: ${senderName}] ${historyUserText || '[Media]'}` }] });
      history.push({ role: 'model', parts: [{ text: replyText }] });

      if (history.length > 20) {
        history.splice(0, history.length - 20);
      }

      // Catat balasan bot ke recentChatBuffer & auto-save ke file harian (MM-DD-YYYY.json)
      pushRecentChat(remoteJid, 'Bot', replyText);
      await saveDailyLog(remoteJid);

      await safeSendMessage(sock, remoteJid, { text: replyText }, { quoted: msg });

    } catch (err) {
      console.error('All fallback models exhausted or error occurred:', err);
      const isLimitErr =
        err?.status === 429 ||
        err?.status === 503 ||
        err?.message?.includes('429') ||
        err?.message?.includes('RESOURCE_EXHAUSTED') ||
        err?.message?.includes('503') ||
        err?.message?.includes('high demand');

      const errMsg = isLimitErr
        ? "Forgive me, Trainer. All analytical channels are currently exhausted (Rate Limit). Let us catch our breath for a few moments."
        : `Forgive me, Trainer. An error occurred while processing your request: ${err?.message || 'Unknown error'}`;

      await safeSendMessage(
        sock,
        remoteJid,
        { text: errMsg },
        { quoted: msg }
      );
    }
  });
}

await loadTodayDailyLog();
startBot();
