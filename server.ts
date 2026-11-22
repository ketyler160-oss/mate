import crypto from 'node:crypto';
import fs from 'node:fs';
import http from 'node:http';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import dotenv from 'dotenv';
import express from 'express';
import type { Request, Response } from 'express';
import nodemailer from 'nodemailer';
import { WebSocket, WebSocketServer } from 'ws';
import { GoogleGenAI, ThinkingLevel, Type } from '@google/genai';

dotenv.config();

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const PORT = Number(process.env.PORT) || 3000;
const STARTING_DEMO_BALANCE = 500;
const STORE_DIR = path.resolve(__dirname, '.data');
const STORE_PATH = path.join(STORE_DIR, 'luckymate-store.json');
let runtimeAppSecret = process.env.APP_SECRET || '';

const BETTING_SECONDS = 10;
const ROUND_PAUSE_SECONDS = 4;
const TICK_MS = 100;

export const CRASH_GAME_IDS = [
  'aviator',
  'comet-crash',
  'swimminator',
  'b-crash',
  'punchinator',
  'crash-3dx',
  'crash-royale',
  'fortune-spins',
  'jetx',
  'spaceman',
  'original',
] as const;

export type CrashGameId = (typeof CRASH_GAME_IDS)[number];

const CRASH_GAME_NAMES: Record<CrashGameId, string> = {
  aviator: 'Aviator',
  'comet-crash': 'Comet Crash',
  swimminator: 'Swimminator',
  'b-crash': 'B! Crash',
  punchinator: 'Punchinator',
  'crash-3dx': 'Crash 3DX',
  'crash-royale': 'Crash Royale',
  'fortune-spins': 'Fortune Spins',
  jetx: 'JetX',
  spaceman: 'Spaceman',
  original: 'Original Crash',
};

export interface WalletTransaction {
  id: string;
  type:
    | 'deposit'
    | 'withdraw'
    | 'referral_bonus'
    | 'bet_won'
    | 'bet_lost'
    | 'bet_pending'
    | 'crash_cashout'
    | 'crash_stake';
  amount: number;
  stake?: number;
  odds?: number;
  status?: 'Won' | 'Lost' | 'Pending' | 'Completed';
  label: string;
  detail: string;
  createdAt: string;
}

export interface RoomBetRecord {
  id: string;
  slot: 1 | 2;
  accountId: string;
  username: string;
  roundId: string;
  game: CrashGameId;
  amount: number;
  autoCashout: number | null;
  status: 'active' | 'cashed_out' | 'lost';
  payout: number;
  cashoutMultiplier: number | null;
  walletTxId: string;
  walletMode?: 'demo' | 'real';
  createdAt: string;
}

export interface RoomRoundRecord {
  id: string;
  game: CrashGameId;
  gameTitle: string;
  roundNumber: number;
  status: 'betting' | 'running' | 'crashed';
  seed: string;
  seedHash: string;
  hmacHex: string;
  crashPoint: number;
  startedAt: string | null;
  endedAt: string | null;
}

export type SupportedCountry = 'Kenya' | 'Ghana' | "Côte d'Ivoire";

const BASE_KES_PER_USD = 130;
const MIN_DEPOSIT_USD = 6;
const MIN_WITHDRAW_USD = 60;
const WITHDRAW_FEE_USD = 12;
const REFERRAL_REWARD_USD = 3;
const REFERRAL_MIN_DEPOSIT_USD = 6;

function calculateWithdrawFeeUsd(withdrawUsd: number): number {
  const amt = Number(withdrawUsd);
  if (!Number.isFinite(amt) || amt <= 0) return 0;
  if (amt <= 150) return 12;
  if (amt <= 500) return Number((amt * 0.25).toFixed(2));
  if (amt <= 1000) return 45;
  if (amt <= 5000) return 69;
  if (amt <= 10000) return 89;
  return 250;
}

const COUNTRY_META: Record<
  SupportedCountry,
  {
    dialCode: string;
    currency: 'KES' | 'GHS' | 'XOF';
    usdRate: number;
    payMethod: string;
    sampleLocal: string;
  }
> = {
  Kenya: {
    dialCode: '+254',
    currency: 'KES',
    usdRate: 130,
    payMethod: 'M-PESA',
    sampleLocal: '0712 234567',
  },
  Ghana: {
    dialCode: '+233',
    currency: 'GHS',
    usdRate: 16,
    payMethod: 'MTN MoMo / Telecel',
    sampleLocal: '024 123 4567',
  },
  "Côte d'Ivoire": {
    dialCode: '+225',
    currency: 'XOF',
    usdRate: 600,
    payMethod: 'Orange / MTN Money',
    sampleLocal: '07 01 23 45 67',
  },
};

function parseSupportedCountry(raw: unknown): SupportedCountry {
  if (raw === 'Ghana') return 'Ghana';
  if (raw === "Côte d'Ivoire" || raw === "Cote d'Ivoire" || raw === 'CI') return "Côte d'Ivoire";
  return 'Kenya';
}

function normalizePhoneNumber(
  rawPhone: string,
  country: SupportedCountry
): { ok: true; e164: string; localDigits: string } | { ok: false; message: string } {
  const cleaned = rawPhone.replace(/^tel:/i, '').replace(/[\s\u00A0\-().]/g, '');
  const meta = COUNTRY_META[country];
  const dialDigits = meta.dialCode.slice(1); // 254, 233, 225

  if (!/^\+?\d+$/.test(cleaned)) {
    return {
      ok: false,
      message: `Enter a valid ${country} phone number (${meta.sampleLocal}).`,
    };
  }

  let subscriber = cleaned.startsWith('+') ? cleaned.slice(1) : cleaned;
  if (subscriber.startsWith('00')) {
    subscriber = subscriber.slice(2);
  }
  if (subscriber.startsWith(dialDigits)) {
    subscriber = subscriber.slice(dialDigits.length);
  }

  if (country === 'Kenya') {
    if (subscriber.startsWith('0')) subscriber = subscriber.slice(1);
    if (!/^[17]\d{8}$/.test(subscriber)) {
      return {
        ok: false,
        message: 'Enter a valid Kenya phone number (e.g. 0712 234567 or +254712234567).',
      };
    }
    return { ok: true, e164: `+254${subscriber}`, localDigits: `0${subscriber}` };
  }

  if (country === 'Ghana') {
    if (subscriber.startsWith('0')) subscriber = subscriber.slice(1);
    if (!/^[235]\d{8}$/.test(subscriber)) {
      return {
        ok: false,
        message: 'Enter a valid Ghana phone number (e.g. 024 123 4567 or +233241234567).',
      };
    }
    return { ok: true, e164: `+233${subscriber}`, localDigits: `0${subscriber}` };
  }

  // Côte d'Ivoire supports 10-digit new numbering plan (e.g. 07 01 23 45 67) or 8-digit subscriber numbers
  if (!/^\d{8,10}$/.test(subscriber)) {
    return {
      ok: false,
      message: "Enter a valid Côte d'Ivoire phone number (e.g. 07 01 23 45 67 or +2250701234567).",
    };
  }
  return { ok: true, e164: `+225${subscriber}`, localDigits: subscriber };
}

function normalizeEmail(raw: string): { ok: true; email: string } | { ok: false; message: string } {
  const email = raw.trim().toLowerCase();
  if (!email || !/^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email) || email.length > 160) {
    return { ok: false, message: 'Enter a valid email address (e.g. name@example.com).' };
  }
  return { ok: true, email };
}

interface AccountRecord {
  id: string;
  username: string;
  phone?: string;
  email?: string;
  emailVerified?: boolean;
  otpCodeHash?: string | null;
  otpExpiresAt?: number | null;
  otpAttempts?: number;
  otpLastSentAt?: number;
  country: SupportedCountry;
  passwordHash: string | null;
  encryptedPassword?: string | null;
  isGuest: boolean;
  isAdmin: boolean;
  demoBalance: number;
  realBalance: number;
  activeAccountType: 'demo' | 'real';
  totalWagered: number;
  totalWon: number;
  gamesPlayed: number;
  lastDepositAmount: number;
  lastDepositDate: string;
  history: WalletTransaction[];
  referralCode?: string;
  referredByAccountId?: string | null;
  referredByCode?: string | null;
  referralRewardPaid?: boolean;
  referralEarningsBase?: number;
  hasQualifyingRealDeposit?: boolean;
  pendingReferralBonusBase?: number;
  referrals?: ReferralRecord[];
  createdAt: string;
  updatedAt: number;
}

export interface ReferralRecord {
  id: string;
  referredAccountId: string;
  referredUsername: string;
  maskedPhone: string;
  joinedAt: string;
  status: 'pending_deposit' | 'awaiting_referrer_deposit' | 'rewarded';
  qualifyingDepositUsd?: number;
  rewardUsd: number;
  rewardBase: number;
  rewardedAt?: string;
}

interface ScheduledRoomBet {
  triggerAtMs: number;
  username: string;
  slot: 1 | 2;
  amount: number;
  autoCashout: number | null;
}

interface CrashRoom {
  game: CrashGameId;
  clients: Set<WebSocket>;
  simulatedPresence: number;
  pendingSimBets: ScheduledRoomBet[];
  roundId: string;
  roundNumber: number;
  status: 'betting' | 'running' | 'crashed';
  multiplier: number;
  crashPoint: number;
  seed: string;
  seedHash: string;
  hmacHex: string;
  upcomingSeed: string;
  upcomingSeedHash: string;
  upcomingHmacHex: string;
  upcomingCrashPoint: number;
  deadlineMs: number;
  startedAtMs: number;
  crashedAtMs: number;
  lastStateBroadcastMs: number;
  activeBets: RoomBetRecord[];
  previousBets: RoomBetRecord[];
  previousCrashPoint: number | null;
  topWins: RoomBetRecord[];
  recentRounds: RoomRoundRecord[];
}

const accountsById = new Map<string, AccountRecord>();
const accountIdByUsername = new Map<string, string>();
const accountIdByPhone = new Map<string, string>();
const accountIdByEmail = new Map<string, string>();
const accountIdByReferralCode = new Map<string, string>();
const sessionToAccountId = new Map<string, string>();
const roundsById = new Map<string, RoomRoundRecord>();
const creditedPaystackReferences = new Set<string>();
const settledWithdrawReferences = new Set<string>();
const DEFAULT_PREDICTOR_LOGIN_PASSWORD = '25508128013';
const PREDICTOR_CHANGE_PASSWORD_CODE = '0115612670';
let predictorAccessCode = DEFAULT_PREDICTOR_LOGIN_PASSWORD;

const REFERRAL_CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

function generateUniqueReferralCode(): string {
  for (let attempt = 0; attempt < 25; attempt++) {
    const bytes = crypto.randomBytes(6);
    let suffix = '';
    for (let i = 0; i < 6; i++) {
      suffix += REFERRAL_CODE_CHARS[bytes[i] % REFERRAL_CODE_CHARS.length];
    }
    const candidate = `LM${suffix}`;
    if (!accountIdByReferralCode.has(candidate)) {
      return candidate;
    }
  }
  return `LM${crypto.randomBytes(4).toString('hex').toUpperCase()}`;
}

let saveTimer: ReturnType<typeof setTimeout> | null = null;

function saveStoreNow() {
  try {
    if (!fs.existsSync(STORE_DIR)) {
      fs.mkdirSync(STORE_DIR, { recursive: true });
    }
    const persistedAccounts = Array.from(accountsById.values()).filter(
      (a) => !a.isGuest || a.realBalance > 0 || a.history.length > 3
    );
    const payload = {
      appSecret: runtimeAppSecret,
      predictorAccessCode,
      accounts: persistedAccounts,
      creditedPaystackReferences: Array.from(creditedPaystackReferences),
      settledWithdrawReferences: Array.from(settledWithdrawReferences),
    };
    const tmpPath = `${STORE_PATH}.tmp`;
    fs.writeFileSync(tmpPath, JSON.stringify(payload, null, 2), 'utf8');
    fs.renameSync(tmpPath, STORE_PATH);
  } catch (err) {
    console.error('Failed to persist store:', err);
  }
}

function scheduleSaveStore() {
  if (saveTimer) return;
  saveTimer = setTimeout(() => {
    saveTimer = null;
    saveStoreNow();
  }, 150);
}

function loadPersistentStore() {
  try {
    if (fs.existsSync(STORE_PATH)) {
      const raw = fs.readFileSync(STORE_PATH, 'utf8');
      const parsed = JSON.parse(raw) as {
        appSecret?: string;
        predictorAccessCode?: string;
        accounts?: AccountRecord[];
        creditedPaystackReferences?: string[];
        settledWithdrawReferences?: string[];
      };
      if (!runtimeAppSecret && typeof parsed.appSecret === 'string' && parsed.appSecret.length >= 32) {
        runtimeAppSecret = parsed.appSecret;
      }
      if (
        typeof parsed.predictorAccessCode === 'string' &&
        parsed.predictorAccessCode.trim().length >= 4 &&
        parsed.predictorAccessCode.trim() !== PREDICTOR_CHANGE_PASSWORD_CODE
      ) {
        predictorAccessCode = parsed.predictorAccessCode.trim();
      }
      if (Array.isArray(parsed.accounts)) {
        for (const acc of parsed.accounts) {
          if (!acc || typeof acc.id !== 'string' || typeof acc.username !== 'string') continue;
          if (Array.isArray(acc.history)) {
            const cleaned = acc.history.filter((h) => h && !String(h.id || '').startsWith('seed-'));
            if (cleaned.length !== acc.history.length) {
              acc.history = cleaned;
              const hasRealBet = cleaned.some(
                (h) =>
                  h.type === 'bet_won' ||
                  h.type === 'bet_lost' ||
                  h.type === 'bet_pending' ||
                  h.type === 'crash_cashout' ||
                  h.type === 'crash_stake'
              );
              if (!hasRealBet) {
                acc.totalWagered = 0;
                acc.totalWon = 0;
                acc.gamesPlayed = 0;
              }
            }
          } else {
            acc.history = [];
          }
          if (!acc.isGuest) {
            if (!acc.referralCode || typeof acc.referralCode !== 'string') {
              acc.referralCode = generateUniqueReferralCode();
            } else {
              acc.referralCode = acc.referralCode.trim().toUpperCase();
            }
            if (!Array.isArray(acc.referrals)) {
              acc.referrals = [];
            }
            if (typeof acc.referralEarningsBase !== 'number' || !Number.isFinite(acc.referralEarningsBase)) {
              acc.referralEarningsBase = 0;
            }
            if (typeof acc.pendingReferralBonusBase !== 'number' || !Number.isFinite(acc.pendingReferralBonusBase)) {
              acc.pendingReferralBonusBase = 0;
            }
            if (typeof acc.hasQualifyingRealDeposit !== 'boolean') {
              const minDepositBase = MIN_DEPOSIT_USD * BASE_KES_PER_USD;
              acc.hasQualifyingRealDeposit = Boolean(
                acc.lastDepositAmount >= minDepositBase - 0.01 ||
                  acc.history.some(
                    (h) =>
                      h.type === 'deposit' &&
                      h.amount >= minDepositBase - 0.01 &&
                      String(h.label || '').toLowerCase().includes('real')
                  )
              );
            }
          }
          accountsById.set(acc.id, acc);
          accountIdByUsername.set(acc.username.toLowerCase(), acc.id);
          if (acc.phone) {
            accountIdByPhone.set(acc.phone, acc.id);
          }
          if (acc.email) {
            accountIdByEmail.set(acc.email.toLowerCase(), acc.id);
          }
          if (acc.referralCode) {
            accountIdByReferralCode.set(acc.referralCode.toUpperCase(), acc.id);
          }
        }
      }
      if (Array.isArray(parsed.creditedPaystackReferences)) {
        for (const ref of parsed.creditedPaystackReferences) {
          if (typeof ref === 'string' && ref) {
            creditedPaystackReferences.add(ref);
          }
        }
      }
      if (Array.isArray(parsed.settledWithdrawReferences)) {
        for (const ref of parsed.settledWithdrawReferences) {
          if (typeof ref === 'string' && ref) {
            settledWithdrawReferences.add(ref);
          }
        }
      }
    }
  } catch (err) {
    console.error('Failed to load persistent store:', err);
  }
  if (!runtimeAppSecret) {
    runtimeAppSecret = crypto.randomBytes(32).toString('hex');
    saveStoreNow();
  }
}

loadPersistentStore();

function sha256Hex(value: string): string {
  return crypto.createHash('sha256').update(value).digest('hex');
}

function hashPassword(password: string): string {
  const salt = crypto.randomBytes(16).toString('hex');
  const derived = crypto.pbkdf2Sync(password, salt, 100000, 32, 'sha256').toString('hex');
  return `${salt}$${derived}`;
}

function verifyPassword(password: string, stored: string | null): boolean {
  if (!stored || !stored.includes('$')) return false;
  const [salt, expectedHex] = stored.split('$', 2);
  const actualBuf = crypto.pbkdf2Sync(password, salt, 100000, 32, 'sha256');
  const expectedBuf = Buffer.from(expectedHex, 'hex');
  if (actualBuf.length !== expectedBuf.length) return false;
  return crypto.timingSafeEqual(actualBuf, expectedBuf);
}

function derivePasswordRecoveryKey(identityKey: string): Buffer {
  const normalizedKey = identityKey.trim().toLowerCase() || 'luckymate-default';
  return crypto
    .createHash('sha256')
    .update(`luckymate-pwd-recovery-v1:${normalizedKey}`)
    .digest();
}

function encryptRecoverablePassword(plainPassword: string, identityKey: string): string {
  const key = derivePasswordRecoveryKey(identityKey);
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  const encrypted = Buffer.concat([cipher.update(plainPassword, 'utf8'), cipher.final()]);
  const tag = cipher.getAuthTag();
  return `v1:${iv.toString('hex')}:${tag.toString('hex')}:${encrypted.toString('hex')}`;
}

function decryptRecoverablePassword(
  payload: string | null | undefined,
  identityKey: string
): string | null {
  if (!payload || typeof payload !== 'string' || !payload.startsWith('v1:')) return null;
  const parts = payload.split(':');
  if (parts.length !== 4) return null;
  try {
    const [, ivHex, tagHex, dataHex] = parts;
    const key = derivePasswordRecoveryKey(identityKey);
    const decipher = crypto.createDecipheriv('aes-256-gcm', key, Buffer.from(ivHex, 'hex'));
    decipher.setAuthTag(Buffer.from(tagHex, 'hex'));
    const decrypted = Buffer.concat([
      decipher.update(Buffer.from(dataHex, 'hex')),
      decipher.final(),
    ]);
    const text = decrypted.toString('utf8');
    return text.length >= 6 ? text : null;
  } catch {
    return null;
  }
}

function createAuthToken(accountId: string): string {
  const expiry = Math.floor(Date.now() / 1000) + 86400 * 7;
  const payload = `${accountId}:${expiry}`;
  const sig = crypto.createHmac('sha256', runtimeAppSecret).update(payload).digest('hex');
  return `${payload}:${sig}`;
}

function verifyAuthToken(token: string): AccountRecord | null {
  try {
    const parts = token.split(':');
    if (parts.length !== 3) return null;
    const [accountId, expiryStr, signature] = parts;
    const payload = `${accountId}:${expiryStr}`;
    const expected = crypto.createHmac('sha256', runtimeAppSecret).update(payload).digest('hex');
    const sigBuf = Buffer.from(signature, 'hex');
    const expBuf = Buffer.from(expected, 'hex');
    if (sigBuf.length !== expBuf.length || !crypto.timingSafeEqual(sigBuf, expBuf)) {
      return null;
    }
    if (Number(expiryStr) < Math.floor(Date.now() / 1000)) {
      return null;
    }
    return accountsById.get(accountId) || null;
  } catch {
    return null;
  }
}

function createInitialHistory(): WalletTransaction[] {
  return [];
}

function getAccountBalance(account: AccountRecord, mode?: 'demo' | 'real'): number {
  const target = mode ?? account.activeAccountType;
  return Number((target === 'real' ? account.realBalance : account.demoBalance).toFixed(2));
}

function adjustAccountBalance(account: AccountRecord, mode: 'demo' | 'real', delta: number) {
  if (mode === 'real') {
    account.realBalance = Number((account.realBalance + delta).toFixed(2));
  } else {
    account.demoBalance = Number((account.demoBalance + delta).toFixed(2));
  }
  if (!account.isGuest) {
    scheduleSaveStore();
  }
}

function buildReferralSummary(account: AccountRecord) {
  const referrals = Array.isArray(account.referrals) ? account.referrals : [];
  const qualifiedCount = referrals.filter((r) => r.status === 'rewarded').length;
  const awaitingClaimCount = referrals.filter((r) => r.status === 'awaiting_referrer_deposit').length;
  const pendingCount = referrals.filter((r) => r.status === 'pending_deposit').length;
  const totalEarnedBase = Number((account.referralEarningsBase || 0).toFixed(2));
  const totalEarnedUsd = Number((totalEarnedBase / BASE_KES_PER_USD).toFixed(2));
  const pendingBonusBase = Number((account.pendingReferralBonusBase || 0).toFixed(2));
  const pendingBonusUsd = Number((pendingBonusBase / BASE_KES_PER_USD).toFixed(2));
  const hasQualifyingRealDeposit = Boolean(
    account.hasQualifyingRealDeposit ||
      account.lastDepositAmount >= MIN_DEPOSIT_USD * BASE_KES_PER_USD - 0.01
  );

  return {
    referralCode: account.referralCode || '',
    referredByCode: account.referredByCode ?? null,
    rewardUsd: REFERRAL_REWARD_USD,
    minDepositUsd: REFERRAL_MIN_DEPOSIT_USD,
    hasQualifyingRealDeposit,
    totalInvited: referrals.length,
    qualifiedCount,
    awaitingClaimCount,
    pendingCount,
    totalEarnedBase,
    totalEarnedUsd,
    pendingBonusBase,
    pendingBonusUsd,
    referrals: referrals.slice(0, 50).map((r) => ({
      id: r.id,
      referredUsername: r.referredUsername,
      maskedPhone: r.maskedPhone,
      joinedAt: r.joinedAt,
      status: r.status,
      qualifyingDepositUsd: r.qualifyingDepositUsd,
      rewardUsd: r.rewardUsd,
      rewardBase: r.rewardBase,
      rewardedAt: r.rewardedAt,
    })),
  };
}

function unlockPendingReferralBonusesForAccount(account: AccountRecord): {
  unlockedBase: number;
  unlockedUsd: number;
  unlockedCount: number;
} {
  const pendingBase = Number((account.pendingReferralBonusBase || 0).toFixed(2));
  if (account.isGuest || pendingBase <= 0) {
    return { unlockedBase: 0, unlockedUsd: 0, unlockedCount: 0 };
  }

  const nowIso = new Date().toISOString();
  const unlockedUsd = Number((pendingBase / BASE_KES_PER_USD).toFixed(2));
  let unlockedCount = 0;

  if (Array.isArray(account.referrals)) {
    for (const entry of account.referrals) {
      if (entry.status === 'awaiting_referrer_deposit') {
        entry.status = 'rewarded';
        entry.rewardedAt = nowIso;
        unlockedCount += 1;
      }
    }
  }

  adjustAccountBalance(account, 'real', pendingBase);
  account.referralEarningsBase = Number(((account.referralEarningsBase || 0) + pendingBase).toFixed(2));
  account.pendingReferralBonusBase = 0;
  account.updatedAt = Date.now();

  account.history.unshift({
    id: crypto.randomUUID(),
    type: 'referral_bonus',
    amount: pendingBase,
    status: 'Completed',
    label: `Referral Bonus Unlocked (+$${unlockedUsd.toFixed(2)} USD)`,
    detail: `Your $${MIN_DEPOSIT_USD.toFixed(2)} USD real deposit unlocked ${
      unlockedCount > 1 ? `${unlockedCount} referral bonuses` : 'your earned referral bonus'
    } into your Real Wallet`,
    createdAt: nowIso,
  });
  account.history = account.history.slice(0, 40);

  return { unlockedBase: pendingBase, unlockedUsd, unlockedCount };
}

function processReferralRewardOnQualifyingDeposit(
  depositor: AccountRecord,
  depositUsd: number
): {
  awarded: boolean;
  heldForReferrerDeposit?: boolean;
  referrerUsername?: string;
  rewardUsd?: number;
  unlockedOwnBonusUsd?: number;
} {
  if (depositor.isGuest || depositUsd < MIN_DEPOSIT_USD) {
    return { awarded: false };
  }

  let unlockedOwnBonusUsd = 0;
  let dirty = false;

  // Step 1: Depositor themselves now satisfies the $6 USD real deposit rule — release any held bonuses!
  if (!depositor.hasQualifyingRealDeposit) {
    depositor.hasQualifyingRealDeposit = true;
    dirty = true;
  }
  const unlocked = unlockPendingReferralBonusesForAccount(depositor);
  if (unlocked.unlockedUsd > 0) {
    unlockedOwnBonusUsd = unlocked.unlockedUsd;
    dirty = true;
  }

  // Step 2: If depositor was invited by a friend, reward or hold $3 USD for the referrer
  if (
    !depositor.referredByAccountId ||
    depositor.referralRewardPaid ||
    depositUsd < REFERRAL_MIN_DEPOSIT_USD
  ) {
    if (dirty) saveStoreNow();
    return { awarded: false, unlockedOwnBonusUsd };
  }

  const referrer = accountsById.get(depositor.referredByAccountId);
  if (!referrer || referrer.id === depositor.id || referrer.isGuest) {
    if (dirty) saveStoreNow();
    return { awarded: false, unlockedOwnBonusUsd };
  }

  const rewardBase = Number((REFERRAL_REWARD_USD * BASE_KES_PER_USD).toFixed(2));
  const nowIso = new Date().toISOString();

  depositor.referralRewardPaid = true;
  depositor.updatedAt = Date.now();

  const referrerHasQualifiedDeposit = Boolean(
    referrer.hasQualifyingRealDeposit ||
      referrer.lastDepositAmount >= MIN_DEPOSIT_USD * BASE_KES_PER_USD - 0.01
  );

  if (!Array.isArray(referrer.referrals)) {
    referrer.referrals = [];
  }

  const existingEntry = referrer.referrals.find((r) => r.referredAccountId === depositor.id);
  const nextStatus: ReferralRecord['status'] = referrerHasQualifiedDeposit
    ? 'rewarded'
    : 'awaiting_referrer_deposit';

  if (existingEntry) {
    existingEntry.status = nextStatus;
    existingEntry.qualifyingDepositUsd = Number(depositUsd.toFixed(2));
    existingEntry.rewardUsd = REFERRAL_REWARD_USD;
    existingEntry.rewardBase = rewardBase;
    if (referrerHasQualifiedDeposit) {
      existingEntry.rewardedAt = nowIso;
    }
  } else {
    referrer.referrals.unshift({
      id: crypto.randomUUID(),
      referredAccountId: depositor.id,
      referredUsername: depositor.username,
      maskedPhone: depositor.phone ? maskPhone(depositor.phone) : depositor.username,
      joinedAt: depositor.createdAt,
      status: nextStatus,
      qualifyingDepositUsd: Number(depositUsd.toFixed(2)),
      rewardUsd: REFERRAL_REWARD_USD,
      rewardBase,
      rewardedAt: referrerHasQualifiedDeposit ? nowIso : undefined,
    });
  }

  if (referrerHasQualifiedDeposit) {
    adjustAccountBalance(referrer, 'real', rewardBase);
    referrer.referralEarningsBase = Number(((referrer.referralEarningsBase || 0) + rewardBase).toFixed(2));
    referrer.history.unshift({
      id: crypto.randomUUID(),
      type: 'referral_bonus',
      amount: rewardBase,
      status: 'Completed',
      label: `Referral Bonus (+$${REFERRAL_REWARD_USD.toFixed(2)} USD)`,
      detail: `Invited friend ${depositor.username} deposited $${depositUsd.toFixed(2)} USD · Credited to Real Wallet`,
      createdAt: nowIso,
    });
    referrer.history = referrer.history.slice(0, 40);
  } else {
    referrer.pendingReferralBonusBase = Number(
      ((referrer.pendingReferralBonusBase || 0) + rewardBase).toFixed(2)
    );
  }

  referrer.updatedAt = Date.now();
  saveStoreNow();
  return {
    awarded: referrerHasQualifiedDeposit,
    heldForReferrerDeposit: !referrerHasQualifiedDeposit,
    referrerUsername: referrer.username,
    rewardUsd: REFERRAL_REWARD_USD,
    unlockedOwnBonusUsd,
  };
}

function buildWalletFields(account: AccountRecord) {
  const country = account.country ?? 'Kenya';
  if (!account.isGuest && !account.referralCode) {
    account.referralCode = generateUniqueReferralCode();
    accountIdByReferralCode.set(account.referralCode, account.id);
    scheduleSaveStore();
  }
  return {
    country,
    currency: COUNTRY_META[country].currency,
    phone: account.phone,
    email: account.email,
    emailVerified: account.emailVerified !== false,
    createdAt: account.createdAt,
    referralCode: account.isGuest ? undefined : account.referralCode,
    referredByCode: account.isGuest ? null : account.referredByCode ?? null,
    referralSummary: account.isGuest ? undefined : buildReferralSummary(account),
    balance: getAccountBalance(account),
    demoBalance: Number(account.demoBalance.toFixed(2)),
    realBalance: Number(account.realBalance.toFixed(2)),
    accountMode: account.activeAccountType,
    playedStats: getPlayedStats(account),
    lastDepositAmount: Number(account.lastDepositAmount.toFixed(2)),
    lastDepositDate: account.lastDepositDate,
    history: account.history,
  };
}

function createAccount(params: {
  username: string;
  phone?: string;
  email?: string;
  emailVerified?: boolean;
  otpCodeHash?: string | null;
  otpExpiresAt?: number | null;
  otpAttempts?: number;
  otpLastSentAt?: number;
  country?: SupportedCountry;
  passwordHash: string | null;
  encryptedPassword?: string | null;
  isGuest: boolean;
  isAdmin?: boolean;
  startingBalance?: number;
  referredByAccountId?: string | null;
  referredByCode?: string | null;
  createdAt?: string;
}): AccountRecord {
  const id = crypto.randomUUID();
  const country = params.country ?? 'Kenya';
  const cleanEmail = params.email ? params.email.trim().toLowerCase() : undefined;
  const referralCode = params.isGuest ? undefined : generateUniqueReferralCode();
  const account: AccountRecord = {
    id,
    username: params.username,
    phone: params.phone,
    email: cleanEmail,
    emailVerified: params.emailVerified ?? true,
    otpCodeHash: params.otpCodeHash ?? null,
    otpExpiresAt: params.otpExpiresAt ?? null,
    otpAttempts: params.otpAttempts ?? 0,
    otpLastSentAt: params.otpLastSentAt,
    country,
    passwordHash: params.passwordHash,
    encryptedPassword: params.encryptedPassword ?? null,
    isGuest: params.isGuest,
    isAdmin: Boolean(params.isAdmin),
    demoBalance: params.startingBalance ?? STARTING_DEMO_BALANCE,
    realBalance: 0,
    activeAccountType: 'demo',
    totalWagered: 0,
    totalWon: 0,
    gamesPlayed: 0,
    lastDepositAmount: 0,
    lastDepositDate: 'No real deposit yet',
    history: createInitialHistory(),
    referralCode,
    referredByAccountId: params.referredByAccountId ?? null,
    referredByCode: params.referredByCode ?? null,
    referralRewardPaid: false,
    referralEarningsBase: 0,
    hasQualifyingRealDeposit: false,
    pendingReferralBonusBase: 0,
    referrals: [],
    createdAt: params.createdAt || new Date().toISOString(),
    updatedAt: Date.now(),
  };
  accountsById.set(id, account);
  accountIdByUsername.set(params.username.toLowerCase(), id);
  if (params.phone) {
    accountIdByPhone.set(params.phone, id);
  }
  if (cleanEmail) {
    accountIdByEmail.set(cleanEmail, id);
  }
  if (referralCode) {
    accountIdByReferralCode.set(referralCode, id);
  }
  if (!params.isGuest) {
    saveStoreNow();
  }
  return account;
}

function getPlayedStats(account: AccountRecord) {
  return {
    totalWagered: Number(account.totalWagered.toFixed(2)),
    totalWon: Number(account.totalWon.toFixed(2)),
    netPlayed: Number((account.totalWon - account.totalWagered).toFixed(2)),
    gamesPlayed: account.gamesPlayed,
  };
}

function parseCookieValue(cookieHeader: string, name: string): string {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const match = cookieHeader.match(new RegExp(`(?:^|;\\s*)${escaped}=([^;]+)`));
  return match ? decodeURIComponent(match[1]) : '';
}

function appendSetCookie(res: Response, cookieValue: string) {
  const prev = res.getHeader('Set-Cookie');
  if (!prev) {
    res.setHeader('Set-Cookie', [cookieValue]);
  } else if (Array.isArray(prev)) {
    res.setHeader('Set-Cookie', [...prev.map(String), cookieValue]);
  } else {
    res.setHeader('Set-Cookie', [String(prev), cookieValue]);
  }
}

function resolveSessionIdFromRequest(req: Request, res: Response): string {
  const headerSid =
    typeof req.headers['x-demo-session'] === 'string' ? req.headers['x-demo-session'].trim() : '';
  const cookieHeader = req.headers.cookie || '';
  const cookieSid = parseCookieValue(cookieHeader, 'luckymate_sid');

  let sessionId = headerSid || cookieSid;
  if (!sessionId || sessionId.length < 12 || sessionId.length > 64) {
    sessionId = crypto.randomBytes(16).toString('hex');
  }

  if (cookieSid !== sessionId) {
    appendSetCookie(
      res,
      `luckymate_sid=${encodeURIComponent(sessionId)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800`
    );
  }
  return sessionId;
}

function resolveRequestAccount(
  req: Request,
  res: Response
): { sessionId: string; account: AccountRecord } {
  const authHeader = typeof req.headers.authorization === 'string' ? req.headers.authorization : '';
  const bearerToken = authHeader.startsWith('Bearer ') ? authHeader.slice(7).trim() : '';
  const cookieHeader = req.headers.cookie || '';
  const cookieToken = parseCookieValue(cookieHeader, 'luckymate_auth');
  const sessionId = resolveSessionIdFromRequest(req, res);

  const candidateToken = bearerToken || cookieToken;
  if (candidateToken) {
    const authed = verifyAuthToken(candidateToken);
    if (authed) {
      sessionToAccountId.set(sessionId, authed.id);
      return { sessionId, account: authed };
    }
  }

  const accountId = sessionToAccountId.get(sessionId);
  let account = accountId ? accountsById.get(accountId) : undefined;
  if (!account) {
    const guestTag = sessionId.slice(0, 6).toUpperCase();
    account = createAccount({
      username: `Player-${guestTag}`,
      passwordHash: null,
      isGuest: true,
    });
    sessionToAccountId.set(sessionId, account.id);
  }

  return { sessionId, account };
}

function maskPhone(phone: string): string {
  const digits = phone.replace(/\s+/g, '');
  if (digits.length <= 4) return digits;
  return `${digits.slice(0, 4)}***${digits.slice(-3)}`;
}

function formatShortDate(date: Date): string {
  return date.toLocaleDateString('en-US', { month: 'short', day: 'numeric', year: 'numeric' });
}

// ---------------- PROVABLY FAIR MULTIPLAYER ENGINE ----------------

export function computeRoomCrashPoint(seed: string, game: CrashGameId, roundNumber: number) {
  const message = `${game}:${roundNumber}`;
  const hmacHex = crypto.createHmac('sha256', seed).update(message).digest('hex');
  const h = parseInt(hmacHex.slice(0, 13), 16);
  const e = 4503599627370496; // 2^52
  const crashPoint =
    h % 33 === 0 ? 1.0 : Math.max(1.0, Math.floor((100 * e - h) / (e - h)) / 100);
  return {
    message,
    hmacHex,
    crashPoint: Number(crashPoint.toFixed(2)),
  };
}

const LIVE_PLAYER_HANDLES = [
  'Brian_KE',
  'Wanjiku254',
  'KevinM',
  'Faith_N',
  'OtienoPro',
  'GraceK',
  'David_88',
  'Amina254',
  'Mercy_W',
  'SamuelK',
  'Denis_O',
  'LydiaM',
  'Peter_99',
  'Collins254',
  'EstherK',
  'VictorM',
  'Lucy_W',
  'DanielK',
  'Caleb_N',
  'Joyce254',
  'Njoroge_7',
  'Zawadi_KE',
  'KamauPro',
  'Beatrice_M',
  'Hassan254',
  'Tracy_W',
  'Kiprop_K',
  'Stacy_M',
];

const ROOM_BASE_CROWD: Record<CrashGameId, number> = {
  aviator: 148,
  jetx: 96,
  'b-crash': 84,
  'comet-crash': 72,
  'crash-royale': 68,
  spaceman: 61,
  'crash-3dx': 54,
  punchinator: 49,
  swimminator: 44,
  'fortune-spins': 39,
  original: 57,
};

const STAKE_AMOUNTS = [10, 20, 50, 100, 150, 200, 300, 500, 1000, 2000, 5000];

function pickRandom<T>(items: readonly T[]): T {
  return items[crypto.randomInt(0, items.length)];
}

function generateTargetAutoCashout(): number {
  const bucket = crypto.randomInt(0, 100);
  if (bucket < 38) {
    return Number((1.15 + crypto.randomInt(0, 75) / 100).toFixed(2));
  }
  if (bucket < 76) {
    return Number((1.9 + crypto.randomInt(0, 220) / 100).toFixed(2));
  }
  return Number((4.1 + crypto.randomInt(0, 850) / 100).toFixed(2));
}

function getRoomConnectedPlayers(room: CrashRoom): number {
  return room.simulatedPresence + room.clients.size;
}

function createScheduledBetsForRound(nowMs: number, count: number): ScheduledRoomBet[] {
  const chosenNames = [...LIVE_PLAYER_HANDLES]
    .sort(() => crypto.randomInt(-1, 2))
    .slice(0, Math.min(count, LIVE_PLAYER_HANDLES.length));

  return chosenNames.map((username, idx) => ({
    triggerAtMs: nowMs + 350 + Math.floor((idx / chosenNames.length) * 8400) + crypto.randomInt(0, 350),
    username,
    slot: crypto.randomInt(0, 4) === 0 ? 2 : 1,
    amount: pickRandom(STAKE_AMOUNTS),
    autoCashout: generateTargetAutoCashout(),
  }));
}

const rooms = {} as Record<CrashGameId, CrashRoom>;
for (const gameId of CRASH_GAME_IDS) {
  rooms[gameId] = createEmptyRoom(gameId);
}

function createEmptyRoom(game: CrashGameId): CrashRoom {
  const baseCrowd = ROOM_BASE_CROWD[game] ?? 45;
  const room: CrashRoom = {
    game,
    clients: new Set<WebSocket>(),
    simulatedPresence: baseCrowd + crypto.randomInt(-6, 12),
    pendingSimBets: [],
    roundId: '',
    roundNumber: 0,
    status: 'betting',
    multiplier: 1.0,
    crashPoint: 1.0,
    seed: '',
    seedHash: '',
    hmacHex: '',
    upcomingSeed: '',
    upcomingSeedHash: '',
    upcomingHmacHex: '',
    upcomingCrashPoint: 1.0,
    deadlineMs: 0,
    startedAtMs: 0,
    crashedAtMs: 0,
    lastStateBroadcastMs: 0,
    activeBets: [],
    previousBets: [],
    previousCrashPoint: null,
    topWins: [],
    recentRounds: [],
  };

  // Seed initial completed rounds, previous bets, and top wins so rooms open lively
  const now = Date.now();
  for (let i = 1; i <= 8; i += 1) {
    const seed = crypto.randomBytes(32).toString('hex');
    const seedHash = sha256Hex(seed);
    const { hmacHex, crashPoint } = computeRoomCrashPoint(seed, game, i);
    const rId = crypto.randomUUID();
    const endedAt = new Date(now - (9 - i) * 18000).toISOString();
    const rec: RoomRoundRecord = {
      id: rId,
      game,
      gameTitle: CRASH_GAME_NAMES[game],
      roundNumber: i,
      status: 'crashed',
      seed,
      seedHash,
      hmacHex,
      crashPoint,
      startedAt: new Date(now - (9 - i) * 18000 - 8000).toISOString(),
      endedAt,
    };
    roundsById.set(rId, rec);
    room.recentRounds.unshift(rec);
    room.roundNumber = i;

    const sampleCount = 8;
    const roundBets: RoomBetRecord[] = [];
    for (let j = 0; j < sampleCount; j += 1) {
      const username = LIVE_PLAYER_HANDLES[(i * 5 + j) % LIVE_PLAYER_HANDLES.length];
      const amount = pickRandom(STAKE_AMOUNTS);
      const target = generateTargetAutoCashout();
      const won = crashPoint >= target;
      const payout = won ? Number((amount * target).toFixed(2)) : 0;
      const betRec: RoomBetRecord = {
        id: crypto.randomUUID(),
        slot: j % 4 === 0 ? 2 : 1,
        accountId: `sim-${username}`,
        username,
        roundId: rId,
        game,
        amount,
        autoCashout: target,
        status: won ? 'cashed_out' : 'lost',
        payout,
        cashoutMultiplier: won ? target : null,
        walletTxId: '',
        createdAt: endedAt,
      };
      roundBets.push(betRec);
      if (won) {
        room.topWins.push(betRec);
      }
    }
    if (i === 8) {
      room.previousBets = roundBets;
      room.previousCrashPoint = crashPoint;
    }
  }
  room.topWins = room.topWins.sort((a, b) => b.payout - a.payout).slice(0, 20);

  startNewRound(room);

  // Immediately pre-seed 5 bets into the opening round so lobby/room show live activity right away
  const immediate = room.pendingSimBets.splice(0, 5);
  for (const item of immediate) {
    room.activeBets.unshift({
      id: crypto.randomUUID(),
      slot: item.slot,
      accountId: `sim-${crypto.randomUUID()}`,
      username: item.username,
      roundId: room.roundId,
      game: room.game,
      amount: item.amount,
      autoCashout: item.autoCashout,
      status: 'active',
      payout: 0,
      cashoutMultiplier: null,
      walletTxId: '',
      createdAt: new Date().toISOString(),
    });
  }

  return room;
}

function startNewRound(room: CrashRoom) {
  const nextNumber = room.roundNumber + 1;
  const hasPrecomputed = Boolean(room.upcomingSeed && room.upcomingCrashPoint >= 1);
  const seed = hasPrecomputed ? room.upcomingSeed : crypto.randomBytes(32).toString('hex');
  const seedHash = hasPrecomputed ? room.upcomingSeedHash : sha256Hex(seed);
  const computedCurrent = hasPrecomputed
    ? { hmacHex: room.upcomingHmacHex, crashPoint: room.upcomingCrashPoint }
    : computeRoomCrashPoint(seed, room.game, nextNumber);

  // Pre-compute the following round so the hidden predictor always locks onto the exact future odd
  const followingNumber = nextNumber + 1;
  const upcomingSeed = crypto.randomBytes(32).toString('hex');
  const upcomingSeedHash = sha256Hex(upcomingSeed);
  const computedUpcoming = computeRoomCrashPoint(upcomingSeed, room.game, followingNumber);

  const roundId = crypto.randomUUID();
  const nowMs = Date.now();

  const baseCrowd = ROOM_BASE_CROWD[room.game] ?? 45;
  const drifted = room.simulatedPresence + crypto.randomInt(-3, 4);
  room.simulatedPresence = Math.min(baseCrowd + 22, Math.max(Math.max(12, baseCrowd - 16), drifted));

  room.roundId = roundId;
  room.roundNumber = nextNumber;
  room.status = 'betting';
  room.multiplier = 1.0;
  room.seed = seed;
  room.seedHash = seedHash;
  room.hmacHex = computedCurrent.hmacHex;
  room.crashPoint = computedCurrent.crashPoint;
  room.upcomingSeed = upcomingSeed;
  room.upcomingSeedHash = upcomingSeedHash;
  room.upcomingHmacHex = computedUpcoming.hmacHex;
  room.upcomingCrashPoint = computedUpcoming.crashPoint;
  room.deadlineMs = nowMs + BETTING_SECONDS * 1000;
  room.startedAtMs = 0;
  room.crashedAtMs = 0;
  room.lastStateBroadcastMs = 0;
  room.activeBets = [];
  room.pendingSimBets = createScheduledBetsForRound(nowMs, crypto.randomInt(10, 17));

  roundsById.set(roundId, {
    id: roundId,
    game: room.game,
    gameTitle: CRASH_GAME_NAMES[room.game],
    roundNumber: nextNumber,
    status: 'betting',
    seed,
    seedHash,
    hmacHex: computedCurrent.hmacHex,
    crashPoint: computedCurrent.crashPoint,
    startedAt: null,
    endedAt: null,
  });
}

function sanitizeRoundForPublic(r: RoomRoundRecord) {
  const isCrashed = r.status === 'crashed';
  return {
    roundId: r.id,
    game: r.game,
    gameTitle: r.gameTitle,
    roundNumber: r.roundNumber,
    status: r.status,
    seedHash: r.seedHash,
    seed: isCrashed ? r.seed : null,
    hmacHex: isCrashed ? r.hmacHex : null,
    crashPoint: isCrashed ? r.crashPoint : null,
    startedAt: r.startedAt,
    endedAt: r.endedAt,
  };
}

function serializeBetPublic(b: RoomBetRecord) {
  return {
    betId: b.id,
    slot: b.slot,
    username: b.username,
    amount: b.amount,
    autoCashout: b.autoCashout,
    status: b.status,
    payout: b.payout,
    cashoutMultiplier: b.cashoutMultiplier,
  };
}

function buildRoomSnapshot(room: CrashRoom) {
  const countdown =
    room.status === 'betting'
      ? Number(Math.max(0, (room.deadlineMs - Date.now()) / 1000).toFixed(1))
      : 0;

  return {
    game: room.game,
    gameTitle: CRASH_GAME_NAMES[room.game],
    roundId: room.roundId,
    roundNumber: room.roundNumber,
    status: room.status,
    multiplier: Number(room.multiplier.toFixed(2)),
    countdown,
    seedHash: room.seedHash,
    revealedSeed: room.status === 'crashed' ? room.seed : null,
    crashPoint: room.status === 'crashed' ? room.crashPoint : null,
    connectedPlayers: getRoomConnectedPlayers(room),
    activeBets: room.activeBets.map(serializeBetPublic),
    previousBets: room.previousBets.map(serializeBetPublic),
    previousCrashPoint: room.previousCrashPoint,
    topWins: room.topWins.slice(0, 20).map(serializeBetPublic),
    recentRounds: room.recentRounds.slice(0, 20).map(sanitizeRoundForPublic),
  };
}

function broadcastRoom(room: CrashRoom, payload: Record<string, unknown>) {
  if (room.clients.size === 0) return;
  const text = JSON.stringify(payload);
  for (const client of Array.from(room.clients)) {
    if (client.readyState === WebSocket.OPEN) {
      client.send(text);
    } else if (client.readyState === WebSocket.CLOSED || client.readyState === WebSocket.CLOSING) {
      room.clients.delete(client);
    }
  }
}

function settleBetWin(bet: RoomBetRecord, multiplier: number, automatic: boolean, room: CrashRoom) {
  if (bet.status !== 'active') return;
  const roundedMult = Number(multiplier.toFixed(2));
  const payout = Number((bet.amount * roundedMult).toFixed(2));

  bet.status = 'cashed_out';
  bet.payout = payout;
  bet.cashoutMultiplier = roundedMult;

  const account = accountsById.get(bet.accountId);
  if (account) {
    const mode = bet.walletMode ?? 'demo';
    adjustAccountBalance(account, mode, payout);
    account.totalWon = Number((account.totalWon + payout).toFixed(2));
    account.updatedAt = Date.now();
    const tx = account.history.find((t) => t.id === bet.walletTxId);
    if (tx) {
      tx.status = 'Won';
      tx.odds = roundedMult;
      tx.amount = Number((payout - bet.amount).toFixed(2));
      tx.detail = `[${mode.toUpperCase()}] Slip ${bet.slot} · Stake: KES ${bet.amount.toFixed(0)} | ${
        automatic ? 'Auto' : 'Manual'
      } Cashout @ ${roundedMult.toFixed(2)}x`;
    }
  }

  room.topWins = [bet, ...room.topWins.filter((w) => w.id !== bet.id)]
    .sort((a, b) => b.payout - a.payout)
    .slice(0, 20);

  broadcastRoom(room, {
    type: 'cashout',
    game: room.game,
    roundId: room.roundId,
    betId: bet.id,
    slot: bet.slot,
    username: bet.username,
    amount: bet.amount,
    multiplier: roundedMult,
    payout,
    automatic,
  });
}

function tickCrashRooms() {
  const nowMs = Date.now();

  for (const gameId of CRASH_GAME_IDS) {
    const room = rooms[gameId];

    if (room.status === 'betting') {
      // Flush scheduled live player bets as countdown progresses
      if (room.pendingSimBets.length > 0) {
        const remaining: ScheduledRoomBet[] = [];
        for (const item of room.pendingSimBets) {
          if (item.triggerAtMs <= nowMs) {
            const simBet: RoomBetRecord = {
              id: crypto.randomUUID(),
              slot: item.slot,
              accountId: `sim-${crypto.randomUUID()}`,
              username: item.username,
              roundId: room.roundId,
              game: room.game,
              amount: item.amount,
              autoCashout: item.autoCashout,
              status: 'active',
              payout: 0,
              cashoutMultiplier: null,
              walletTxId: '',
              createdAt: new Date(nowMs).toISOString(),
            };
            room.activeBets.unshift(simBet);
            broadcastRoom(room, {
              type: 'bet',
              game: room.game,
              roundId: room.roundId,
              ...serializeBetPublic(simBet),
            });
          } else {
            remaining.push(item);
          }
        }
        room.pendingSimBets = remaining;
      }

      if (nowMs >= room.deadlineMs) {
        room.pendingSimBets = [];
        room.status = 'running';
        room.startedAtMs = nowMs;
        room.multiplier = 1.0;

        const stored = roundsById.get(room.roundId);
        if (stored) {
          stored.status = 'running';
          stored.startedAt = new Date(nowMs).toISOString();
        }

        broadcastRoom(room, {
          type: 'started',
          ...buildRoomSnapshot(room),
        });
      } else if (nowMs - room.lastStateBroadcastMs >= 300) {
        room.lastStateBroadcastMs = nowMs;
        broadcastRoom(room, {
          type: 'state',
          game: room.game,
          roundId: room.roundId,
          roundNumber: room.roundNumber,
          status: room.status,
          countdown: Number(Math.max(0, (room.deadlineMs - nowMs) / 1000).toFixed(1)),
          seedHash: room.seedHash,
          connectedPlayers: getRoomConnectedPlayers(room),
        });
      }
      continue;
    }

    if (room.status === 'running') {
      const elapsedSec = Math.max(0, (nowMs - room.startedAtMs) / 1000);
      const nextMult = Number((1.0 + Math.pow(elapsedSec, 1.35) * 0.12).toFixed(2));

      if (nextMult >= room.crashPoint) {
        for (const bet of room.activeBets) {
          if (bet.status === 'active' && bet.autoCashout !== null && bet.autoCashout <= room.crashPoint) {
            settleBetWin(bet, bet.autoCashout, true, room);
          }
        }

        room.multiplier = room.crashPoint;
        room.status = 'crashed';
        room.crashedAtMs = nowMs;

        for (const bet of room.activeBets) {
          if (bet.status === 'active') {
            bet.status = 'lost';
            const account = accountsById.get(bet.accountId);
            if (account) {
              const tx = account.history.find((t) => t.id === bet.walletTxId);
              if (tx) {
                tx.status = 'Lost';
                tx.detail = `Slip ${bet.slot} · Stake: KES ${bet.amount.toFixed(0)} | Crashed @ ${room.crashPoint.toFixed(2)}x`;
              }
            }
          }
        }

        const stored = roundsById.get(room.roundId);
        if (stored) {
          stored.status = 'crashed';
          stored.endedAt = new Date(nowMs).toISOString();
          room.recentRounds.unshift(stored);
          room.recentRounds = room.recentRounds.slice(0, 30);
        }

        room.previousBets = room.activeBets.map((b) => ({ ...b }));
        room.previousCrashPoint = room.crashPoint;

        broadcastRoom(room, {
          type: 'crashed',
          game: room.game,
          roundId: room.roundId,
          roundNumber: room.roundNumber,
          multiplier: room.crashPoint,
          connectedPlayers: getRoomConnectedPlayers(room),
          previousBets: room.previousBets.map(serializeBetPublic),
          previousCrashPoint: room.previousCrashPoint,
          topWins: room.topWins.slice(0, 20).map(serializeBetPublic),
          recentRounds: room.recentRounds.slice(0, 20).map(sanitizeRoundForPublic),
        });
      } else {
        room.multiplier = nextMult;
        for (const bet of room.activeBets) {
          if (bet.status === 'active' && bet.autoCashout !== null && bet.autoCashout <= nextMult) {
            settleBetWin(bet, bet.autoCashout, true, room);
          }
        }

        broadcastRoom(room, {
          type: 'tick',
          game: room.game,
          roundId: room.roundId,
          roundNumber: room.roundNumber,
          status: room.status,
          multiplier: room.multiplier,
          connectedPlayers: getRoomConnectedPlayers(room),
        });
      }
      continue;
    }

    if (room.status === 'crashed') {
      if (nowMs - room.crashedAtMs >= ROUND_PAUSE_SECONDS * 1000) {
        startNewRound(room);
        broadcastRoom(room, {
          type: 'new_round',
          ...buildRoomSnapshot(room),
        });
      }
    }
  }
}

async function startServer() {
  const app = express();
  app.use(
    express.json({
      verify: (req, _res, buf) => {
        (req as Request & { rawBody?: Buffer }).rawBody = buf;
      },
    })
  );

  const adminUsername = process.env.ADMIN_USERNAME;
  const adminPassword = process.env.ADMIN_PASSWORD;
  if (adminUsername && adminPassword && !accountIdByUsername.has(adminUsername.toLowerCase())) {
    createAccount({
      username: adminUsername,
      passwordHash: hashPassword(adminPassword),
      isGuest: false,
      isAdmin: true,
    });
  }

  type SmsChannel =
    | 'africastalking'
    | 'twilio'
    | 'termii'
    | 'vonage'
    | 'textbelt'
    | 'webhook'
    | 'preview_no_carrier';

  function getTwilioConfig() {
    const accountSid = (
      process.env.TWILIO_ACCOUNT_SID ||
      process.env.TWILIO_SID ||
      ''
    ).trim();
    const authToken = (
      process.env.TWILIO_AUTH_TOKEN ||
      process.env.TWILIO_TOKEN ||
      ''
    ).trim();
    const rawFrom = (
      process.env.TWILIO_FROM_NUMBER ||
      process.env.TWILIO_PHONE_NUMBER ||
      process.env.TWILIO_NUMBER ||
      process.env.TWILIO_SENDER_ID ||
      ''
    ).trim();
    const fromNumber = rawFrom
      ? /^\d{8,15}$/.test(rawFrom)
        ? `+${rawFrom}`
        : rawFrom
      : '';
    const messagingServiceSid = (process.env.TWILIO_MESSAGING_SERVICE_SID || '').trim();
    const missing: string[] = [];
    if (!accountSid) missing.push('TWILIO_ACCOUNT_SID');
    if (!authToken) missing.push('TWILIO_AUTH_TOKEN');
    if (!fromNumber && !messagingServiceSid) {
      missing.push('TWILIO_FROM_NUMBER or TWILIO_MESSAGING_SERVICE_SID');
    }
    return {
      configured: Boolean(accountSid && authToken && (fromNumber || messagingServiceSid)),
      accountSid,
      authToken,
      fromNumber,
      messagingServiceSid,
      missing,
    };
  }

  function getConfiguredSmsProvider(): { configured: boolean; channel: SmsChannel; providerLabel: string } {
    const twilioCfg = getTwilioConfig();
    if (twilioCfg.configured) {
      return { configured: true, channel: 'twilio', providerLabel: 'Twilio SMS' };
    }
    if (process.env.AFRICASTALKING_API_KEY?.trim() && process.env.AFRICASTALKING_USERNAME?.trim()) {
      return { configured: true, channel: 'africastalking', providerLabel: "Africa's Talking SMS" };
    }
    if (process.env.TERMII_API_KEY?.trim()) {
      return { configured: true, channel: 'termii', providerLabel: 'Termii SMS' };
    }
    if (process.env.VONAGE_API_KEY?.trim() && process.env.VONAGE_API_SECRET?.trim()) {
      return { configured: true, channel: 'vonage', providerLabel: 'Vonage SMS' };
    }
    if (process.env.TEXTBELT_API_KEY?.trim()) {
      return { configured: true, channel: 'textbelt', providerLabel: 'Textbelt SMS' };
    }
    if (process.env.SMS_WEBHOOK_URL?.trim()) {
      return { configured: true, channel: 'webhook', providerLabel: 'Custom SMS Gateway' };
    }
    return {
      configured: false,
      channel: 'preview_no_carrier',
      providerLabel: 'No Carrier Key Configured',
    };
  }

  async function dispatchRealSms(params: {
    toE164: string;
    country: SupportedCountry;
    messageBody: string;
  }): Promise<
    | {
        ok: true;
        isRealSms: boolean;
        channel: SmsChannel;
        providerLabel: string;
        messageBody: string;
        messageId?: string;
      }
    | { ok: false; channel: SmsChannel; errorMessage: string }
  > {
    const { messageBody } = params;
    const active = getConfiguredSmsProvider();

    if (!active.configured) {
      return {
        ok: true,
        isRealSms: false,
        channel: 'preview_no_carrier',
        providerLabel: active.providerLabel,
        messageBody,
      };
    }

    try {
      // 1. Africa's Talking (Kenya / Ghana / Côte d'Ivoire)
      if (active.channel === 'africastalking') {
        const username = process.env.AFRICASTALKING_USERNAME!;
        const apiKey = process.env.AFRICASTALKING_API_KEY!;
        const senderId = process.env.AFRICASTALKING_SENDER_ID;
        const endpoint =
          username.toLowerCase() === 'sandbox'
            ? 'https://api.sandbox.africastalking.com/version1/messaging'
            : 'https://api.africastalking.com/version1/messaging';
        const form = new URLSearchParams({
          username,
          to: params.toE164,
          message: messageBody,
        });
        if (senderId) form.set('from', senderId);

        const resp = await fetch(endpoint, {
          method: 'POST',
          headers: {
            Accept: 'application/json',
            'Content-Type': 'application/x-www-form-urlencoded',
            apiKey,
          },
          body: form.toString(),
        });
        const data = (await resp.json().catch(() => ({}))) as {
          SMSMessageData?: { Message?: string; Recipients?: Array<{ statusCode?: number; status?: string }> };
        };
        const rec = data.SMSMessageData?.Recipients?.[0];
        const okStatus = rec?.statusCode === 100 || rec?.statusCode === 101 || rec?.statusCode === 102;
        if (resp.ok && okStatus) {
          return {
            ok: true,
            isRealSms: true,
            channel: 'africastalking',
            providerLabel: active.providerLabel,
            messageBody,
          };
        }
        return {
          ok: false,
          channel: 'africastalking',
          errorMessage: `Africa's Talking SMS failed: ${rec?.status || data.SMSMessageData?.Message || resp.status}`,
        };
      }

      // 2. Twilio Programmable SMS
      if (active.channel === 'twilio') {
        const twilioCfg = getTwilioConfig();
        const authHeader = Buffer.from(
          `${twilioCfg.accountSid}:${twilioCfg.authToken}`
        ).toString('base64');
        const form = new URLSearchParams({ To: params.toE164, Body: messageBody });
        if (twilioCfg.messagingServiceSid) {
          form.set('MessagingServiceSid', twilioCfg.messagingServiceSid);
        } else if (twilioCfg.fromNumber) {
          form.set('From', twilioCfg.fromNumber);
        }
        const resp = await fetch(
          `https://api.twilio.com/2010-04-01/Accounts/${encodeURIComponent(twilioCfg.accountSid)}/Messages.json`,
          {
            method: 'POST',
            headers: {
              Authorization: `Basic ${authHeader}`,
              'Content-Type': 'application/x-www-form-urlencoded',
            },
            body: form.toString(),
          }
        );
        const data = (await resp.json().catch(() => ({}))) as {
          sid?: string;
          status?: string;
          code?: number;
          message?: string;
        };
        if (resp.ok && data.sid) {
          return {
            ok: true,
            isRealSms: true,
            channel: 'twilio',
            providerLabel: active.providerLabel,
            messageBody,
            messageId: data.sid,
          };
        }
        return {
          ok: false,
          channel: 'twilio',
          errorMessage: `Twilio SMS failed (${data.code ?? resp.status}): ${data.message || 'Check Twilio credentials and sender number'}`,
        };
      }

      // 3. Termii SMS
      if (active.channel === 'termii') {
        const resp = await fetch('https://api.ng.termii.com/api/sms/send', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            api_key: process.env.TERMII_API_KEY,
            to: params.toE164.replace(/^\+/, ''),
            from: process.env.TERMII_SENDER_ID || 'Luckymate',
            sms: messageBody,
            type: 'plain',
            channel: process.env.TERMII_CHANNEL || 'generic',
          }),
        });
        const data = (await resp.json().catch(() => ({}))) as { code?: string; message?: string };
        if (resp.ok && (data.code === 'ok' || data.message === 'Successfully Sent')) {
          return {
            ok: true,
            isRealSms: true,
            channel: 'termii',
            providerLabel: active.providerLabel,
            messageBody,
          };
        }
        return {
          ok: false,
          channel: 'termii',
          errorMessage: `Termii SMS failed: ${data.message || resp.status}`,
        };
      }

      // 4. Vonage SMS
      if (active.channel === 'vonage') {
        const resp = await fetch('https://rest.nexmo.com/sms/json', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            api_key: process.env.VONAGE_API_KEY,
            api_secret: process.env.VONAGE_API_SECRET,
            to: params.toE164.replace(/^\+/, ''),
            from: process.env.VONAGE_FROM || 'Luckymate',
            text: messageBody,
          }),
        });
        const data = (await resp.json().catch(() => ({}))) as {
          messages?: Array<{ status?: string; 'error-text'?: string }>;
        };
        const first = data.messages?.[0];
        if (resp.ok && first?.status === '0') {
          return {
            ok: true,
            isRealSms: true,
            channel: 'vonage',
            providerLabel: active.providerLabel,
            messageBody,
          };
        }
        return {
          ok: false,
          channel: 'vonage',
          errorMessage: `Vonage SMS failed: ${first?.['error-text'] || resp.status}`,
        };
      }

      // 5. Textbelt SMS
      if (active.channel === 'textbelt') {
        const resp = await fetch('https://textbelt.com/text', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            phone: params.toE164,
            message: messageBody,
            key: process.env.TEXTBELT_API_KEY,
          }),
        });
        const data = (await resp.json().catch(() => ({}))) as { success?: boolean; error?: string };
        if (resp.ok && data.success) {
          return {
            ok: true,
            isRealSms: true,
            channel: 'textbelt',
            providerLabel: active.providerLabel,
            messageBody,
          };
        }
        return {
          ok: false,
          channel: 'textbelt',
          errorMessage: `Textbelt SMS failed: ${data.error || resp.status}`,
        };
      }

      // 6. Custom SMS Webhook
      const webhookHeaders: Record<string, string> = { 'Content-Type': 'application/json' };
      if (process.env.SMS_WEBHOOK_TOKEN) {
        webhookHeaders.Authorization = `Bearer ${process.env.SMS_WEBHOOK_TOKEN}`;
      }
      const resp = await fetch(process.env.SMS_WEBHOOK_URL!, {
        method: 'POST',
        headers: webhookHeaders,
        body: JSON.stringify({
          to: params.toE164,
          country: params.country,
          message: messageBody,
        }),
      });
      if (resp.ok) {
        return {
          ok: true,
          isRealSms: true,
          channel: 'webhook',
          providerLabel: active.providerLabel,
          messageBody,
        };
      }
      return {
        ok: false,
        channel: 'webhook',
        errorMessage: `SMS webhook returned HTTP ${resp.status}`,
      };
    } catch (err) {
      return {
        ok: false,
        channel: active.channel,
        errorMessage: `SMS carrier request error: ${err instanceof Error ? err.message : 'Network error'}`,
      };
    }
  }

  type EmailChannel =
    | 'resend'
    | 'sendgrid'
    | 'brevo'
    | 'gmail_smtp'
    | 'custom_smtp'
    | 'email_webhook'
    | 'unconfigured';

  function getConfiguredEmailProvider(): {
    configured: boolean;
    channel: EmailChannel;
    providerLabel: string;
    fromAddress: string;
  } {
    const resendKey = (process.env.RESEND_API_KEY || '').trim();
    const sendgridKey = (process.env.SENDGRID_API_KEY || '').trim();
    const brevoKey = (process.env.BREVO_API_KEY || '').trim();
    const gmailUser = (process.env.GMAIL_USER || '').trim();
    const gmailPass = (process.env.GMAIL_APP_PASSWORD || '').trim();
    const smtpHost = (process.env.SMTP_HOST || '').trim();
    const smtpUser = (process.env.SMTP_USER || '').trim();
    const smtpPass = (process.env.SMTP_PASS || '').trim();
    const webhookUrl = (process.env.EMAIL_WEBHOOK_URL || '').trim();
    const customFrom = (process.env.EMAIL_FROM || '').trim();

    if (resendKey) {
      return {
        configured: true,
        channel: 'resend',
        providerLabel: 'Resend Email',
        fromAddress: customFrom || 'Luckymate <onboarding@resend.dev>',
      };
    }
    if (sendgridKey) {
      return {
        configured: true,
        channel: 'sendgrid',
        providerLabel: 'SendGrid Email',
        fromAddress: customFrom || 'no-reply@luckymate.app',
      };
    }
    if (brevoKey) {
      return {
        configured: true,
        channel: 'brevo',
        providerLabel: 'Brevo Email',
        fromAddress: customFrom || 'no-reply@luckymate.app',
      };
    }
    if (gmailUser && gmailPass) {
      return {
        configured: true,
        channel: 'gmail_smtp',
        providerLabel: 'Gmail SMTP',
        fromAddress: customFrom || `Luckymate <${gmailUser}>`,
      };
    }
    if (smtpHost && smtpUser && smtpPass) {
      return {
        configured: true,
        channel: 'custom_smtp',
        providerLabel: 'SMTP Email',
        fromAddress: customFrom || smtpUser,
      };
    }
    if (webhookUrl) {
      return {
        configured: true,
        channel: 'email_webhook',
        providerLabel: 'Email Webhook',
        fromAddress: customFrom || 'no-reply@luckymate.app',
      };
    }
    return {
      configured: false,
      channel: 'unconfigured',
      providerLabel: 'No Email Provider Configured',
      fromAddress: 'no-reply@luckymate.app',
    };
  }

  async function dispatchRegistrationEmail(params: {
    toEmail: string;
    phone: string;
    username: string;
    country: SupportedCountry;
  }): Promise<
    | { ok: true; isRealEmail: boolean; channel: EmailChannel; providerLabel: string }
    | { ok: false; channel: EmailChannel; errorMessage: string }
  > {
    const active = getConfiguredEmailProvider();
    if (!active.configured) {
      return {
        ok: true,
        isRealEmail: false,
        channel: 'unconfigured',
        providerLabel: active.providerLabel,
      };
    }

    const subject = 'Luckymate: Account Registered Successfully';
    const textBody = [
      `Hello ${params.username},`,
      '',
      `Your Luckymate account (${params.phone}) has been successfully registered!`,
      `Country: ${params.country}`,
      '',
      'You can now log in with your phone number and password to start playing.',
      '',
      'If you did not create this account, please contact Luckymate support.',
    ].join('\n');

    const htmlBody = `
      <div style="font-family:Arial,sans-serif;background:#0e141d;color:#f8fafc;padding:24px;border-radius:12px;max-width:480px;margin:0 auto;">
        <h2 style="margin:0 0 8px;color:#7bc114;">Account Registered Successfully</h2>
        <p style="margin:0 0 14px;color:#cbd5e1;font-size:14px;">
          Hello <strong>${params.username}</strong>, your Luckymate account has been registered and is ready to use.
        </p>
        <div style="background:#18212e;border:1px solid #2b3a4f;border-radius:10px;padding:14px;margin:14px 0;font-size:13px;color:#e2e8f0;">
          <div><strong>Phone:</strong> ${params.phone}</div>
          <div style="margin-top:4px;"><strong>Country:</strong> ${params.country}</div>
        </div>
        <p style="margin:0;color:#94a3b8;font-size:12px;">
          Log in anytime with your registered phone number and password.
        </p>
      </div>
    `;

    try {
      if (active.channel === 'resend') {
        const resp = await fetch('https://api.resend.com/emails', {
          method: 'POST',
          headers: {
            Authorization: `Bearer ${(process.env.RESEND_API_KEY || '').trim()}`,
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({
            from: active.fromAddress,
            to: [params.toEmail],
            subject,
            text: textBody,
            html: htmlBody,
          }),
        });
        const data = (await resp.json().catch(() => ({}))) as { message?: string; id?: string };
        if (resp.ok) {
          return { ok: true, isRealEmail: true, channel: 'resend', providerLabel: active.providerLabel };
        }
        return {
          ok: false,
          channel: 'resend',
          errorMessage: `Resend error: ${data.message || resp.status}`,
        };
      }

      if (active.channel === 'sendgrid') {
        const resp = await fetch('https://api.sendgrid.com/v3/mail/send', {
          method: 'POST',
          headers: {
            Authorization: `Bearer ${(process.env.SENDGRID_API_KEY || '').trim()}`,
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({
            personalizations: [{ to: [{ email: params.toEmail }] }],
            from: { email: active.fromAddress.replace(/^.*<([^>]+)>$/, '$1') },
            subject,
            content: [
              { type: 'text/plain', value: textBody },
              { type: 'text/html', value: htmlBody },
            ],
          }),
        });
        if (resp.ok) {
          return { ok: true, isRealEmail: true, channel: 'sendgrid', providerLabel: active.providerLabel };
        }
        const errTxt = await resp.text().catch(() => String(resp.status));
        return { ok: false, channel: 'sendgrid', errorMessage: `SendGrid error: ${errTxt}` };
      }

      if (active.channel === 'brevo') {
        const senderEmail = active.fromAddress.replace(/^.*<([^>]+)>$/, '$1');
        const resp = await fetch('https://api.brevo.com/v3/smtp/email', {
          method: 'POST',
          headers: {
            'api-key': (process.env.BREVO_API_KEY || '').trim(),
            'Content-Type': 'application/json',
          },
          body: JSON.stringify({
            sender: { name: 'Luckymate', email: senderEmail },
            to: [{ email: params.toEmail }],
            subject,
            textContent: textBody,
            htmlContent: htmlBody,
          }),
        });
        if (resp.ok) {
          return { ok: true, isRealEmail: true, channel: 'brevo', providerLabel: active.providerLabel };
        }
        const errData = (await resp.json().catch(() => ({}))) as { message?: string };
        return { ok: false, channel: 'brevo', errorMessage: `Brevo error: ${errData.message || resp.status}` };
      }

      if (active.channel === 'gmail_smtp' || active.channel === 'custom_smtp') {
        const isGmail = active.channel === 'gmail_smtp';
        const host = isGmail ? 'smtp.gmail.com' : (process.env.SMTP_HOST || '').trim();
        const port = isGmail ? 465 : Number(process.env.SMTP_PORT || 465);
        const secure = isGmail
          ? true
          : String(process.env.SMTP_SECURE || (port === 465 ? 'true' : 'false')).toLowerCase() === 'true';
        const user = isGmail
          ? (process.env.GMAIL_USER || '').trim()
          : (process.env.SMTP_USER || '').trim();
        const pass = isGmail
          ? (process.env.GMAIL_APP_PASSWORD || '').trim()
          : (process.env.SMTP_PASS || '').trim();

        const transporter = nodemailer.createTransport({
          host,
          port,
          secure,
          auth: { user, pass },
        });
        await transporter.sendMail({
          from: active.fromAddress,
          to: params.toEmail,
          subject,
          text: textBody,
          html: htmlBody,
        });
        return {
          ok: true,
          isRealEmail: true,
          channel: active.channel,
          providerLabel: active.providerLabel,
        };
      }

      const webhookHeaders: Record<string, string> = { 'Content-Type': 'application/json' };
      if (process.env.EMAIL_WEBHOOK_TOKEN) {
        webhookHeaders.Authorization = `Bearer ${process.env.EMAIL_WEBHOOK_TOKEN.trim()}`;
      }
      const resp = await fetch((process.env.EMAIL_WEBHOOK_URL || '').trim(), {
        method: 'POST',
        headers: webhookHeaders,
        body: JSON.stringify({
          to: params.toEmail,
          subject,
          text: textBody,
          html: htmlBody,
        }),
      });
      if (resp.ok) {
        return {
          ok: true,
          isRealEmail: true,
          channel: 'email_webhook',
          providerLabel: active.providerLabel,
        };
      }
      return {
        ok: false,
        channel: 'email_webhook',
        errorMessage: `Email webhook returned HTTP ${resp.status}`,
      };
    } catch (err) {
      return {
        ok: false,
        channel: active.channel,
        errorMessage: `Email send error: ${err instanceof Error ? err.message : 'SMTP/Network error'}`,
      };
    }
  }

  function findAccountByIdentifier(identifier: string, preferredCountry?: SupportedCountry): AccountRecord | undefined {
    const clean = identifier.trim();
    if (clean.includes('@')) {
      const byEmailId = accountIdByEmail.get(clean.toLowerCase());
      if (byEmailId && accountsById.has(byEmailId)) {
        return accountsById.get(byEmailId);
      }
    }
    const byUsernameId = accountIdByUsername.get(clean.toLowerCase());
    if (byUsernameId && accountsById.has(byUsernameId)) {
      return accountsById.get(byUsernameId);
    }
    const candidates: SupportedCountry[] = preferredCountry
      ? [preferredCountry, 'Kenya', 'Ghana', "Côte d'Ivoire"]
      : ['Kenya', 'Ghana', "Côte d'Ivoire"];
    for (const c of candidates) {
      const normalized = normalizePhoneNumber(clean, c);
      if (normalized.ok) {
        const id = accountIdByPhone.get(normalized.e164);
        if (id && accountsById.has(id)) {
          return accountsById.get(id);
        }
        // Fallback for Côte d'Ivoire leading-zero differences
        if (c === "Côte d'Ivoire") {
          const withoutZero = normalized.localDigits.startsWith('0')
            ? `+225${normalized.localDigits.slice(1)}`
            : `+2250${normalized.localDigits}`;
          const altId = accountIdByPhone.get(withoutZero);
          if (altId && accountsById.has(altId)) {
            return accountsById.get(altId);
          }
        }
      }
    }
    // Last-resort unambiguous digit suffix lookup across registered accounts
    const digitsOnly = clean.replace(/\D/g, '');
    if (digitsOnly.length >= 8) {
      const tail9 = digitsOnly.slice(-9);
      const matches: AccountRecord[] = [];
      for (const acc of accountsById.values()) {
        if (!acc.isGuest && acc.phone) {
          const accDigits = acc.phone.replace(/\D/g, '');
          if (accDigits === digitsOnly || accDigits.endsWith(tail9)) {
            matches.push(acc);
          }
        }
      }
      if (matches.length === 1) {
        return matches[0];
      }
    }
    return undefined;
  }

  function extractPhoneKeys(raw: string, preferredCountry?: SupportedCountry): Set<string> {
    const keys = new Set<string>();
    const clean = raw.trim();
    if (!clean) return keys;
    const candidates: SupportedCountry[] = preferredCountry
      ? [preferredCountry, 'Kenya', 'Ghana', "Côte d'Ivoire"]
      : ['Kenya', 'Ghana', "Côte d'Ivoire"];
    for (const c of candidates) {
      const normalized = normalizePhoneNumber(clean, c);
      if (normalized.ok) {
        keys.add(normalized.e164);
        if (c === "Côte d'Ivoire") {
          const alt = normalized.localDigits.startsWith('0')
            ? `+225${normalized.localDigits.slice(1)}`
            : `+2250${normalized.localDigits}`;
          keys.add(alt);
        }
      }
    }
    const digits = clean.replace(/\D/g, '');
    if (digits.length >= 8) {
      keys.add(`tail:${digits.slice(-9)}`);
    }
    return keys;
  }

  function phonesMatch(
    rawA: string,
    countryA: SupportedCountry | undefined,
    rawB: string,
    countryB: SupportedCountry | undefined
  ): boolean {
    const keysA = extractPhoneKeys(rawA, countryA);
    const keysB = extractPhoneKeys(rawB, countryB);
    for (const k of keysA) {
      if (keysB.has(k)) return true;
    }
    return false;
  }

  interface SavedProfilePayload {
    phone?: unknown;
    email?: unknown;
    emailVerified?: unknown;
    country?: unknown;
    username?: unknown;
    registeredAt?: unknown;
    passwordHash?: unknown;
    passwordRecovery?: unknown;
  }

  function resolveMatchingSavedProfile(
    identifier: string,
    preferredCountry: SupportedCountry | undefined,
    rawSaved: unknown,
    rawSavedList?: unknown
  ): {
    phoneE164: string;
    email?: string;
    country: SupportedCountry;
    username: string;
    passwordHash: string | null;
    passwordRecovery: string | null;
    createdAt?: string;
  } | null {
    const candidatesList: unknown[] = [];
    if (Array.isArray(rawSavedList)) {
      candidatesList.push(...rawSavedList);
    }
    if (rawSaved && typeof rawSaved === 'object') {
      candidatesList.push(rawSaved);
    }
    const cleanId = identifier.trim().toLowerCase();
    for (const item of candidatesList) {
      if (!item || typeof item !== 'object') continue;
      const sp = item as SavedProfilePayload;
      if (sp.emailVerified === false) continue;
      const spPhone = typeof sp.phone === 'string' ? sp.phone.trim() : '';
      const spEmail = typeof sp.email === 'string' ? sp.email.trim().toLowerCase() : '';
      if (!spPhone) continue;
      const spCountry = parseSupportedCountry(sp.country ?? preferredCountry);
      const emailMatched = Boolean(cleanId && spEmail && cleanId === spEmail);
      if (!emailMatched && !phonesMatch(identifier, preferredCountry, spPhone, spCountry)) {
        continue;
      }
      const normalizedSp = normalizePhoneNumber(spPhone, spCountry);
      if (!normalizedSp.ok) continue;

      const rawUsername = typeof sp.username === 'string' ? sp.username.trim() : '';
      const safeUsername =
        rawUsername && !accountIdByUsername.has(rawUsername.toLowerCase())
          ? rawUsername
          : `Member-${crypto.randomBytes(2).toString('hex').toUpperCase()}`;
      const spHash =
        typeof sp.passwordHash === 'string' && sp.passwordHash.includes('$')
          ? sp.passwordHash.trim()
          : null;
      const spRecovery =
        typeof sp.passwordRecovery === 'string' && sp.passwordRecovery.startsWith('v1:')
          ? sp.passwordRecovery.trim()
          : null;
      const spCreatedAt =
        typeof sp.registeredAt === 'string' && sp.registeredAt.trim()
          ? sp.registeredAt.trim()
          : undefined;

      return {
        phoneE164: normalizedSp.e164,
        email: spEmail || undefined,
        country: spCountry,
        username: safeUsername,
        passwordHash: spHash,
        passwordRecovery: spRecovery,
        createdAt: spCreatedAt,
      };
    }
    return null;
  }

  // ---------------- AUTHENTICATION API ----------------

  app.get('/api/sms/status', (_req: Request, res: Response) => {
    const status = getConfiguredSmsProvider();
    const twilioCfg = getTwilioConfig();
    res.json({
      configured: status.configured,
      channel: status.channel,
      providerLabel: status.providerLabel,
      missingTwilioVars: twilioCfg.configured ? [] : twilioCfg.missing,
    });
  });

  app.get('/api/email/status', (_req: Request, res: Response) => {
    const status = getConfiguredEmailProvider();
    res.json({
      configured: status.configured,
      channel: status.channel,
      providerLabel: status.providerLabel,
    });
  });

  app.post('/api/register', async (req: Request, res: Response) => {
    const body = req.body ?? {};
    const country = parseSupportedCountry(body.country);
    const rawPhone = String(body.phone ?? '').trim();
    const rawEmail = String(body.email ?? '').trim();
    const password = String(body.password ?? '');
    const cleanPassword = password.trim();
    const confirmPassword = String(body.confirmPassword ?? '').trim();
    const acceptedTerms = body.acceptedTerms === undefined ? true : Boolean(body.acceptedTerms);

    const normalized = normalizePhoneNumber(rawPhone, country);
    if (!normalized.ok) {
      res.status(400).json({ message: normalized.message });
      return;
    }

    let validEmail: string | undefined;
    if (rawEmail) {
      const emailCheck = normalizeEmail(rawEmail);
      if (!emailCheck.ok) {
        res.status(400).json({ message: emailCheck.message });
        return;
      }
      validEmail = emailCheck.email;
    }

    if (cleanPassword.length < 6 || cleanPassword.length > 100) {
      res.status(400).json({ message: 'Password must be at least 6 characters.' });
      return;
    }

    if (body.confirmPassword !== undefined && cleanPassword !== confirmPassword) {
      res.status(400).json({ message: 'Passwords do not match. Check Confirm Password.' });
      return;
    }

    if (!acceptedTerms) {
      res.status(400).json({
        message: 'You must agree to the Terms & Conditions, Privacy policy and confirm you are 18+.',
      });
      return;
    }

    const existingPhoneId = accountIdByPhone.get(normalized.e164);
    let existingByPhone = existingPhoneId ? accountsById.get(existingPhoneId) : undefined;
    if (!existingByPhone) {
      for (const acc of accountsById.values()) {
        if (!acc.isGuest && acc.phone && phonesMatch(rawPhone, country, acc.phone, acc.country)) {
          existingByPhone = acc;
          break;
        }
      }
    }
    if (!existingByPhone) {
      const savedExisting = resolveMatchingSavedProfile(
        normalized.e164,
        country,
        body.savedProfile,
        body.savedProfiles
      );
      if (savedExisting && savedExisting.passwordHash) {
        existingByPhone = createAccount({
          username: savedExisting.username,
          phone: savedExisting.phoneE164,
          email: savedExisting.email,
          emailVerified: true,
          country: savedExisting.country,
          passwordHash: savedExisting.passwordHash,
          encryptedPassword: savedExisting.passwordRecovery,
          isGuest: false,
          createdAt: savedExisting.createdAt,
        });
      }
    }
    if (existingByPhone) {
      res.status(409).json({
        alreadyRegistered: true,
        message:
          'This phone number is already registered. You cannot register the same number again. Please Log In or use Forgot Password.',
      });
      return;
    }

    if (validEmail) {
      const existingEmailId = accountIdByEmail.get(validEmail);
      const existingByEmail = existingEmailId ? accountsById.get(existingEmailId) : undefined;
      if (existingByEmail) {
        res.status(409).json({
          alreadyRegistered: true,
          message: 'This email address is already registered. Please Login instead.',
        });
        return;
      }
    }

    const rawRefCode = String(body.referralCode ?? '')
      .trim()
      .toUpperCase()
      .replace(/[^A-Z0-9]/g, '');
    let referrerAccount: AccountRecord | undefined;
    if (rawRefCode) {
      const refOwnerId = accountIdByReferralCode.get(rawRefCode);
      const foundOwner = refOwnerId ? accountsById.get(refOwnerId) : undefined;
      if (
        foundOwner &&
        !foundOwner.isGuest &&
        foundOwner.phone !== normalized.e164 &&
        (!validEmail || foundOwner.email !== validEmail)
      ) {
        referrerAccount = foundOwner;
      }
    }

    const memberHandle = `Member-${crypto.randomBytes(2).toString('hex').toUpperCase()}`;
    const encryptedPwd = encryptRecoverablePassword(cleanPassword, normalized.e164);
    const account = createAccount({
      username: memberHandle,
      phone: normalized.e164,
      email: validEmail,
      emailVerified: true,
      otpCodeHash: null,
      otpExpiresAt: null,
      otpAttempts: 0,
      country,
      passwordHash: hashPassword(cleanPassword),
      encryptedPassword: encryptedPwd,
      isGuest: false,
      referredByAccountId: referrerAccount?.id ?? null,
      referredByCode: referrerAccount?.referralCode ?? null,
    });

    if (referrerAccount) {
      if (!Array.isArray(referrerAccount.referrals)) {
        referrerAccount.referrals = [];
      }
      referrerAccount.referrals.unshift({
        id: crypto.randomUUID(),
        referredAccountId: account.id,
        referredUsername: account.username,
        maskedPhone: maskPhone(normalized.e164),
        joinedAt: account.createdAt,
        status: 'pending_deposit',
        rewardUsd: REFERRAL_REWARD_USD,
        rewardBase: Number((REFERRAL_REWARD_USD * BASE_KES_PER_USD).toFixed(2)),
      });
      referrerAccount.referrals = referrerAccount.referrals.slice(0, 100);
      referrerAccount.updatedAt = Date.now();
      saveStoreNow();
    }

    const welcomeSms = `Your Luckymate account (${account.phone}) is registered! Share your invite code ${account.referralCode} with friends and earn $${REFERRAL_REWARD_USD} USD when they deposit $${REFERRAL_MIN_DEPOSIT_USD} USD.`;
    const smsDispatch = await dispatchRealSms({
      toE164: normalized.e164,
      country,
      messageBody: welcomeSms,
    }).catch(() => ({
      ok: false as const,
      channel: 'unconfigured' as const,
      errorMessage: 'SMS dispatch failed',
    }));

    let emailSent = false;
    let emailProviderLabel = getConfiguredEmailProvider().providerLabel;
    if (validEmail) {
      const emailDispatch = await dispatchRegistrationEmail({
        toEmail: validEmail,
        phone: normalized.e164,
        username: account.username,
        country,
      });
      if (!emailDispatch.ok) {
        console.warn('[Registration Email Dispatch]', emailDispatch.errorMessage);
        emailProviderLabel = 'Email Delivery Error';
      } else {
        emailSent = emailDispatch.isRealEmail;
        emailProviderLabel = emailDispatch.providerLabel;
      }
    }

    const smsSent = smsDispatch.ok && smsDispatch.isRealSms;
    res.json({
      success: true,
      requiresEmailVerification: false,
      requiresLogin: true,
      activated: true,
      username: account.username,
      phone: account.phone,
      email: account.email,
      country,
      createdAt: account.createdAt,
      passwordHash: account.passwordHash ?? undefined,
      passwordRecovery: account.encryptedPassword ?? undefined,
      referralCode: account.referralCode,
      referredByCode: account.referredByCode ?? null,
      referrerUsername: referrerAccount?.username ?? null,
      smsSent,
      smsMessageId: smsDispatch.ok ? smsDispatch.messageId : undefined,
      emailSent,
      emailProviderLabel,
      providerLabel: smsDispatch.ok ? smsDispatch.providerLabel : 'SMS Delivery Error',
      message: 'Account registered! Log in with your phone number and password.',
    });
  });

  app.get('/api/referral/validate/:code', (req: Request, res: Response) => {
    const code = String(req.params.code || '')
      .trim()
      .toUpperCase()
      .replace(/[^A-Z0-9]/g, '');
    const ownerId = code ? accountIdByReferralCode.get(code) : undefined;
    const owner = ownerId ? accountsById.get(ownerId) : undefined;
    if (!owner || owner.isGuest) {
      res.json({
        valid: false,
        rewardUsd: REFERRAL_REWARD_USD,
        minDepositUsd: REFERRAL_MIN_DEPOSIT_USD,
      });
      return;
    }
    res.json({
      valid: true,
      code: owner.referralCode,
      referrerUsername: owner.username,
      rewardUsd: REFERRAL_REWARD_USD,
      minDepositUsd: REFERRAL_MIN_DEPOSIT_USD,
    });
  });

  app.get('/api/referral/summary', (req: Request, res: Response) => {
    const { account } = resolveRequestAccount(req, res);
    if (account.isGuest) {
      res.status(401).json({
        message: 'Log in or register to access your personal invite link and referral rewards.',
      });
      return;
    }
    if (!account.referralCode) {
      account.referralCode = generateUniqueReferralCode();
      accountIdByReferralCode.set(account.referralCode, account.id);
      saveStoreNow();
    }
    res.json(buildReferralSummary(account));
  });

  app.post('/api/login', (req: Request, res: Response) => {
    const body = req.body ?? {};
    const identifier = String(body.phone ?? body.email ?? body.username ?? '').trim();
    const password = String(body.password ?? '');
    const preferredCountry = body.country ? parseSupportedCountry(body.country) : undefined;

    let account = findAccountByIdentifier(identifier, preferredCountry);

    if (!account) {
      const savedMatch = resolveMatchingSavedProfile(
        identifier,
        preferredCountry,
        body.savedProfile,
        body.savedProfiles
      );
      if (savedMatch) {
        const cleanedAttempt = password.replace(/[\r\n]+/g, '').trim();
        if (savedMatch.passwordHash) {
          const savedPasswordMatched =
            verifyPassword(password, savedMatch.passwordHash) ||
            (cleanedAttempt !== password && verifyPassword(cleanedAttempt, savedMatch.passwordHash));
          if (!savedPasswordMatched) {
            res.status(401).json({
              message: 'Incorrect password for this phone number. Check your password or use Forgot Password.',
              wrongPassword: true,
            });
            return;
          }
          account = createAccount({
            username: savedMatch.username,
            phone: savedMatch.phoneE164,
            email: savedMatch.email,
            emailVerified: true,
            country: savedMatch.country,
            passwordHash: savedMatch.passwordHash,
            encryptedPassword:
              savedMatch.passwordRecovery ||
              encryptRecoverablePassword(cleanedAttempt || password, savedMatch.phoneE164),
            isGuest: false,
            createdAt: savedMatch.createdAt,
          });
        } else {
          const cleanPass = cleanedAttempt;
          if (cleanPass.length < 6) {
            res.status(401).json({
              message: 'Incorrect password for this phone number. Check your password or use Forgot Password.',
              wrongPassword: true,
            });
            return;
          }
          account = createAccount({
            username: savedMatch.username,
            phone: savedMatch.phoneE164,
            email: savedMatch.email,
            emailVerified: true,
            country: savedMatch.country,
            passwordHash: hashPassword(cleanPass),
            encryptedPassword: encryptRecoverablePassword(cleanPass, savedMatch.phoneE164),
            isGuest: false,
            createdAt: savedMatch.createdAt,
          });
        }
      }
    }

    if (!account) {
      res.status(401).json({
        message: 'No account found for this phone number or email. Please Register first.',
        accountNotFound: true,
      });
      return;
    }

    const cleanedPassword = password.replace(/[\r\n]+/g, '').trim();
    const decryptedStored = decryptRecoverablePassword(
      account.encryptedPassword,
      account.phone || account.username
    );
    const passwordMatched =
      verifyPassword(password, account.passwordHash) ||
      (cleanedPassword !== password && verifyPassword(cleanedPassword, account.passwordHash)) ||
      (Boolean(decryptedStored) &&
        (password === decryptedStored || cleanedPassword === decryptedStored));

    if (!passwordMatched) {
      res.status(401).json({
        message: 'Incorrect password for this phone number. Check your password or use Forgot Password.',
        wrongPassword: true,
      });
      return;
    }

    if (!account.encryptedPassword && cleanedPassword.length >= 6) {
      account.encryptedPassword = encryptRecoverablePassword(
        cleanedPassword,
        account.phone || account.username
      );
      account.updatedAt = Date.now();
      saveStoreNow();
    }

    if (account.emailVerified === false) {
      account.emailVerified = true;
      account.otpCodeHash = null;
      account.otpExpiresAt = null;
      account.otpAttempts = 0;
      account.updatedAt = Date.now();
      scheduleSaveStore();
    }

    if (account.realBalance > 0) {
      account.activeAccountType = 'real';
      account.updatedAt = Date.now();
      scheduleSaveStore();
    }

    const sessionId = resolveSessionIdFromRequest(req, res);
    sessionToAccountId.set(sessionId, account.id);
    const token = createAuthToken(account.id);
    appendSetCookie(
      res,
      `luckymate_auth=${encodeURIComponent(token)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800`
    );

    res.json({
      sessionId,
      token,
      username: account.username,
      passwordHash: account.passwordHash ?? undefined,
      passwordRecovery: account.encryptedPassword ?? undefined,
      ...buildWalletFields(account),
      admin: account.isAdmin,
      guest: false,
    });
  });

  app.post('/api/recover-password', (req: Request, res: Response) => {
    const body = req.body ?? {};
    const identifier = String(body.phone ?? body.username ?? '').trim();
    const preferredCountry = body.country ? parseSupportedCountry(body.country) : undefined;

    if (!identifier) {
      res.status(400).json({ message: 'Enter your registered phone number.' });
      return;
    }

    let account = findAccountByIdentifier(identifier, preferredCountry);
    if (!account || account.isGuest) {
      const savedMatch = resolveMatchingSavedProfile(
        identifier,
        preferredCountry,
        body.savedProfile,
        body.savedProfiles
      );
      if (savedMatch) {
        account = createAccount({
          username: savedMatch.username,
          phone: savedMatch.phoneE164,
          email: savedMatch.email,
          emailVerified: true,
          country: savedMatch.country,
          passwordHash: savedMatch.passwordHash,
          encryptedPassword: savedMatch.passwordRecovery,
          isGuest: false,
          createdAt: savedMatch.createdAt,
        });
      }
    }

    if (!account || account.isGuest) {
      res.status(404).json({
        message: 'No registered account found for this phone number. Please Register first.',
        accountNotFound: true,
      });
      return;
    }

    const identityKey = account.phone || account.username;
    let recoveredPassword = decryptRecoverablePassword(account.encryptedPassword, identityKey);

    if (!recoveredPassword) {
      const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZabcdefghjkmnpqrstuvwxyz23456789';
      const bytes = crypto.randomBytes(6);
      let suffix = '';
      for (let i = 0; i < 6; i++) {
        suffix += chars[bytes[i] % chars.length];
      }
      recoveredPassword = `LM${suffix}`;
      account.passwordHash = hashPassword(recoveredPassword);
      account.encryptedPassword = encryptRecoverablePassword(recoveredPassword, identityKey);
      account.updatedAt = Date.now();
      saveStoreNow();
    } else if (!verifyPassword(recoveredPassword, account.passwordHash)) {
      account.passwordHash = hashPassword(recoveredPassword);
      account.updatedAt = Date.now();
      saveStoreNow();
    }

    res.json({
      success: true,
      phone: account.phone,
      country: account.country,
      previousPassword: recoveredPassword,
      passwordHash: account.passwordHash ?? undefined,
      passwordRecovery: account.encryptedPassword ?? undefined,
      message: 'Your previous password is ready. Copy it and log in below.',
    });
  });

  app.post('/api/reset-password', async (req: Request, res: Response) => {
    const body = req.body ?? {};
    const identifier = String(body.phone ?? body.username ?? '').trim();
    const newPassword = String(body.newPassword ?? '').trim();
    const confirmPassword = String(body.confirmPassword ?? '').trim();
    const preferredCountry = body.country ? parseSupportedCountry(body.country) : undefined;

    if (!identifier) {
      res.status(400).json({ message: 'Enter your registered phone number.' });
      return;
    }

    let account = findAccountByIdentifier(identifier, preferredCountry);
    if (!account || account.isGuest) {
      const savedMatch = resolveMatchingSavedProfile(
        identifier,
        preferredCountry,
        body.savedProfile,
        body.savedProfiles
      );
      if (savedMatch) {
        if (newPassword.length < 6 || newPassword.length > 100) {
          res.status(400).json({ message: 'New password must be at least 6 characters.' });
          return;
        }
        if (newPassword !== confirmPassword) {
          res.status(400).json({ message: 'New passwords do not match.' });
          return;
        }
        account = createAccount({
          username: savedMatch.username,
          phone: savedMatch.phoneE164,
          country: savedMatch.country,
          passwordHash: hashPassword(newPassword),
          isGuest: false,
          createdAt: savedMatch.createdAt,
        });
        if (account.phone) {
          await dispatchRealSms({
            toE164: account.phone,
            country: account.country,
            messageBody: `Your Luckymate account (${account.phone}) password has been updated.`,
          }).catch(() => {});
        }
        res.json({
          success: true,
          phone: account.phone,
          country: account.country,
          passwordHash: account.passwordHash ?? undefined,
          message: 'Password updated! Enter your phone number and new password to log in.',
        });
        return;
      }

      res.status(404).json({
        message: 'No registered account found for this phone number. Please Register first.',
        accountNotFound: true,
      });
      return;
    }

    if (account.realBalance > 0) {
      res.status(403).json({
        message: 'Accounts with real funds require support verification to reset the password.',
      });
      return;
    }

    if (newPassword.length < 6 || newPassword.length > 100) {
      res.status(400).json({ message: 'New password must be at least 6 characters.' });
      return;
    }

    if (newPassword !== confirmPassword) {
      res.status(400).json({ message: 'New passwords do not match.' });
      return;
    }

    account.passwordHash = hashPassword(newPassword);
    account.encryptedPassword = encryptRecoverablePassword(
      newPassword,
      account.phone || account.username
    );
    account.updatedAt = Date.now();
    saveStoreNow();

    if (account.phone) {
      await dispatchRealSms({
        toE164: account.phone,
        country: account.country,
        messageBody: `Your Luckymate account (${account.phone}) password has been updated.`,
      }).catch(() => {});
    }

    res.json({
      success: true,
      phone: account.phone,
      country: account.country,
      passwordHash: account.passwordHash ?? undefined,
      passwordRecovery: account.encryptedPassword ?? undefined,
      message: 'Password updated! Enter your phone number and new password to log in.',
    });
  });

  app.post('/api/guest', (req: Request, res: Response) => {
    const sessionId = resolveSessionIdFromRequest(req, res);
    const username = `Guest-${crypto.randomBytes(3).toString('hex').toUpperCase()}`;
    const account = createAccount({
      username,
      passwordHash: null,
      isGuest: true,
    });
    sessionToAccountId.set(sessionId, account.id);
    appendSetCookie(res, 'luckymate_auth=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0');
    const token = createAuthToken(account.id);

    res.json({
      sessionId,
      token,
      username: account.username,
      ...buildWalletFields(account),
      guest: true,
    });
  });

  app.post('/api/logout', (req: Request, res: Response) => {
    const oldSessionId = resolveSessionIdFromRequest(req, res);
    sessionToAccountId.delete(oldSessionId);
    const freshSessionId = crypto.randomBytes(16).toString('hex');
    appendSetCookie(res, 'luckymate_auth=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0');
    appendSetCookie(
      res,
      `luckymate_sid=${encodeURIComponent(freshSessionId)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800`
    );
    res.json({ success: true, sessionId: freshSessionId });
  });

  app.get('/api/me', (req: Request, res: Response) => {
    const authHeader = typeof req.headers.authorization === 'string' ? req.headers.authorization : '';
    const token = authHeader.startsWith('Bearer ') ? authHeader.slice(7).trim() : '';
    const account = token ? verifyAuthToken(token) : null;
    if (!account) {
      res.status(401).json({ message: 'Please log in again.' });
      return;
    }
    res.json({
      id: account.id,
      username: account.username,
      ...buildWalletFields(account),
      admin: account.isAdmin,
      guest: account.isGuest,
    });
  });

  // ---------------- WALLET & SPORTSBOOK API ----------------

  app.get('/api/wallet', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    res.json({
      sessionId,
      username: account.username,
      isGuest: account.isGuest,
      passwordHash: !account.isGuest ? (account.passwordHash ?? undefined) : undefined,
      ...buildWalletFields(account),
    });
  });

  app.post('/api/account/country', (req: Request, res: Response) => {
    const { account } = resolveRequestAccount(req, res);
    const country = parseSupportedCountry(req.body?.country);
    account.country = country;
    account.updatedAt = Date.now();
    if (!account.isGuest) scheduleSaveStore();
    res.json({
      success: true,
      country,
      currency: COUNTRY_META[country].currency,
    });
  });

  app.post('/api/account/mode', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const requested = req.body?.mode === 'real' ? 'real' : 'demo';

    if (requested === 'real' && account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Please register an account before switching to a Real Account.',
      });
      return;
    }

    account.activeAccountType = requested;
    account.updatedAt = Date.now();
    if (!account.isGuest) scheduleSaveStore();
    res.json({
      success: true,
      sessionId,
      username: account.username,
      isGuest: account.isGuest,
      ...buildWalletFields(account),
    });
  });

  app.post('/api/demo-deposit', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const body = req.body ?? {};
    const country = body.country ? parseSupportedCountry(body.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const hasUsd = body.amountUsd !== undefined && body.amountUsd !== null && body.amountUsd !== '';
    const parsedUsd = hasUsd
      ? Number(body.amountUsd)
      : Number(body.amount) / countryMeta.usdRate;
    const phone = String(body.phone || account.phone || '').trim();
    const walletMode: 'demo' | 'real' =
      body.walletMode === 'demo' || body.walletMode === 'real'
        ? body.walletMode
        : account.isGuest
        ? 'demo'
        : 'real';

    if (walletMode === 'real' && account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Register an account first to deposit into your Real balance.',
      });
      return;
    }

    if (walletMode === 'real' && process.env.PAYSTACK_SECRET_KEY) {
      res.status(403).json({
        success: false,
        message: 'Real wallet deposits require live payment verification.',
      });
      return;
    }

    const minLocal = MIN_DEPOSIT_USD * countryMeta.usdRate;
    if (!Number.isFinite(parsedUsd) || parsedUsd < MIN_DEPOSIT_USD || parsedUsd > 50000) {
      res.status(400).json({
        success: false,
        message: `Minimum deposit is $${MIN_DEPOSIT_USD.toFixed(2)} USD (${countryMeta.currency} ${minLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      });
      return;
    }

    const digitsOnly = phone.replace(/\D/g, '');
    if (walletMode === 'real' && phone.length > 0 && (digitsOnly.length < 8 || digitsOnly.length > 14)) {
      res.status(400).json({
        success: false,
        message: `Enter a valid phone number (${countryMeta.sampleLocal}).`,
      });
      return;
    }

    const depositUsd = Number(parsedUsd.toFixed(2));
    const depositBase = Number((depositUsd * BASE_KES_PER_USD).toFixed(2));
    const depositLocal = Number((depositUsd * countryMeta.usdRate).toFixed(2));

    adjustAccountBalance(account, walletMode, depositBase);
    if (walletMode === 'real') {
      account.activeAccountType = 'real';
    }
    account.country = country;
    account.lastDepositAmount = depositBase;
    account.lastDepositDate = formatShortDate(new Date());
    account.updatedAt = Date.now();
    account.history.unshift({
      id: crypto.randomUUID(),
      type: 'deposit',
      amount: depositBase,
      status: 'Completed',
      label:
        walletMode === 'real'
          ? `Real Account Deposit ($${depositUsd.toFixed(2)} USD)`
          : `Demo Top-up ($${depositUsd.toFixed(2)} USD)`,
      detail: `$${depositUsd.toFixed(2)} USD (${countryMeta.currency} ${depositLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) · ${
        walletMode === 'real' ? 'Real Wallet' : 'Demo Wallet'
      }`,
      createdAt: new Date().toISOString(),
    });
    account.history = account.history.slice(0, 40);
    let unlockedReferralBonusUsd = 0;
    if (walletMode === 'real') {
      const refResult = processReferralRewardOnQualifyingDeposit(account, depositUsd);
      unlockedReferralBonusUsd = refResult.unlockedOwnBonusUsd || 0;
    }
    if (!account.isGuest) saveStoreNow();

    res.json({
      success: true,
      sessionId,
      depositUsd,
      depositLocal,
      unlockedReferralBonusUsd,
      message:
        unlockedReferralBonusUsd > 0
          ? `Deposited $${depositUsd.toFixed(2)} USD and unlocked +$${unlockedReferralBonusUsd.toFixed(2)} USD in referral bonus into your Real account!`
          : `Deposited $${depositUsd.toFixed(2)} USD (${countryMeta.currency} ${depositLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) into your ${
              walletMode === 'real' ? 'Real' : 'Demo'
            } account.`,
      ...buildWalletFields(account),
    });
  });

  app.post('/api/demo-withdraw', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const body = req.body ?? {};
    const country = body.country ? parseSupportedCountry(body.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const hasUsd = body.amountUsd !== undefined && body.amountUsd !== null && body.amountUsd !== '';
    const parsedUsd = hasUsd
      ? Number(body.amountUsd)
      : Number(body.amount) / countryMeta.usdRate;
    const phone = String(body.phone || account.phone || '').trim();
    const walletMode: 'demo' | 'real' =
      body.walletMode === 'demo' || body.walletMode === 'real'
        ? body.walletMode
        : account.activeAccountType;

    if (walletMode === 'real' && account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Register an account first to withdraw from your Real balance.',
      });
      return;
    }

    if (walletMode === 'real' && process.env.PAYSTACK_SECRET_KEY) {
      res.status(403).json({
        success: false,
        message: 'Real wallet withdrawals require withdrawal fee payment verification.',
      });
      return;
    }

    const minWithdrawLocal = MIN_WITHDRAW_USD * countryMeta.usdRate;
    if (!Number.isFinite(parsedUsd) || parsedUsd < MIN_WITHDRAW_USD || parsedUsd > 50000) {
      res.status(400).json({
        success: false,
        message: `Minimum withdrawal is $${MIN_WITHDRAW_USD.toFixed(2)} USD (${countryMeta.currency} ${minWithdrawLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      });
      return;
    }

    const digitsOnly = phone.replace(/\D/g, '');
    if (walletMode === 'real' && phone.length > 0 && (digitsOnly.length < 8 || digitsOnly.length > 14)) {
      res.status(400).json({
        success: false,
        message: `Enter a valid phone number (${countryMeta.sampleLocal}).`,
      });
      return;
    }

    const withdrawUsd = Number(parsedUsd.toFixed(2));
    const grossBase = Number((withdrawUsd * BASE_KES_PER_USD).toFixed(2));
    const grossLocal = Number((withdrawUsd * countryMeta.usdRate).toFixed(2));
    const feeUsd = calculateWithdrawFeeUsd(withdrawUsd);
    const feeLocal = Number((feeUsd * countryMeta.usdRate).toFixed(2));
    const netUsd = Number((withdrawUsd - feeUsd).toFixed(2));
    const netLocal = Number((netUsd * countryMeta.usdRate).toFixed(2));

    const currentBalanceBase = getAccountBalance(account, walletMode);
    if (grossBase > currentBalanceBase) {
      const currentLocal = Number(((currentBalanceBase / BASE_KES_PER_USD) * countryMeta.usdRate).toFixed(2));
      res.status(400).json({
        success: false,
        message: `Insufficient ${walletMode === 'real' ? 'Real' : 'Demo'} wallet balance. Need ${countryMeta.currency} ${grossLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })} ($${withdrawUsd.toFixed(2)} USD), available ${countryMeta.currency} ${currentLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}.`,
      });
      return;
    }

    adjustAccountBalance(account, walletMode, -grossBase);
    account.country = country;
    account.updatedAt = Date.now();
    account.history.unshift({
      id: crypto.randomUUID(),
      type: 'withdraw',
      amount: -grossBase,
      status: 'Completed',
      label:
        walletMode === 'real'
          ? `Real Account Withdrawal ($${withdrawUsd.toFixed(2)} USD)`
          : `Demo Withdrawal ($${withdrawUsd.toFixed(2)} USD)`,
      detail: `Requested $${withdrawUsd.toFixed(2)} USD · Fee -$${feeUsd.toFixed(2)} USD (-${countryMeta.currency} ${feeLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) · Net Payout $${netUsd.toFixed(2)} USD (${countryMeta.currency} ${netLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })})`,
      createdAt: new Date().toISOString(),
    });
    account.history = account.history.slice(0, 40);
    if (!account.isGuest) saveStoreNow();

    res.json({
      success: true,
      sessionId,
      withdrawUsd,
      feeUsd,
      feeLocal,
      netUsd,
      netLocal,
      message: `Withdrawal of $${withdrawUsd.toFixed(2)} USD completed ($${feeUsd.toFixed(2)} USD fee charged). Net payout: $${netUsd.toFixed(2)} USD (${countryMeta.currency} ${netLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      ...buildWalletFields(account),
    });
  });

  // ---------------- PAYSTACK REAL PAYMENTS (STK PUSH & CHECKOUT) ----------------

  type PaystackProviderCode =
    | 'mpesa'
    | 'mtn'
    | 'vod'
    | 'atl'
    | 'orange'
    | 'moov'
    | 'wave'
    | 'checkout';

  interface PaystackMetadataPayload {
    txKind?: 'deposit' | 'withdraw_fee';
    accountId?: string;
    username?: string;
    registeredPhone?: string;
    country?: SupportedCountry;
    depositUsd?: number;
    withdrawUsd?: number;
    feeUsd?: number;
    provider?: PaystackProviderCode;
  }

  interface PendingPaystackDeposit {
    reference: string;
    accountId: string;
    depositUsd: number;
    depositBase: number;
    depositLocal: number;
    expectedMinor: number;
    currency: 'KES' | 'GHS' | 'XOF';
    country: SupportedCountry;
    phoneE164: string;
    provider: PaystackProviderCode;
    status: 'pending' | 'send_otp' | 'open_url' | 'success' | 'failed';
    credited: boolean;
    createdAt: string;
  }

  interface PendingPaystackWithdrawFee {
    reference: string;
    accountId: string;
    withdrawUsd: number;
    withdrawBase: number;
    withdrawLocal: number;
    feeUsd: number;
    feeBase: number;
    feeLocal: number;
    expectedMinor: number;
    currency: 'KES' | 'GHS' | 'XOF';
    country: SupportedCountry;
    phoneE164: string;
    provider: PaystackProviderCode;
    status: 'pending' | 'send_otp' | 'open_url' | 'success' | 'failed';
    settled: boolean;
    createdAt: string;
  }

  const pendingPaystackDeposits = new Map<string, PendingPaystackDeposit>();
  const pendingPaystackWithdrawals = new Map<string, PendingPaystackWithdrawFee>();

  const PAYSTACK_ALLOWED_PROVIDERS: Record<SupportedCountry, Exclude<PaystackProviderCode, 'checkout'>[]> = {
    Kenya: ['mpesa'],
    Ghana: ['mtn', 'vod', 'atl'],
    "Côte d'Ivoire": ['orange', 'mtn', 'moov', 'wave'],
  };

  function resolvePaystackProvider(
    country: SupportedCountry,
    raw: unknown
  ): Exclude<PaystackProviderCode, 'checkout'> {
    const allowed = PAYSTACK_ALLOWED_PROVIDERS[country];
    if (
      typeof raw === 'string' &&
      allowed.includes(raw as Exclude<PaystackProviderCode, 'checkout'>)
    ) {
      return raw as Exclude<PaystackProviderCode, 'checkout'>;
    }
    return allowed[0];
  }

  function toPaystackMinorAmount(localAmount: number, currency: 'KES' | 'GHS' | 'XOF'): number {
    // Paystack expects XOF in integer CFA units * 100 (multiples of 100)
    if (currency === 'XOF') {
      return Math.round(localAmount) * 100;
    }
    return Math.round(localAmount * 100);
  }

  function buildPaystackCallbackUrl(req: Request): string | undefined {
    const explicit = process.env.APP_URL?.trim();
    if (explicit) {
      return explicit.replace(/\/+$/, '');
    }
    const originHeader = req.headers.origin;
    if (typeof originHeader === 'string' && /^https?:\/\//i.test(originHeader)) {
      return originHeader.replace(/\/+$/, '');
    }
    const host = req.get('host');
    if (!host) return undefined;
    const proto = req.headers['x-forwarded-proto']
      ? String(req.headers['x-forwarded-proto']).split(',')[0].trim()
      : req.protocol || 'https';
    return `${proto}://${host}`;
  }

  function resolveDepositRecord(
    reference: string,
    metadata?: PaystackMetadataPayload,
    paidMinor?: number
  ): PendingPaystackDeposit | undefined {
    const existing = pendingPaystackDeposits.get(reference);
    if (existing) return existing;

    if (!metadata?.accountId) return undefined;
    const account = accountsById.get(String(metadata.accountId));
    if (!account) return undefined;

    const country = metadata.country ? parseSupportedCountry(metadata.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const metaUsd = Number(metadata.depositUsd ?? 0);
    const derivedLocal =
      Number.isFinite(paidMinor) && (paidMinor ?? 0) > 0
        ? Number(((paidMinor as number) / 100).toFixed(2))
        : Number((metaUsd * countryMeta.usdRate).toFixed(2));
    const depositUsd =
      Number.isFinite(metaUsd) && metaUsd >= MIN_DEPOSIT_USD
        ? Number(metaUsd.toFixed(2))
        : Number((derivedLocal / countryMeta.usdRate).toFixed(2));
    if (!Number.isFinite(depositUsd) || depositUsd < MIN_DEPOSIT_USD) return undefined;

    const depositBase = Number((depositUsd * BASE_KES_PER_USD).toFixed(2));
    const depositLocal = Number((depositUsd * countryMeta.usdRate).toFixed(2));
    const reconstructed: PendingPaystackDeposit = {
      reference,
      accountId: account.id,
      depositUsd,
      depositBase,
      depositLocal,
      expectedMinor: toPaystackMinorAmount(depositLocal, countryMeta.currency),
      currency: countryMeta.currency,
      country,
      phoneE164: String(metadata.registeredPhone || account.phone || ''),
      provider: metadata.provider === 'checkout' ? 'checkout' : resolvePaystackProvider(country, metadata.provider),
      status: 'pending',
      credited: creditedPaystackReferences.has(reference),
      createdAt: new Date().toISOString(),
    };
    pendingPaystackDeposits.set(reference, reconstructed);
    return reconstructed;
  }

  function creditPaystackDepositIfVerified(
    reference: string,
    verificationData?: {
      status?: string;
      amount?: number;
      currency?: string;
      channel?: string;
      metadata?: PaystackMetadataPayload;
    }
  ): {
    creditedNow: boolean;
    record?: PendingPaystackDeposit;
    account?: AccountRecord;
    unlockedReferralBonusUsd?: number;
  } {
    const record = resolveDepositRecord(
      reference,
      verificationData?.metadata,
      verificationData?.amount
    );
    if (!record) return { creditedNow: false };

    const account = accountsById.get(record.accountId);
    if (!account) return { creditedNow: false, record };

    if (record.credited || creditedPaystackReferences.has(reference)) {
      record.credited = true;
      return { creditedNow: false, record, account };
    }

    if (verificationData?.status !== 'success') {
      return { creditedNow: false, record, account };
    }

    const paidMinor = Number(verificationData.amount ?? 0);
    if (Number.isFinite(paidMinor) && paidMinor > 0 && paidMinor + 100 < record.expectedMinor) {
      return { creditedNow: false, record, account };
    }

    creditedPaystackReferences.add(reference);
    record.credited = true;
    record.status = 'success';

    adjustAccountBalance(account, 'real', record.depositBase);
    account.activeAccountType = 'real';
    account.country = record.country;
    account.lastDepositAmount = record.depositBase;
    account.lastDepositDate = formatShortDate(new Date());
    account.updatedAt = Date.now();

    account.history.unshift({
      id: crypto.randomUUID(),
      type: 'deposit',
      amount: record.depositBase,
      status: 'Completed',
      label: `Real Account Deposit ($${record.depositUsd.toFixed(2)} USD)`,
      detail: `${record.phoneE164 ? `${maskPhone(record.phoneE164)} · ` : ''}${record.currency} ${record.depositLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })} · Real Wallet`,
      createdAt: new Date().toISOString(),
    });
    account.history = account.history.slice(0, 40);
    const refOutcome = processReferralRewardOnQualifyingDeposit(account, record.depositUsd);
    saveStoreNow();

    return {
      creditedNow: true,
      record,
      account,
      unlockedReferralBonusUsd: refOutcome.unlockedOwnBonusUsd || 0,
    };
  }

  function resolveWithdrawRecord(
    reference: string,
    metadata?: PaystackMetadataPayload
  ): PendingPaystackWithdrawFee | undefined {
    const existing = pendingPaystackWithdrawals.get(reference);
    if (existing) return existing;

    if (!metadata?.accountId || metadata.txKind !== 'withdraw_fee') return undefined;
    const account = accountsById.get(String(metadata.accountId));
    if (!account) return undefined;

    const country = metadata.country ? parseSupportedCountry(metadata.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const metaWithdrawUsd = Number(metadata.withdrawUsd ?? MIN_WITHDRAW_USD);
    const withdrawUsd =
      Number.isFinite(metaWithdrawUsd) && metaWithdrawUsd >= MIN_WITHDRAW_USD
        ? Number(metaWithdrawUsd.toFixed(2))
        : MIN_WITHDRAW_USD;
    const withdrawBase = Number((withdrawUsd * BASE_KES_PER_USD).toFixed(2));
    const withdrawLocal = Number((withdrawUsd * countryMeta.usdRate).toFixed(2));
    const metaFeeUsd = Number(metadata.feeUsd);
    const feeUsd =
      Number.isFinite(metaFeeUsd) && metaFeeUsd > 0
        ? Number(metaFeeUsd.toFixed(2))
        : calculateWithdrawFeeUsd(withdrawUsd);
    const feeBase = Number((feeUsd * BASE_KES_PER_USD).toFixed(2));
    const feeLocal = Number((feeUsd * countryMeta.usdRate).toFixed(2));

    const reconstructed: PendingPaystackWithdrawFee = {
      reference,
      accountId: account.id,
      withdrawUsd,
      withdrawBase,
      withdrawLocal,
      feeUsd,
      feeBase,
      feeLocal,
      expectedMinor: toPaystackMinorAmount(feeLocal, countryMeta.currency),
      currency: countryMeta.currency,
      country,
      phoneE164: String(metadata.registeredPhone || account.phone || ''),
      provider:
        metadata.provider === 'checkout'
          ? 'checkout'
          : resolvePaystackProvider(country, metadata.provider),
      status: 'pending',
      settled: settledWithdrawReferences.has(reference),
      createdAt: new Date().toISOString(),
    };
    pendingPaystackWithdrawals.set(reference, reconstructed);
    return reconstructed;
  }

  function settlePaystackWithdrawalIfVerified(
    reference: string,
    verificationData?: {
      status?: string;
      amount?: number;
      currency?: string;
      channel?: string;
      metadata?: PaystackMetadataPayload;
    }
  ): { settledNow: boolean; record?: PendingPaystackWithdrawFee; account?: AccountRecord } {
    const record = resolveWithdrawRecord(reference, verificationData?.metadata);
    if (!record) return { settledNow: false };

    const account = accountsById.get(record.accountId);
    if (!account) return { settledNow: false, record };

    if (record.settled || settledWithdrawReferences.has(reference)) {
      record.settled = true;
      return { settledNow: false, record, account };
    }

    if (verificationData?.status !== 'success') {
      return { settledNow: false, record, account };
    }

    const paidMinor = Number(verificationData.amount ?? 0);
    if (Number.isFinite(paidMinor) && paidMinor > 0 && paidMinor + 100 < record.expectedMinor) {
      return { settledNow: false, record, account };
    }

    settledWithdrawReferences.add(reference);
    record.settled = true;
    record.status = 'success';

    const previousRealBase = Number(account.realBalance.toFixed(2));
    // Clear real balance to 0.00 until the user deposits again
    account.realBalance = 0;
    account.activeAccountType = 'real';
    account.country = record.country;
    account.updatedAt = Date.now();

    account.history.unshift({
      id: crypto.randomUUID(),
      type: 'withdraw',
      amount: -Math.max(previousRealBase, record.withdrawBase),
      status: 'Completed',
      label: `Real Account Withdrawal ($${record.withdrawUsd.toFixed(2)} USD)`,
      detail: `Withdrew $${record.withdrawUsd.toFixed(2)} USD (${record.currency} ${record.withdrawLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) · Fee Paid: $${record.feeUsd.toFixed(2)} USD (${record.currency} ${record.feeLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) · Balance: ${record.currency} 0.00`,
      createdAt: new Date().toISOString(),
    });
    account.history = account.history.slice(0, 40);
    saveStoreNow();

    return { settledNow: true, record, account };
  }

  app.get('/api/payments/paystack/status', (_req: Request, res: Response) => {
    const secret = process.env.PAYSTACK_SECRET_KEY || '';
    const mode: 'live' | 'test' | 'unconfigured' = !secret
      ? 'unconfigured'
      : secret.startsWith('sk_live_')
      ? 'live'
      : 'test';
    res.json({
      configured: Boolean(secret),
      publicKey: process.env.PAYSTACK_PUBLIC_KEY || '',
      mode,
    });
  });

  app.post('/api/payments/paystack/checkout', async (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    if (account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Register an account first to deposit real money with Paystack into your Real Wallet.',
      });
      return;
    }

    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({
        success: false,
        paystackConfigured: false,
        message:
          'Paystack live collection is not configured yet. Add PAYSTACK_SECRET_KEY in AI Studio Secrets to collect real money via Paystack.',
      });
      return;
    }

    const body = req.body ?? {};
    const country = body.country ? parseSupportedCountry(body.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const hasUsd = body.amountUsd !== undefined && body.amountUsd !== null && body.amountUsd !== '';
    const parsedUsd = hasUsd
      ? Number(body.amountUsd)
      : Number(body.amount) / countryMeta.usdRate;

    const minLocal = MIN_DEPOSIT_USD * countryMeta.usdRate;
    if (!Number.isFinite(parsedUsd) || parsedUsd < MIN_DEPOSIT_USD || parsedUsd > 50000) {
      res.status(400).json({
        success: false,
        message: `Minimum deposit is $${MIN_DEPOSIT_USD.toFixed(2)} USD (${countryMeta.currency} ${minLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      });
      return;
    }

    const rawTargetPhone = String(account.phone || body.phone || '').trim();
    const normalized = normalizePhoneNumber(rawTargetPhone, country);
    const phoneResult = normalized.ok
      ? normalized
      : account.phone
      ? normalizePhoneNumber(account.phone, account.country)
      : normalized;

    const phoneE164 = phoneResult.ok ? phoneResult.e164 : rawTargetPhone;
    const depositUsd = Number(parsedUsd.toFixed(2));
    const depositBase = Number((depositUsd * BASE_KES_PER_USD).toFixed(2));
    const depositLocal = Number((depositUsd * countryMeta.usdRate).toFixed(2));
    const amountMinor = toPaystackMinorAmount(depositLocal, countryMeta.currency);
    const reference = `LM-PS-${Date.now()}-${crypto.randomBytes(3).toString('hex').toUpperCase()}`;
    const customerEmail =
      account.email || `member.${account.id.replace(/[^a-zA-Z0-9]/g, '').slice(0, 12)}@luckymate.app`;
    const callbackUrl = buildPaystackCallbackUrl(req);
    const formattedLocal = depositLocal.toLocaleString('en-US', {
      minimumFractionDigits: 2,
      maximumFractionDigits: 2,
    });
    const stkPrompt = `DO YOU WANT TO DEPOSIT $${depositUsd.toFixed(2)} USD (${countryMeta.currency} ${formattedLocal}) TO LUCKYMATE?`;

    try {
      const initPayload: Record<string, unknown> = {
        email: customerEmail,
        amount: amountMinor,
        currency: countryMeta.currency,
        reference,
        channels: ['mobile_money', 'card', 'bank', 'ussd'],
        metadata: {
          accountId: account.id,
          username: account.username,
          registeredPhone: phoneE164,
          country,
          depositUsd,
          provider: 'checkout',
          stkPrompt,
          custom_fields: [
            {
              display_name: 'Luckymate Deposit Prompt',
              variable_name: 'stk_prompt',
              value: stkPrompt,
            },
          ],
        },
      };
      if (callbackUrl) {
        initPayload.callback_url = callbackUrl;
      }

      const initResp = await fetch('https://api.paystack.co/transaction/initialize', {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${paystackSecret}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(initPayload),
      });

      const initJson = (await initResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: {
          authorization_url?: string;
          access_code?: string;
          reference?: string;
        };
      };

      if (!initResp.ok || !initJson.status || !initJson.data?.authorization_url) {
        res.status(400).json({
          success: false,
          message:
            initJson.message ||
            `Paystack could not initialize checkout (${initResp.status}). Verify PAYSTACK_SECRET_KEY and ${countryMeta.currency} currency activation in your Paystack dashboard.`,
        });
        return;
      }

      const psRef = String(initJson.data.reference || reference);
      const depositRecord: PendingPaystackDeposit = {
        reference: psRef,
        accountId: account.id,
        depositUsd,
        depositBase,
        depositLocal,
        expectedMinor: amountMinor,
        currency: countryMeta.currency,
        country,
        phoneE164,
        provider: 'checkout',
        status: 'open_url',
        credited: false,
        createdAt: new Date().toISOString(),
      };
      pendingPaystackDeposits.set(psRef, depositRecord);

      res.json({
        success: true,
        sessionId,
        reference: psRef,
        status: 'open_url',
        stkPrompt,
        displayText: stkPrompt,
        authorizationUrl: initJson.data.authorization_url,
        accessCode: initJson.data.access_code,
        phone: phoneE164,
        maskedPhone: phoneE164 ? maskPhone(phoneE164) : '',
        provider: 'checkout',
        depositUsd,
        depositLocal,
        currency: countryMeta.currency,
        message: stkPrompt,
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        message: `Paystack connection error: ${err instanceof Error ? err.message : 'Network failure'}`,
      });
    }
  });

  app.post('/api/payments/paystack/deposit', async (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    if (account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Register an account first to receive Paystack STK Push into your Real Wallet.',
      });
      return;
    }

    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({
        success: false,
        paystackConfigured: false,
        message:
          'Paystack live collection is not configured yet. Add PAYSTACK_SECRET_KEY in AI Studio Secrets to trigger real STK Push prompts.',
      });
      return;
    }

    const body = req.body ?? {};
    const country = body.country ? parseSupportedCountry(body.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const hasUsd = body.amountUsd !== undefined && body.amountUsd !== null && body.amountUsd !== '';
    const parsedUsd = hasUsd
      ? Number(body.amountUsd)
      : Number(body.amount) / countryMeta.usdRate;

    const minLocal = MIN_DEPOSIT_USD * countryMeta.usdRate;
    if (!Number.isFinite(parsedUsd) || parsedUsd < MIN_DEPOSIT_USD || parsedUsd > 50000) {
      res.status(400).json({
        success: false,
        message: `Minimum deposit is $${MIN_DEPOSIT_USD.toFixed(2)} USD (${countryMeta.currency} ${minLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      });
      return;
    }

    // Prioritize the registered phone number used when creating the account
    const rawTargetPhone = String(account.phone || body.phone || '').trim();
    const normalized = normalizePhoneNumber(rawTargetPhone, country);
    const phoneResult = normalized.ok
      ? normalized
      : account.phone
      ? normalizePhoneNumber(account.phone, account.country)
      : normalized;

    if (!phoneResult.ok) {
      res.status(400).json({
        success: false,
        message: phoneResult.message,
      });
      return;
    }

    const provider = resolvePaystackProvider(country, body.provider);
    const depositUsd = Number(parsedUsd.toFixed(2));
    const depositBase = Number((depositUsd * BASE_KES_PER_USD).toFixed(2));
    const depositLocal = Number((depositUsd * countryMeta.usdRate).toFixed(2));
    const amountMinor = toPaystackMinorAmount(depositLocal, countryMeta.currency);
    const reference = `LM-PS-${Date.now()}-${crypto.randomBytes(3).toString('hex').toUpperCase()}`;

    const paystackMobilePhone = country === 'Kenya' ? phoneResult.e164 : phoneResult.localDigits;
    const customerEmail =
      account.email || `member.${account.id.replace(/[^a-zA-Z0-9]/g, '').slice(0, 12)}@luckymate.app`;

    const formattedLocal = depositLocal.toLocaleString('en-US', {
      minimumFractionDigits: 2,
      maximumFractionDigits: 2,
    });
    const stkPrompt = `DO YOU WANT TO DEPOSIT $${depositUsd.toFixed(2)} USD (${countryMeta.currency} ${formattedLocal}) TO LUCKYMATE?`;

    try {
      const chargeResp = await fetch('https://api.paystack.co/charge', {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${paystackSecret}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          email: customerEmail,
          amount: amountMinor,
          currency: countryMeta.currency,
          reference,
          mobile_money: {
            phone: paystackMobilePhone,
            provider,
          },
          metadata: {
            accountId: account.id,
            username: account.username,
            registeredPhone: phoneResult.e164,
            country,
            depositUsd,
            provider,
            stkPrompt,
            custom_fields: [
              {
                display_name: 'Luckymate Deposit Prompt',
                variable_name: 'stk_prompt',
                value: stkPrompt,
              },
            ],
          },
        }),
      });

      const chargeJson = (await chargeResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: {
          reference?: string;
          status?: string;
          display_text?: string;
          url?: string;
          amount?: number;
          currency?: string;
        };
      };

      if (!chargeResp.ok || !chargeJson.status || !chargeJson.data) {
        res.status(400).json({
          success: false,
          message:
            chargeJson.message ||
            `Paystack rejected STK Push (${chargeResp.status}). Try "Paystack Checkout" or verify ${countryMeta.currency} mobile money is enabled on your Paystack account.`,
        });
        return;
      }

      const psStatusRaw = String(chargeJson.data.status || 'pay_offline');
      const psRef = String(chargeJson.data.reference || reference);
      const mappedStatus: PendingPaystackDeposit['status'] =
        psStatusRaw === 'success'
          ? 'success'
          : psStatusRaw === 'send_otp'
          ? 'send_otp'
          : psStatusRaw === 'open_url'
          ? 'open_url'
          : 'pending';

      const depositRecord: PendingPaystackDeposit = {
        reference: psRef,
        accountId: account.id,
        depositUsd,
        depositBase,
        depositLocal,
        expectedMinor: amountMinor,
        currency: countryMeta.currency,
        country,
        phoneE164: phoneResult.e164,
        provider,
        status: mappedStatus,
        credited: false,
        createdAt: new Date().toISOString(),
      };
      pendingPaystackDeposits.set(psRef, depositRecord);

      if (psStatusRaw === 'success') {
        const creditOutcome = creditPaystackDepositIfVerified(psRef, {
          status: 'success',
          amount: chargeJson.data.amount ?? amountMinor,
          currency: chargeJson.data.currency ?? countryMeta.currency,
        });
        const unlockedBonus = creditOutcome.unlockedReferralBonusUsd || 0;
        res.json({
          ...buildWalletFields(account),
          success: true,
          sessionId,
          reference: psRef,
          status: 'success',
          stkPrompt,
          displayText: chargeJson.data.display_text || stkPrompt,
          phone: phoneResult.e164,
          maskedPhone: maskPhone(phoneResult.e164),
          provider,
          depositUsd,
          depositLocal,
          currency: countryMeta.currency,
          unlockedReferralBonusUsd: unlockedBonus,
          message:
            unlockedBonus > 0
              ? `Deposit confirmed! +$${unlockedBonus.toFixed(2)} USD referral bonus unlocked and added to your Real Account.`
              : `Deposit confirmed! ${countryMeta.currency} ${formattedLocal} credited to your Real Account.`,
        });
        return;
      }

      res.json({
        success: true,
        sessionId,
        reference: psRef,
        status:
          psStatusRaw === 'send_otp'
            ? 'send_otp'
            : psStatusRaw === 'open_url'
            ? 'open_url'
            : psStatusRaw === 'pay_offline'
            ? 'pay_offline'
            : 'pending',
        stkPrompt,
        displayText: chargeJson.data.display_text,
        authorizationUrl: chargeJson.data.url,
        phone: phoneResult.e164,
        maskedPhone: maskPhone(phoneResult.e164),
        provider,
        depositUsd,
        depositLocal,
        currency: countryMeta.currency,
        message: 'Confirming real money deposit...',
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        message: `Paystack connection error: ${err instanceof Error ? err.message : 'Network failure'}`,
      });
    }
  });

  app.post('/api/payments/paystack/submit-otp', async (req: Request, res: Response) => {
    const { account } = resolveRequestAccount(req, res);
    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({ success: false, message: 'Paystack is not configured.' });
      return;
    }
    const reference = String(req.body?.reference ?? '').trim();
    const otp = String(req.body?.otp ?? '').trim();
    const record = pendingPaystackDeposits.get(reference);
    if (!record || record.accountId !== account.id) {
      res.status(404).json({ success: false, message: 'Payment reference not found for your account.' });
      return;
    }

    try {
      const otpResp = await fetch('https://api.paystack.co/charge/submit_otp', {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${paystackSecret}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ otp, reference }),
      });
      const otpJson = (await otpResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: { status?: string; amount?: number; currency?: string };
      };
      if (!otpResp.ok || !otpJson.status) {
        res.status(400).json({
          success: false,
          message: otpJson.message || 'OTP verification failed with Paystack.',
        });
        return;
      }
      let unlockedBonus = 0;
      if (otpJson.data?.status === 'success') {
        const creditOutcome = creditPaystackDepositIfVerified(reference, otpJson.data);
        unlockedBonus = creditOutcome.unlockedReferralBonusUsd || 0;
      }
      res.json({
        success: true,
        reference,
        status: record.credited ? 'success' : 'pending',
        credited: record.credited,
        unlockedReferralBonusUsd: unlockedBonus,
        message: record.credited
          ? unlockedBonus > 0
            ? `Payment verified! +$${unlockedBonus.toFixed(2)} USD referral bonus unlocked and added to your Real Account.`
            : `Payment verified! ${record.currency} ${record.depositLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })} reflected on your Real Account.`
          : 'OTP accepted. Waiting for final Paystack confirmation...',
        ...buildWalletFields(account),
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        message: err instanceof Error ? err.message : 'Unable to submit OTP to Paystack.',
      });
    }
  });

  app.get('/api/payments/paystack/verify/:reference', async (req: Request, res: Response) => {
    const { account } = resolveRequestAccount(req, res);
    const reference = String(req.params.reference ?? '').trim();
    if (!reference) {
      res.status(400).json({
        success: false,
        status: 'failed',
        credited: false,
        message: 'Missing Paystack transaction reference.',
        ...buildWalletFields(account),
      });
      return;
    }

    const existingRecord = pendingPaystackDeposits.get(reference);
    if (existingRecord && existingRecord.accountId !== account.id) {
      res.status(403).json({
        success: false,
        status: 'failed',
        credited: false,
        message: 'Deposit reference belongs to another account.',
        ...buildWalletFields(account),
      });
      return;
    }

    if (existingRecord?.credited) {
      res.json({
        success: true,
        reference,
        status: 'success',
        credited: true,
        message: `Deposit of $${existingRecord.depositUsd.toFixed(2)} USD (${existingRecord.currency} ${existingRecord.depositLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) reflected on your Real Account.`,
        ...buildWalletFields(account),
      });
      return;
    }

    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({
        success: false,
        status: 'failed',
        credited: false,
        message: 'Paystack Secret Key is not configured.',
        ...buildWalletFields(account),
      });
      return;
    }

    try {
      const verifyResp = await fetch(
        `https://api.paystack.co/transaction/verify/${encodeURIComponent(reference)}`,
        {
          headers: {
            Authorization: `Bearer ${paystackSecret}`,
            Accept: 'application/json',
          },
        }
      );
      const verifyJson = (await verifyResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: {
          status?: string;
          amount?: number;
          currency?: string;
          channel?: string;
          gateway_response?: string;
          metadata?: PaystackMetadataPayload;
        };
      };

      const meta = verifyJson.data?.metadata;
      if (!existingRecord && (!verifyJson.status || meta?.accountId !== account.id)) {
        res.status(404).json({
          success: false,
          status: 'failed',
          credited: false,
          message: 'Deposit reference not found for your account.',
          ...buildWalletFields(account),
        });
        return;
      }

      const txStatus = String(verifyJson.data?.status || 'pending');
      if (txStatus === 'success') {
        const result = creditPaystackDepositIfVerified(reference, verifyJson.data);
        const rec = result.record ?? existingRecord;
        const unlockedBonus = result.unlockedReferralBonusUsd || 0;
        res.json({
          success: true,
          reference,
          status: 'success',
          credited: Boolean(rec?.credited),
          unlockedReferralBonusUsd: unlockedBonus,
          message:
            unlockedBonus > 0 && rec
              ? `Money deposited! $${rec.depositUsd.toFixed(2)} USD + $${unlockedBonus.toFixed(2)} USD unlocked referral bonus added to your Real Account.`
              : rec
              ? `Money deposited! $${rec.depositUsd.toFixed(2)} USD (${rec.currency} ${rec.depositLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}) added to your Real Account.`
              : 'Money deposited to your Real Account.',
          ...buildWalletFields(account),
        });
        return;
      }

      if (txStatus === 'failed' || txStatus === 'abandoned' || txStatus === 'reversed') {
        if (existingRecord) {
          existingRecord.status = 'failed';
        }
        res.json({
          success: false,
          reference,
          status: 'failed',
          credited: false,
          message:
            verifyJson.data?.gateway_response ||
            'Deposit was cancelled or failed. Please try again.',
          ...buildWalletFields(account),
        });
        return;
      }

      res.json({
        success: true,
        reference,
        status: 'pending',
        credited: false,
        message: 'Confirming real money deposit...',
        ...buildWalletFields(account),
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        status: 'pending',
        credited: false,
        message: `Verification retry needed: ${err instanceof Error ? err.message : 'Network error'}`,
        ...buildWalletFields(account),
      });
    }
  });

  app.post('/api/payments/paystack/webhook', (req: Request, res: Response) => {
    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({ message: 'Paystack not configured' });
      return;
    }

    const signatureHeader = String(req.headers['x-paystack-signature'] || '').trim();
    const rawBuf =
      (req as Request & { rawBody?: Buffer }).rawBody ??
      Buffer.from(JSON.stringify(req.body ?? {}));

    const expectedHex = crypto
      .createHmac('sha512', paystackSecret)
      .update(rawBuf)
      .digest('hex');

    const sigBuf = Buffer.from(signatureHeader, 'hex');
    const expBuf = Buffer.from(expectedHex, 'hex');
    if (
      !signatureHeader ||
      sigBuf.length !== expBuf.length ||
      !crypto.timingSafeEqual(sigBuf, expBuf)
    ) {
      res.status(401).json({ message: 'Invalid Paystack signature' });
      return;
    }

    const event = req.body as {
      event?: string;
      data?: {
        reference?: string;
        status?: string;
        amount?: number;
        currency?: string;
        channel?: string;
        metadata?: PaystackMetadataPayload;
      };
    };
    if (event?.event === 'charge.success' && event.data?.reference) {
      const ref = event.data.reference;
      if (ref.startsWith('LM-WD-') || event.data.metadata?.txKind === 'withdraw_fee') {
        settlePaystackWithdrawalIfVerified(ref, {
          status: event.data.status || 'success',
          amount: event.data.amount,
          currency: event.data.currency,
          channel: event.data.channel,
          metadata: event.data.metadata,
        });
      } else {
        creditPaystackDepositIfVerified(ref, {
          status: event.data.status || 'success',
          amount: event.data.amount,
          currency: event.data.currency,
          channel: event.data.channel,
          metadata: event.data.metadata,
        });
      }
    }

    res.status(200).json({ received: true });
  });

  // ---------------- PAYSTACK REAL WITHDRAWAL ($12 FEE STK PUSH) ----------------

  app.post('/api/payments/paystack/withdraw', async (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    if (account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Register an account first to withdraw from your Real Account.',
      });
      return;
    }

    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({
        success: false,
        paystackConfigured: false,
        message: 'Live payment verification is not configured yet.',
      });
      return;
    }

    const body = req.body ?? {};
    const country = body.country ? parseSupportedCountry(body.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const hasUsd = body.amountUsd !== undefined && body.amountUsd !== null && body.amountUsd !== '';
    const parsedUsd = hasUsd
      ? Number(body.amountUsd)
      : Number(body.amount) / countryMeta.usdRate;

    const minWithdrawLocal = MIN_WITHDRAW_USD * countryMeta.usdRate;
    if (!Number.isFinite(parsedUsd) || parsedUsd < MIN_WITHDRAW_USD || parsedUsd > 50000) {
      res.status(400).json({
        success: false,
        message: `Minimum withdrawal is $${MIN_WITHDRAW_USD.toFixed(2)} USD (${countryMeta.currency} ${minWithdrawLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      });
      return;
    }

    const withdrawUsd = Number(parsedUsd.toFixed(2));
    const withdrawBase = Number((withdrawUsd * BASE_KES_PER_USD).toFixed(2));
    const withdrawLocal = Number((withdrawUsd * countryMeta.usdRate).toFixed(2));
    const currentRealBase = getAccountBalance(account, 'real');
    if (withdrawBase > currentRealBase) {
      const currentLocal = Number(((currentRealBase / BASE_KES_PER_USD) * countryMeta.usdRate).toFixed(2));
      res.status(400).json({
        success: false,
        message: `Insufficient Real wallet balance. Need ${countryMeta.currency} ${withdrawLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })} ($${withdrawUsd.toFixed(2)} USD), available ${countryMeta.currency} ${currentLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}.`,
      });
      return;
    }

    const rawTargetPhone = String(account.phone || body.phone || '').trim();
    const normalized = normalizePhoneNumber(rawTargetPhone, country);
    const phoneResult = normalized.ok
      ? normalized
      : account.phone
      ? normalizePhoneNumber(account.phone, account.country)
      : normalized;

    if (!phoneResult.ok) {
      res.status(400).json({
        success: false,
        message: phoneResult.message,
      });
      return;
    }

    const provider = resolvePaystackProvider(country, body.provider);
    const feeUsd = calculateWithdrawFeeUsd(withdrawUsd);
    const feeBase = Number((feeUsd * BASE_KES_PER_USD).toFixed(2));
    const feeLocal = Number((feeUsd * countryMeta.usdRate).toFixed(2));
    const amountMinor = toPaystackMinorAmount(feeLocal, countryMeta.currency);
    const reference = `LM-WD-${Date.now()}-${crypto.randomBytes(3).toString('hex').toUpperCase()}`;

    const paystackMobilePhone = country === 'Kenya' ? phoneResult.e164 : phoneResult.localDigits;
    const customerEmail =
      account.email || `member.${account.id.replace(/[^a-zA-Z0-9]/g, '').slice(0, 12)}@luckymate.app`;

    const formattedFeeLocal = feeLocal.toLocaleString('en-US', {
      minimumFractionDigits: 2,
      maximumFractionDigits: 2,
    });
    const stkPrompt = `PAY $${feeUsd.toFixed(2)} USD (${countryMeta.currency} ${formattedFeeLocal}) WITHDRAWAL FEE TO LUCKYMATE?`;

    try {
      const chargeResp = await fetch('https://api.paystack.co/charge', {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${paystackSecret}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          email: customerEmail,
          amount: amountMinor,
          currency: countryMeta.currency,
          reference,
          mobile_money: {
            phone: paystackMobilePhone,
            provider,
          },
          metadata: {
            txKind: 'withdraw_fee',
            accountId: account.id,
            username: account.username,
            registeredPhone: phoneResult.e164,
            country,
            withdrawUsd,
            feeUsd,
            provider,
            stkPrompt,
            custom_fields: [
              {
                display_name: 'Luckymate Withdrawal Fee',
                variable_name: 'stk_prompt',
                value: stkPrompt,
              },
            ],
          },
        }),
      });

      const chargeJson = (await chargeResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: {
          reference?: string;
          status?: string;
          display_text?: string;
          url?: string;
          amount?: number;
          currency?: string;
        };
      };

      if (!chargeResp.ok || !chargeJson.status || !chargeJson.data) {
        res.status(400).json({
          success: false,
          message:
            chargeJson.message ||
            `Unable to initiate $${feeUsd.toFixed(2)} USD withdrawal fee request (${chargeResp.status}).`,
        });
        return;
      }

      const psStatusRaw = String(chargeJson.data.status || 'pay_offline');
      const psRef = String(chargeJson.data.reference || reference);
      const mappedStatus: PendingPaystackWithdrawFee['status'] =
        psStatusRaw === 'success'
          ? 'success'
          : psStatusRaw === 'send_otp'
          ? 'send_otp'
          : psStatusRaw === 'open_url'
          ? 'open_url'
          : 'pending';

      const withdrawRecord: PendingPaystackWithdrawFee = {
        reference: psRef,
        accountId: account.id,
        withdrawUsd,
        withdrawBase,
        withdrawLocal,
        feeUsd,
        feeBase,
        feeLocal,
        expectedMinor: amountMinor,
        currency: countryMeta.currency,
        country,
        phoneE164: phoneResult.e164,
        provider,
        status: mappedStatus,
        settled: false,
        createdAt: new Date().toISOString(),
      };
      pendingPaystackWithdrawals.set(psRef, withdrawRecord);

      if (psStatusRaw === 'success') {
        settlePaystackWithdrawalIfVerified(psRef, {
          status: 'success',
          amount: chargeJson.data.amount ?? amountMinor,
          currency: chargeJson.data.currency ?? countryMeta.currency,
        });
        res.json({
          ...buildWalletFields(account),
          success: true,
          sessionId,
          reference: psRef,
          status: 'success',
          withdrawUsd,
          feeUsd,
          feeLocal,
          currency: countryMeta.currency,
          message: `Withdrawal completed! Real balance is now ${countryMeta.currency} 0.00.`,
        });
        return;
      }

      res.json({
        success: true,
        sessionId,
        reference: psRef,
        status:
          psStatusRaw === 'send_otp'
            ? 'send_otp'
            : psStatusRaw === 'open_url'
            ? 'open_url'
            : psStatusRaw === 'pay_offline'
            ? 'pay_offline'
            : 'pending',
        stkPrompt,
        displayText: chargeJson.data.display_text,
        authorizationUrl: chargeJson.data.url,
        phone: phoneResult.e164,
        maskedPhone: maskPhone(phoneResult.e164),
        provider,
        withdrawUsd,
        feeUsd,
        feeLocal,
        currency: countryMeta.currency,
        message: `Confirm $${feeUsd.toFixed(2)} USD withdrawal fee on your phone.`,
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        message: `Payment connection error: ${err instanceof Error ? err.message : 'Network failure'}`,
      });
    }
  });

  app.post('/api/payments/paystack/withdraw-checkout', async (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    if (account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Register an account first to withdraw from your Real Account.',
      });
      return;
    }

    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({
        success: false,
        paystackConfigured: false,
        message: 'Live payment verification is not configured yet.',
      });
      return;
    }

    const body = req.body ?? {};
    const country = body.country ? parseSupportedCountry(body.country) : account.country;
    const countryMeta = COUNTRY_META[country];
    const hasUsd = body.amountUsd !== undefined && body.amountUsd !== null && body.amountUsd !== '';
    const parsedUsd = hasUsd
      ? Number(body.amountUsd)
      : Number(body.amount) / countryMeta.usdRate;

    const minWithdrawLocal = MIN_WITHDRAW_USD * countryMeta.usdRate;
    if (!Number.isFinite(parsedUsd) || parsedUsd < MIN_WITHDRAW_USD || parsedUsd > 50000) {
      res.status(400).json({
        success: false,
        message: `Minimum withdrawal is $${MIN_WITHDRAW_USD.toFixed(2)} USD (${countryMeta.currency} ${minWithdrawLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}).`,
      });
      return;
    }

    const withdrawUsd = Number(parsedUsd.toFixed(2));
    const withdrawBase = Number((withdrawUsd * BASE_KES_PER_USD).toFixed(2));
    const withdrawLocal = Number((withdrawUsd * countryMeta.usdRate).toFixed(2));
    const currentRealBase = getAccountBalance(account, 'real');
    if (withdrawBase > currentRealBase) {
      const currentLocal = Number(((currentRealBase / BASE_KES_PER_USD) * countryMeta.usdRate).toFixed(2));
      res.status(400).json({
        success: false,
        message: `Insufficient Real wallet balance. Need ${countryMeta.currency} ${withdrawLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })} ($${withdrawUsd.toFixed(2)} USD), available ${countryMeta.currency} ${currentLocal.toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 })}.`,
      });
      return;
    }

    const rawTargetPhone = String(account.phone || body.phone || '').trim();
    const normalized = normalizePhoneNumber(rawTargetPhone, country);
    const phoneResult = normalized.ok
      ? normalized
      : account.phone
      ? normalizePhoneNumber(account.phone, account.country)
      : normalized;
    const phoneE164 = phoneResult.ok ? phoneResult.e164 : rawTargetPhone;

    const feeUsd = calculateWithdrawFeeUsd(withdrawUsd);
    const feeBase = Number((feeUsd * BASE_KES_PER_USD).toFixed(2));
    const feeLocal = Number((feeUsd * countryMeta.usdRate).toFixed(2));
    const amountMinor = toPaystackMinorAmount(feeLocal, countryMeta.currency);
    const reference = `LM-WD-${Date.now()}-${crypto.randomBytes(3).toString('hex').toUpperCase()}`;
    const customerEmail =
      account.email || `member.${account.id.replace(/[^a-zA-Z0-9]/g, '').slice(0, 12)}@luckymate.app`;
    const callbackUrl = buildPaystackCallbackUrl(req);
    const formattedFeeLocal = feeLocal.toLocaleString('en-US', {
      minimumFractionDigits: 2,
      maximumFractionDigits: 2,
    });
    const stkPrompt = `PAY $${feeUsd.toFixed(2)} USD (${countryMeta.currency} ${formattedFeeLocal}) WITHDRAWAL FEE TO LUCKYMATE?`;

    try {
      const initPayload: Record<string, unknown> = {
        email: customerEmail,
        amount: amountMinor,
        currency: countryMeta.currency,
        reference,
        channels: ['mobile_money', 'card', 'bank', 'ussd'],
        metadata: {
          txKind: 'withdraw_fee',
          accountId: account.id,
          username: account.username,
          registeredPhone: phoneE164,
          country,
          withdrawUsd,
          feeUsd,
          provider: 'checkout',
          stkPrompt,
        },
      };
      if (callbackUrl) {
        initPayload.callback_url = callbackUrl;
      }

      const initResp = await fetch('https://api.paystack.co/transaction/initialize', {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${paystackSecret}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(initPayload),
      });

      const initJson = (await initResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: {
          authorization_url?: string;
          access_code?: string;
          reference?: string;
        };
      };

      if (!initResp.ok || !initJson.status || !initJson.data?.authorization_url) {
        res.status(400).json({
          success: false,
          message:
            initJson.message ||
            `Could not initialize $${feeUsd.toFixed(2)} USD withdrawal fee payment (${initResp.status}).`,
        });
        return;
      }

      const psRef = String(initJson.data.reference || reference);
      const withdrawRecord: PendingPaystackWithdrawFee = {
        reference: psRef,
        accountId: account.id,
        withdrawUsd,
        withdrawBase,
        withdrawLocal,
        feeUsd,
        feeBase,
        feeLocal,
        expectedMinor: amountMinor,
        currency: countryMeta.currency,
        country,
        phoneE164,
        provider: 'checkout',
        status: 'open_url',
        settled: false,
        createdAt: new Date().toISOString(),
      };
      pendingPaystackWithdrawals.set(psRef, withdrawRecord);

      res.json({
        success: true,
        sessionId,
        reference: psRef,
        status: 'open_url',
        stkPrompt,
        displayText: stkPrompt,
        authorizationUrl: initJson.data.authorization_url,
        accessCode: initJson.data.access_code,
        phone: phoneE164,
        maskedPhone: phoneE164 ? maskPhone(phoneE164) : '',
        provider: 'checkout',
        withdrawUsd,
        feeUsd,
        feeLocal,
        currency: countryMeta.currency,
        message: `Confirm $${feeUsd.toFixed(2)} USD withdrawal fee to complete withdrawal.`,
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        message: `Payment connection error: ${err instanceof Error ? err.message : 'Network failure'}`,
      });
    }
  });

  app.post('/api/payments/paystack/withdraw/submit-otp', async (req: Request, res: Response) => {
    const { account } = resolveRequestAccount(req, res);
    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({ success: false, message: 'Live payment processor is not configured.' });
      return;
    }
    const reference = String(req.body?.reference ?? '').trim();
    const otp = String(req.body?.otp ?? '').trim();
    const record = pendingPaystackWithdrawals.get(reference);
    if (!record || record.accountId !== account.id) {
      res.status(404).json({ success: false, message: 'Withdrawal reference not found for your account.' });
      return;
    }

    try {
      const otpResp = await fetch('https://api.paystack.co/charge/submit_otp', {
        method: 'POST',
        headers: {
          Authorization: `Bearer ${paystackSecret}`,
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ otp, reference }),
      });
      const otpJson = (await otpResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: { status?: string; amount?: number; currency?: string };
      };
      if (!otpResp.ok || !otpJson.status) {
        res.status(400).json({
          success: false,
          message: otpJson.message || 'Verification code failed.',
        });
        return;
      }
      if (otpJson.data?.status === 'success') {
        settlePaystackWithdrawalIfVerified(reference, otpJson.data);
      }
      res.json({
        success: true,
        reference,
        status: record.settled ? 'success' : 'pending',
        settled: record.settled,
        withdrawUsd: record.withdrawUsd,
        feeUsd: record.feeUsd,
        message: record.settled
          ? `Withdrawal fee confirmed! Your Real balance is now ${record.currency} 0.00.`
          : 'Code accepted. Confirming withdrawal fee...',
        ...buildWalletFields(account),
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        message: err instanceof Error ? err.message : 'Unable to submit verification code.',
      });
    }
  });

  app.get('/api/payments/paystack/withdraw/verify/:reference', async (req: Request, res: Response) => {
    const { account } = resolveRequestAccount(req, res);
    const reference = String(req.params.reference ?? '').trim();
    if (!reference) {
      res.status(400).json({
        success: false,
        status: 'failed',
        settled: false,
        message: 'Missing withdrawal reference.',
        ...buildWalletFields(account),
      });
      return;
    }

    const existingRecord = pendingPaystackWithdrawals.get(reference);
    if (existingRecord && existingRecord.accountId !== account.id) {
      res.status(403).json({
        success: false,
        status: 'failed',
        settled: false,
        message: 'Withdrawal reference belongs to another account.',
        ...buildWalletFields(account),
      });
      return;
    }

    if (existingRecord?.settled) {
      res.json({
        success: true,
        reference,
        status: 'success',
        settled: true,
        withdrawUsd: existingRecord.withdrawUsd,
        feeUsd: existingRecord.feeUsd,
        message: `Money withdrawn! Real Account balance is now ${existingRecord.currency} 0.00.`,
        ...buildWalletFields(account),
      });
      return;
    }

    const paystackSecret = process.env.PAYSTACK_SECRET_KEY;
    if (!paystackSecret) {
      res.status(503).json({
        success: false,
        status: 'failed',
        settled: false,
        message: 'Live payment processor is not configured.',
        ...buildWalletFields(account),
      });
      return;
    }

    try {
      const verifyResp = await fetch(
        `https://api.paystack.co/transaction/verify/${encodeURIComponent(reference)}`,
        {
          headers: {
            Authorization: `Bearer ${paystackSecret}`,
            Accept: 'application/json',
          },
        }
      );
      const verifyJson = (await verifyResp.json().catch(() => ({}))) as {
        status?: boolean;
        message?: string;
        data?: {
          status?: string;
          amount?: number;
          currency?: string;
          channel?: string;
          gateway_response?: string;
          metadata?: PaystackMetadataPayload;
        };
      };

      const meta = verifyJson.data?.metadata;
      if (!existingRecord && (!verifyJson.status || meta?.accountId !== account.id || meta?.txKind !== 'withdraw_fee')) {
        res.status(404).json({
          success: false,
          status: 'failed',
          settled: false,
          message: 'Withdrawal reference not found for your account.',
          ...buildWalletFields(account),
        });
        return;
      }

      const txStatus = String(verifyJson.data?.status || 'pending');
      if (txStatus === 'success') {
        const result = settlePaystackWithdrawalIfVerified(reference, verifyJson.data);
        const rec = result.record ?? existingRecord;
        res.json({
          success: true,
          reference,
          status: 'success',
          settled: Boolean(rec?.settled),
          withdrawUsd: rec?.withdrawUsd ?? MIN_WITHDRAW_USD,
          feeUsd: rec?.feeUsd ?? calculateWithdrawFeeUsd(rec?.withdrawUsd ?? MIN_WITHDRAW_USD),
          message: rec
            ? `Money withdrawn ($${rec.withdrawUsd.toFixed(2)} USD). Real balance is now ${rec.currency} 0.00.`
            : 'Money withdrawn. Real balance is now 0.00.',
          ...buildWalletFields(account),
        });
        return;
      }

      if (txStatus === 'failed' || txStatus === 'abandoned' || txStatus === 'reversed') {
        if (existingRecord) {
          existingRecord.status = 'failed';
        }
        res.json({
          success: false,
          reference,
          status: 'failed',
          settled: false,
          message:
            verifyJson.data?.gateway_response ||
            'Withdrawal fee payment was cancelled or failed. Please try again.',
          ...buildWalletFields(account),
        });
        return;
      }

      const pendingFeeUsd = existingRecord?.feeUsd ?? WITHDRAW_FEE_USD;
      res.json({
        success: true,
        reference,
        status: 'pending',
        settled: false,
        message: `Confirming $${pendingFeeUsd.toFixed(2)} USD withdrawal fee...`,
        ...buildWalletFields(account),
      });
    } catch (err) {
      res.status(502).json({
        success: false,
        status: 'pending',
        settled: false,
        message: `Verification retry needed: ${err instanceof Error ? err.message : 'Network error'}`,
        ...buildWalletFields(account),
      });
    }
  });

  app.post('/api/demo-slip', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const body = req.body ?? {};
    const stake = Number(body.stake);
    const picks = Array.isArray(body.picks) ? body.picks : [];
    const walletMode: 'demo' | 'real' =
      body.walletMode === 'real' || body.walletMode === 'demo'
        ? body.walletMode
        : account.activeAccountType;

    if (walletMode === 'real' && account.isGuest) {
      res.status(401).json({
        success: false,
        requiresRegistration: true,
        message: 'Please register an account to place Real Account bets.',
      });
      return;
    }

    if (picks.length === 0) {
      res.status(400).json({
        success: false,
        message: 'Select at least one match outcome before placing a bet.',
      });
      return;
    }

    if (!Number.isFinite(stake) || stake <= 0 || stake > 100000) {
      res.status(400).json({
        success: false,
        message: 'Enter a valid stake amount.',
      });
      return;
    }

    if (stake > getAccountBalance(account, walletMode)) {
      res.status(400).json({
        success: false,
        message:
          walletMode === 'real'
            ? 'Insufficient Real balance. Make a payment/deposit first.'
            : 'Insufficient Demo balance. Reset or switch account.',
      });
      return;
    }

    const combinedOdds = picks.reduce((acc: number, item: { odds?: number }) => {
      const oddsVal = Number(item?.odds);
      return acc * (Number.isFinite(oddsVal) && oddsVal > 1 ? oddsVal : 1);
    }, 1);

    const roundedStake = Number(stake.toFixed(2));
    const potentialReturn = Number((roundedStake * combinedOdds).toFixed(2));
    const matchTitle =
      picks.length === 1
        ? String(picks[0]?.matchLabel || 'Single Match Pick')
        : `Accumulator (${picks.length} matches)`;

    const cur = COUNTRY_META[account.country].currency;
    adjustAccountBalance(account, walletMode, -roundedStake);
    account.totalWagered = Number((account.totalWagered + roundedStake).toFixed(2));
    account.gamesPlayed += 1;
    account.updatedAt = Date.now();
    account.history.unshift({
      id: crypto.randomUUID(),
      type: 'bet_pending',
      amount: -roundedStake,
      stake: roundedStake,
      odds: Number(combinedOdds.toFixed(2)),
      status: 'Pending',
      label: matchTitle,
      detail: `[${walletMode.toUpperCase()}] Stake: ${cur} ${roundedStake.toFixed(0)} | Est. ${cur} ${potentialReturn.toFixed(0)}`,
      createdAt: new Date().toISOString(),
    });
    account.history = account.history.slice(0, 40);
    if (!account.isGuest) scheduleSaveStore();

    res.json({
      success: true,
      sessionId,
      message: `${walletMode === 'real' ? 'Real' : 'Demo'} bet placed: ${cur} ${roundedStake.toFixed(2)} (Est. return ${cur} ${potentialReturn.toFixed(2)}).`,
      ...buildWalletFields(account),
      potentialReturn,
    });
  });

  app.post('/api/wallet/reset', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const cur = COUNTRY_META[account.country].currency;
    account.demoBalance = STARTING_DEMO_BALANCE;
    account.totalWagered = 0;
    account.totalWon = 0;
    account.gamesPlayed = 0;
    account.history = account.history.filter(
      (h) => h.type === 'deposit' || h.type === 'withdraw'
    );
    account.updatedAt = Date.now();
    if (!account.isGuest) scheduleSaveStore();

    res.json({
      success: true,
      sessionId,
      ...buildWalletFields(account),
      message: `Demo balance reset to ${cur} 500.00.`,
    });
  });

  // ---------------- LIVE CRASH ROOMS & LOBBY API ----------------

  app.get('/api/games', (_req: Request, res: Response) => {
    res.json(
      CRASH_GAME_IDS.map((id) => ({
        id,
        name: CRASH_GAME_NAMES[id],
        mode: 'demo',
      }))
    );
  });

  app.get('/api/games/lobby', (_req: Request, res: Response) => {
    const nowMs = Date.now();
    res.json(
      CRASH_GAME_IDS.map((id) => {
        const room = rooms[id];
        const countdown =
          room.status === 'betting'
            ? Number(Math.max(0, (room.deadlineMs - nowMs) / 1000).toFixed(1))
            : 0;
        const lastRound = room.recentRounds[0];
        return {
          id,
          name: CRASH_GAME_NAMES[id],
          roundNumber: room.roundNumber,
          status: room.status,
          multiplier: Number(room.multiplier.toFixed(2)),
          countdown,
          connectedPlayers: getRoomConnectedPlayers(room),
          activeBetsCount: room.activeBets.length,
          lastCrashPoint: lastRound ? lastRound.crashPoint : null,
        };
      })
    );
  });

  app.get('/api/state/:game', (req: Request, res: Response) => {
    const game = req.params.game as CrashGameId;
    if (!CRASH_GAME_IDS.includes(game)) {
      res.status(404).json({ message: 'Game not found.' });
      return;
    }
    const { sessionId, account } = resolveRequestAccount(req, res);
    const room = rooms[game];
    const slip1 = room.activeBets.find((b) => b.accountId === account.id && b.slot === 1) ?? null;
    const slip2 = room.activeBets.find((b) => b.accountId === account.id && b.slot === 2) ?? null;
    res.json({
      sessionId,
      ...buildRoomSnapshot(room),
      myActiveBets: {
        slip1: slip1 ? serializeBetPublic(slip1) : null,
        slip2: slip2 ? serializeBetPublic(slip2) : null,
      },
    });
  });

  app.post('/api/bet', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const body = req.body ?? {};
    const game = String(body.game ?? '') as CrashGameId;
    const slot: 1 | 2 = Number(body.slot) === 2 ? 2 : 1;
    const amount = Number(body.amount);
    const rawAuto = body.autoCashout;
    const autoCashout =
      rawAuto !== undefined && rawAuto !== null && rawAuto !== '' ? Number(rawAuto) : null;
    const walletMode: 'demo' | 'real' =
      body.walletMode === 'real' || body.walletMode === 'demo'
        ? body.walletMode
        : account.activeAccountType;

    if (walletMode === 'real' && account.isGuest) {
      res.status(401).json({
        requiresRegistration: true,
        message: 'Please register an account before playing with a Real Account.',
      });
      return;
    }

    if (!CRASH_GAME_IDS.includes(game)) {
      res.status(404).json({ message: 'Game not found.' });
      return;
    }

    const room = rooms[game];
    if (room.status !== 'betting') {
      res
        .status(400)
        .json({ message: `Betting is closed for ${CRASH_GAME_NAMES[game]} Round #${room.roundNumber}.` });
      return;
    }

    if (!Number.isFinite(amount) || amount <= 0 || amount > 100000) {
      res.status(400).json({ message: 'Enter a bet between 1 and 100,000 KES.' });
      return;
    }

    if (
      autoCashout !== null &&
      (!Number.isFinite(autoCashout) || autoCashout < 1.01 || autoCashout > 100)
    ) {
      res.status(400).json({ message: 'Auto cashout must be between 1.01x and 100.00x.' });
      return;
    }

    const alreadyInSlot = room.activeBets.some(
      (b) => b.accountId === account.id && b.slot === slot && b.status === 'active'
    );
    if (alreadyInSlot) {
      res.status(400).json({ message: `Slip ${slot} already has an active bet in this round.` });
      return;
    }

    const roundedAmount = Number(amount.toFixed(2));
    const available = getAccountBalance(account, walletMode);
    if (available < roundedAmount) {
      res.status(400).json({
        message:
          walletMode === 'real'
            ? 'Insufficient Real balance (KES 0.00). Please make a deposit first.'
            : 'Insufficient Demo balance.',
      });
      return;
    }

    adjustAccountBalance(account, walletMode, -roundedAmount);
    account.totalWagered = Number((account.totalWagered + roundedAmount).toFixed(2));
    account.gamesPlayed += 1;
    account.updatedAt = Date.now();

    const walletTxId = crypto.randomUUID();
    account.history.unshift({
      id: walletTxId,
      type: 'crash_stake',
      amount: -roundedAmount,
      stake: roundedAmount,
      status: 'Pending',
      label: `${CRASH_GAME_NAMES[game]} #${room.roundNumber} (Slip ${slot})`,
      detail: `[${walletMode.toUpperCase()}] Stake: KES ${roundedAmount.toFixed(0)} | ${
        autoCashout ? `Auto @ ${autoCashout.toFixed(2)}x` : 'Manual Cashout'
      }`,
      createdAt: new Date().toISOString(),
    });
    account.history = account.history.slice(0, 40);

    const bet: RoomBetRecord = {
      id: crypto.randomUUID(),
      slot,
      accountId: account.id,
      username: account.username,
      roundId: room.roundId,
      game,
      amount: roundedAmount,
      autoCashout: autoCashout !== null ? Number(autoCashout.toFixed(2)) : null,
      status: 'active',
      payout: 0,
      cashoutMultiplier: null,
      walletTxId,
      walletMode,
      createdAt: new Date().toISOString(),
    };
    room.activeBets.unshift(bet);

    broadcastRoom(room, {
      type: 'bet',
      game: room.game,
      roundId: room.roundId,
      ...serializeBetPublic(bet),
    });

    res.json({
      success: true,
      sessionId,
      message: `Slip ${slot} ${walletMode} bet accepted for Round #${room.roundNumber}.`,
      roundId: room.roundId,
      bet: serializeBetPublic(bet),
      ...buildWalletFields(account),
    });
  });

  app.post('/api/bet/cancel', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const body = req.body ?? {};
    const game = String(body.game ?? '') as CrashGameId;
    const slot: 1 | 2 = Number(body.slot) === 2 ? 2 : 1;

    if (!CRASH_GAME_IDS.includes(game)) {
      res.status(404).json({ message: 'Game not found.' });
      return;
    }

    const room = rooms[game];
    if (room.status !== 'betting') {
      res.status(400).json({ message: 'Bets can only be cancelled before takeoff.' });
      return;
    }

    const idx = room.activeBets.findIndex(
      (b) =>
        b.accountId === account.id &&
        b.roundId === room.roundId &&
        b.slot === slot &&
        b.status === 'active'
    );
    if (idx === -1) {
      res.status(400).json({ message: `No active Slip ${slot} bet to cancel.` });
      return;
    }

    const [removed] = room.activeBets.splice(idx, 1);
    const mode = removed.walletMode ?? account.activeAccountType;
    adjustAccountBalance(account, mode, removed.amount);
    account.totalWagered = Math.max(0, Number((account.totalWagered - removed.amount).toFixed(2)));
    account.gamesPlayed = Math.max(0, account.gamesPlayed - 1);
    account.history = account.history.filter((t) => t.id !== removed.walletTxId);
    account.updatedAt = Date.now();

    broadcastRoom(room, {
      type: 'bet_cancelled',
      game: room.game,
      roundId: room.roundId,
      betId: removed.id,
      slot,
    });

    res.json({
      success: true,
      sessionId,
      slot,
      ...buildWalletFields(account),
    });
  });

  app.post('/api/cashout', (req: Request, res: Response) => {
    const { sessionId, account } = resolveRequestAccount(req, res);
    const body = req.body ?? {};
    const game = String(body.game ?? '') as CrashGameId;
    const slot: 1 | 2 = Number(body.slot) === 2 ? 2 : 1;

    if (!CRASH_GAME_IDS.includes(game)) {
      res.status(404).json({ message: 'Game not found.' });
      return;
    }

    const room = rooms[game];
    if (room.status !== 'running') {
      res.status(400).json({ message: 'Cash-out is only available while the round is flying.' });
      return;
    }

    const bet = room.activeBets.find(
      (b) =>
        b.accountId === account.id &&
        b.roundId === room.roundId &&
        b.slot === slot &&
        b.status === 'active'
    );
    if (!bet) {
      res.status(400).json({ message: `No active bet found on Slip ${slot} in this round.` });
      return;
    }

    settleBetWin(bet, room.multiplier, false, room);

    res.json({
      success: true,
      sessionId,
      slot,
      multiplier: bet.cashoutMultiplier,
      payout: bet.payout,
      bet: serializeBetPublic(bet),
      ...buildWalletFields(account),
    });
  });

  app.get('/api/rounds/:game', (req: Request, res: Response) => {
    const game = req.params.game as CrashGameId;
    if (!CRASH_GAME_IDS.includes(game)) {
      res.status(404).json({ message: 'Game not found.' });
      return;
    }
    const room = rooms[game];
    res.json(room.recentRounds.slice(0, 30).map(sanitizeRoundForPublic));
  });

  // ---------------- STANDALONE OPERATOR CRASH PREDICTOR API ----------------

  function timingSafeCodeEqual(provided: string, expected: string): boolean {
    const a = Buffer.from(provided);
    const b = Buffer.from(expected);
    return a.length === b.length && crypto.timingSafeEqual(a, b);
  }

  function createPredictorToken(): string {
    const expiry = Math.floor(Date.now() / 1000) + 86400;
    const payload = `predictor:${expiry}`;
    const sig = crypto.createHmac('sha256', runtimeAppSecret).update(payload).digest('hex');
    return `${payload}:${sig}`;
  }

  function verifyPredictorRequest(req: Request): boolean {
    const predHeader =
      typeof req.headers['x-predictor-token'] === 'string'
        ? req.headers['x-predictor-token'].trim()
        : '';
    if (predHeader) {
      try {
        const parts = predHeader.split(':');
        if (parts.length === 3 && parts[0] === 'predictor') {
          const payload = `${parts[0]}:${parts[1]}`;
          const expected = crypto.createHmac('sha256', runtimeAppSecret).update(payload).digest('hex');
          const sigBuf = Buffer.from(parts[2], 'hex');
          const expBuf = Buffer.from(expected, 'hex');
          if (
            sigBuf.length === expBuf.length &&
            crypto.timingSafeEqual(sigBuf, expBuf) &&
            Number(parts[1]) >= Math.floor(Date.now() / 1000)
          ) {
            return true;
          }
        }
      } catch {
        // Fall through to admin token check
      }
    }

    const authHeader = typeof req.headers.authorization === 'string' ? req.headers.authorization : '';
    const bearer = authHeader.startsWith('Bearer ') ? authHeader.slice(7).trim() : '';
    const account = bearer ? verifyAuthToken(bearer) : null;
    return Boolean(account?.isAdmin);
  }

  function buildPredictorSnapshot(room: CrashRoom) {
    const nowMs = Date.now();
    const bettingCountdown =
      room.status === 'betting' ? Math.max(0, (room.deadlineMs - nowMs) / 1000) : 0;
    const pauseRemaining =
      room.status === 'crashed'
        ? Math.max(0, (room.crashedAtMs + ROUND_PAUSE_SECONDS * 1000 - nowMs) / 1000)
        : 0;

    // When betting, current round hasn't launched yet so room.crashPoint IS the upcoming crash.
    // When running or crashed, upcomingCrashPoint IS the very next round's exact crash point.
    const primaryTargetRound = room.status === 'betting' ? room.roundNumber : room.roundNumber + 1;
    const primaryPredictedOdd =
      room.status === 'betting' ? room.crashPoint : room.upcomingCrashPoint;

    return {
      game: room.game,
      gameTitle: CRASH_GAME_NAMES[room.game],
      roundNumber: room.roundNumber,
      status: room.status,
      liveMultiplier: Number(room.multiplier.toFixed(2)),
      countdownSeconds: Number(
        (room.status === 'betting' ? bettingCountdown : pauseRemaining).toFixed(1)
      ),
      currentRoundCrashPoint: room.crashPoint,
      targetRoundNumber: primaryTargetRound,
      predictedNextOdd: primaryPredictedOdd,
      followingRoundNumber: primaryTargetRound + 1,
      followingPredictedOdd: room.upcomingCrashPoint,
      recentCrashPoints: room.recentRounds.slice(0, 12).map((r) => ({
        roundNumber: r.roundNumber,
        crashPoint: r.crashPoint,
        endedAt: r.endedAt,
      })),
    };
  }

  app.use('/api/predictor', (_req: Request, res: Response, next) => {
    res.setHeader('Access-Control-Allow-Origin', '*');
    res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
    res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization, x-predictor-token');
    if (_req.method === 'OPTIONS') {
      res.status(204).end();
      return;
    }
    next();
  });

  app.post('/api/predictor/unlock', (req: Request, res: Response) => {
    const code = String(req.body?.accessCode ?? '').trim();
    const codeValid = timingSafeCodeEqual(code, predictorAccessCode);

    if (!codeValid && !verifyPredictorRequest(req)) {
      res.status(401).json({ success: false, message: 'Invalid predictor password.' });
      return;
    }

    res.json({
      success: true,
      predictorToken: createPredictorToken(),
      expiresInSeconds: 86400,
    });
  });

  app.post('/api/predictor/verify-change-code', (req: Request, res: Response) => {
    const code = String(req.body?.code ?? '').trim();
    if (!code || !timingSafeCodeEqual(code, PREDICTOR_CHANGE_PASSWORD_CODE)) {
      res.status(401).json({
        success: false,
        message: 'Invalid security code. Enter the authorized code to change password.',
      });
      return;
    }
    res.json({
      success: true,
      message: 'Code verified. You can now enter a new password.',
    });
  });

  app.post('/api/predictor/change-password', (req: Request, res: Response) => {
    const currentCode = String(req.body?.currentCode ?? '').trim();
    const newPassword = String(req.body?.newPassword ?? '').trim();

    if (!currentCode) {
      res.status(400).json({ success: false, message: 'Enter the security code to change password.' });
      return;
    }

    const authorized = timingSafeCodeEqual(currentCode, PREDICTOR_CHANGE_PASSWORD_CODE);
    if (!authorized) {
      res.status(401).json({ success: false, message: 'Invalid security code. Enter the authorized code to change password.' });
      return;
    }

    if (newPassword.length < 4 || newPassword.length > 64) {
      res.status(400).json({ success: false, message: 'New password must be between 4 and 64 characters.' });
      return;
    }

    predictorAccessCode = newPassword;
    saveStoreNow();

    res.json({
      success: true,
      predictorToken: createPredictorToken(),
      expiresInSeconds: 86400,
      message: 'Predictor password updated successfully.',
    });
  });

  app.get('/api/predictor/all', (req: Request, res: Response) => {
    if (!verifyPredictorRequest(req)) {
      res.status(403).json({ message: 'Forbidden' });
      return;
    }
    res.json({
      updatedAt: new Date().toISOString(),
      games: CRASH_GAME_IDS.map((id) => buildPredictorSnapshot(rooms[id])),
    });
  });

  app.get('/api/predictor/:game', (req: Request, res: Response) => {
    if (!verifyPredictorRequest(req)) {
      res.status(403).json({ message: 'Forbidden' });
      return;
    }
    const game = req.params.game as CrashGameId;
    if (!CRASH_GAME_IDS.includes(game)) {
      res.status(404).json({ message: 'Game not found.' });
      return;
    }
    res.json(buildPredictorSnapshot(rooms[game]));
  });

  // ---------------- OFFICIAL REAL-GAME LIVESCORE PROXY API ----------------

  interface LiveScoreCacheEntry {
    expiresAt: number;
    payload: unknown;
  }

  const liveScoreCache = new Map<string, LiveScoreCacheEntry>();

  const OFFICIAL_SOCCER_LEAGUES: { slug: string; fallbackName: string }[] = [
    { slug: 'eng.1', fallbackName: 'English Premier League' },
    { slug: 'uefa.champions', fallbackName: 'UEFA Champions League' },
    { slug: 'uefa.europa', fallbackName: 'UEFA Europa League' },
    { slug: 'esp.1', fallbackName: 'Spanish LALIGA' },
    { slug: 'ita.1', fallbackName: 'Italian Serie A' },
    { slug: 'ger.1', fallbackName: 'German Bundesliga' },
    { slug: 'fra.1', fallbackName: 'French Ligue 1' },
    { slug: 'caf.nations', fallbackName: 'Africa Cup of Nations' },
    { slug: 'fifa.friendly', fallbackName: 'FIFA International Friendlies' },
    { slug: 'usa.1', fallbackName: 'MLS' },
  ];

  const WORLD_PLAYER_LEAGUES: { slug: string; name: string; featuredTeamIds: string[] }[] = [
    { slug: 'eng.1', name: 'Premier League', featuredTeamIds: ['359', '382', '364', '363'] }, // Arsenal, Man City, Liverpool, Chelsea
    { slug: 'esp.1', name: 'LaLiga', featuredTeamIds: ['86', '83', '1068'] }, // Real Madrid, Barcelona, Atlético Madrid
    { slug: 'ita.1', name: 'Serie A', featuredTeamIds: ['110', '103', '111'] }, // Inter, AC Milan, Juventus
    { slug: 'ger.1', name: 'Bundesliga', featuredTeamIds: ['132', '131', '124'] }, // Bayern, Leverkusen, Dortmund
    { slug: 'fra.1', name: 'Ligue 1', featuredTeamIds: ['160', '176'] }, // PSG, Marseille
    { slug: 'usa.1', name: 'MLS', featuredTeamIds: ['20232', '18966'] }, // Inter Miami CF, LAFC
  ];

  interface WorldTeamMeta {
    id: string;
    name: string;
    shortName: string;
    abbreviation: string;
    logo: string;
    color: string;
    leagueSlug: string;
    leagueName: string;
  }

  interface WorldPlayerRecord {
    id: string;
    name: string;
    shortName: string;
    jersey: string;
    position: string;
    positionAbbr: string;
    nationality: string;
    age: number | null;
    height: string;
    weight: string;
    teamId: string;
    teamName: string;
    teamAbbr: string;
    teamLogo: string;
    teamColor: string;
    leagueSlug: string;
    leagueName: string;
    stats: {
      appearances: number;
      goals: number;
      assists: number;
      shots: number;
      yellowCards: number;
      redCards: number;
      saves: number;
    };
  }

  const leagueTeamsCache = new Map<string, { expiresAt: number; teams: WorldTeamMeta[] }>();
  const teamRosterCache = new Map<string, { expiresAt: number; players: WorldPlayerRecord[] }>();
  const matchSummaryCache = new Map<string, { expiresAt: number; payload: unknown }>();

  async function fetchLeagueTeamsCached(
    leagueSlug: string,
    leagueName: string
  ): Promise<WorldTeamMeta[]> {
    const cached = leagueTeamsCache.get(leagueSlug);
    if (cached && cached.expiresAt > Date.now()) {
      return cached.teams;
    }

    const url = `https://site.api.espn.com/apis/site/v2/sports/soccer/${leagueSlug}/teams`;
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(8000),
      headers: { Accept: 'application/json', 'User-Agent': 'Luckymate-Soccer/1.0' },
    });
    if (!resp.ok) return [];

    const json = (await resp.json()) as {
      sports?: Array<{
        leagues?: Array<{
          name?: string;
          teams?: Array<{
            team?: {
              id?: string;
              displayName?: string;
              shortDisplayName?: string;
              abbreviation?: string;
              color?: string;
              logos?: Array<{ href?: string }>;
            };
          }>;
        }>;
      }>;
    };

    const resolvedLeagueName = json.sports?.[0]?.leagues?.[0]?.name || leagueName;
    const rawTeams = json.sports?.[0]?.leagues?.[0]?.teams || [];
    const teams: WorldTeamMeta[] = rawTeams
      .map((entry) => entry.team)
      .filter((t): t is NonNullable<typeof t> => Boolean(t?.id && t?.displayName))
      .map((t) => ({
        id: String(t.id),
        name: String(t.displayName),
        shortName: String(t.shortDisplayName || t.displayName),
        abbreviation: String(t.abbreviation || String(t.displayName).slice(0, 3).toUpperCase()),
        logo: String(t.logos?.[0]?.href || ''),
        color: String(t.color || '253141'),
        leagueSlug,
        leagueName: resolvedLeagueName,
      }));

    leagueTeamsCache.set(leagueSlug, {
      expiresAt: Date.now() + 30 * 60_000,
      teams,
    });
    return teams;
  }

  function extractRosterStatMap(
    categories?: Array<{ stats?: Array<{ name?: string; value?: number; displayValue?: string }> }>
  ) {
    const map: Record<string, number> = {};
    for (const cat of categories || []) {
      for (const s of cat.stats || []) {
        if (!s.name) continue;
        const n = Number(s.value ?? s.displayValue);
        if (Number.isFinite(n)) map[s.name] = n;
      }
    }
    return map;
  }

  async function fetchTeamRosterCached(
    leagueSlug: string,
    team: WorldTeamMeta
  ): Promise<WorldPlayerRecord[]> {
    const cacheKey = `${leagueSlug}:${team.id}`;
    const cached = teamRosterCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      return cached.players;
    }

    const url = `https://site.api.espn.com/apis/site/v2/sports/soccer/${leagueSlug}/teams/${team.id}/roster`;
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(8000),
      headers: { Accept: 'application/json', 'User-Agent': 'Luckymate-Soccer/1.0' },
    });
    if (!resp.ok) return [];

    const json = (await resp.json()) as {
      athletes?: Array<{
        id?: string;
        displayName?: string;
        shortName?: string;
        jersey?: string;
        age?: number;
        displayHeight?: string;
        displayWeight?: string;
        citizenship?: string;
        citizenshipCountry?: { alternate?: string };
        position?: { displayName?: string; name?: string; abbreviation?: string };
        statistics?: {
          splits?: {
            categories?: Array<{
              stats?: Array<{ name?: string; value?: number; displayValue?: string }>;
            }>;
          };
        };
      }>;
    };

    const players: WorldPlayerRecord[] = (json.athletes || [])
      .filter((a) => Boolean(a?.id && a?.displayName))
      .map((a) => {
        const stats = extractRosterStatMap(a.statistics?.splits?.categories);
        const posAbbrRaw = String(a.position?.abbreviation || 'M').toUpperCase();
        const posAbbr =
          posAbbrRaw.startsWith('G')
            ? 'G'
            : posAbbrRaw.startsWith('D') || posAbbrRaw.includes('B')
            ? 'D'
            : posAbbrRaw.startsWith('F') || posAbbrRaw.startsWith('S') || posAbbrRaw.includes('W')
            ? 'F'
            : 'M';

        return {
          id: String(a.id),
          name: String(a.displayName),
          shortName: String(a.shortName || a.displayName),
          jersey: String(a.jersey || '-'),
          position: String(a.position?.displayName || a.position?.name || 'Player'),
          positionAbbr: posAbbr,
          nationality: String(a.citizenship || a.citizenshipCountry?.alternate || 'International'),
          age: typeof a.age === 'number' && Number.isFinite(a.age) ? a.age : null,
          height: String(a.displayHeight || ''),
          weight: String(a.displayWeight || ''),
          teamId: team.id,
          teamName: team.name,
          teamAbbr: team.abbreviation,
          teamLogo: team.logo,
          teamColor: team.color,
          leagueSlug: team.leagueSlug,
          leagueName: team.leagueName,
          stats: {
            appearances: stats.appearances || 0,
            goals: stats.totalGoals || 0,
            assists: stats.goalAssists || 0,
            shots: stats.totalShots || 0,
            yellowCards: stats.yellowCards || 0,
            redCards: stats.redCards || 0,
            saves: stats.saves || 0,
          },
        };
      });

    teamRosterCache.set(cacheKey, {
      expiresAt: Date.now() + 15 * 60_000,
      players,
    });
    return players;
  }

  function toDecimalOdds(americanRaw: unknown): number | undefined {
    const num = Number(americanRaw);
    if (!Number.isFinite(num) || num === 0) return undefined;
    const dec = num > 0 ? 1 + num / 100 : 1 + 100 / Math.abs(num);
    if (!Number.isFinite(dec) || dec <= 1) return undefined;
    return Number(dec.toFixed(2));
  }

  function formatYyyymmdd(offsetDays: number): string {
    const dt = new Date(Date.now() + offsetDays * 86_400_000);
    const y = dt.getUTCFullYear();
    const m = String(dt.getUTCMonth() + 1).padStart(2, '0');
    const d = String(dt.getUTCDate()).padStart(2, '0');
    return `${y}${m}${d}`;
  }

  function formatKickoffLabel(isoDate: string): string {
    const dt = new Date(isoDate);
    if (Number.isNaN(dt.getTime())) return '--:--';
    const day = String(dt.getUTCDate()).padStart(2, '0');
    const mon = String(dt.getUTCMonth() + 1).padStart(2, '0');
    const hh = String(dt.getUTCHours()).padStart(2, '0');
    const mm = String(dt.getUTCMinutes()).padStart(2, '0');
    return `${day}/${mon}, ${hh}:${mm} UTC`;
  }

  app.get('/api/livescore', async (req: Request, res: Response) => {
    const rawLeague = String(req.query.league || 'all').trim();
    const rawDay = String(req.query.day || 'today').trim();
    const day: 'yesterday' | 'today' | 'tomorrow' =
      rawDay === 'yesterday' || rawDay === 'tomorrow' ? rawDay : 'today';

    const allowedSlugs = new Set(['all', ...OFFICIAL_SOCCER_LEAGUES.map((l) => l.slug)]);
    const leagueSlug = allowedSlugs.has(rawLeague) ? rawLeague : 'all';

    const cacheKey = `${leagueSlug}:${day}`;
    const cached = liveScoreCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json(cached.payload);
      return;
    }

    const offsetDays = day === 'yesterday' ? -1 : day === 'tomorrow' ? 1 : 0;
    const dateParam = `?dates=${formatYyyymmdd(offsetDays)}`;

    const targets =
      leagueSlug === 'all'
        ? [
            { slug: 'all', fallbackName: 'International & World', useDate: true },
            ...OFFICIAL_SOCCER_LEAGUES.map((l) => ({
              ...l,
              useDate: day !== 'today',
            })),
          ]
        : [
            {
              ...(OFFICIAL_SOCCER_LEAGUES.find((l) => l.slug === leagueSlug) || {
                slug: leagueSlug,
                fallbackName: leagueSlug.toUpperCase(),
              }),
              useDate: day !== 'today',
            },
          ];

    try {
      const settled = await Promise.allSettled(
        targets.map(async (target) => {
          const queryStr = target.useDate ? dateParam : '';
          const url = `https://site.api.espn.com/apis/site/v2/sports/soccer/${target.slug}/scoreboard${queryStr}`;
          const resp = await fetch(url, {
            signal: AbortSignal.timeout(8000),
            headers: {
              Accept: 'application/json',
              'User-Agent': 'Luckymate-LiveScore/1.0',
            },
          });
          if (!resp.ok) {
            throw new Error(`Upstream ${target.slug} HTTP ${resp.status}`);
          }
          const json = (await resp.json()) as {
            leagues?: Array<{ name?: string; shortName?: string }>;
            events?: Array<Record<string, unknown>>;
          };

          const resolvedLeagueName =
            target.slug === 'all'
              ? 'International & World'
              : json.leagues?.[0]?.name || target.fallbackName;

          return {
            slug: target.slug,
            leagueName: resolvedLeagueName,
            events: Array.isArray(json.events) ? json.events : [],
          };
        })
      );

      const fulfilled = settled
        .filter(
          (r): r is PromiseFulfilledResult<{
            slug: string;
            leagueName: string;
            events: Array<Record<string, unknown>>;
          }> => r.status === 'fulfilled'
        )
        .map((r) => r.value);

      if (fulfilled.length === 0) {
        res.status(502).json({
          error: 'Official LiveScore upstream feed is temporarily unreachable.',
        });
        return;
      }

      const matchMap = new Map<
        string,
        {
          id: string;
          league: string;
          leagueSlug: string;
          date: string;
          kickoffLabel: string;
          state: 'pre' | 'in' | 'post';
          statusText: string;
          clock: string;
          completed: boolean;
          venue: string;
          homeTeam: {
            id: string;
            name: string;
            shortName: string;
            abbreviation: string;
            logo: string;
            score: number | null;
            winner: boolean;
            form: string;
            record: string;
            color: string;
          };
          awayTeam: {
            id: string;
            name: string;
            shortName: string;
            abbreviation: string;
            logo: string;
            score: number | null;
            winner: boolean;
            form: string;
            record: string;
            color: string;
          };
          keyEvents?: Array<{
            minute: string;
            type: 'goal' | 'penalty' | 'own_goal' | 'yellow' | 'red';
            playerName: string;
            teamId: string;
            isScoring: boolean;
          }>;
          odds?: {
            home?: number;
            draw?: number;
            away?: number;
          };
        }
      >();

      // Process named leagues first if filtering a specific league, or 'all' (today's real world matches) alongside named leagues
      for (const feed of fulfilled) {
        for (const ev of feed.events as Array<{
          id?: string;
          date?: string;
          status?: {
            displayClock?: string;
            type?: {
              state?: string;
              completed?: boolean;
              detail?: string;
              shortDetail?: string;
              description?: string;
            };
          };
          competitions?: Array<{
            venue?: { fullName?: string; address?: { city?: string } };
            details?: Array<{
              type?: { text?: string };
              clock?: { displayValue?: string };
              team?: { id?: string };
              scoringPlay?: boolean;
              redCard?: boolean;
              yellowCard?: boolean;
              penaltyKick?: boolean;
              ownGoal?: boolean;
              athletesInvolved?: Array<{
                displayName?: string;
                shortName?: string;
              }>;
            }>;
            competitors?: Array<{
              homeAway?: string;
              score?: string;
              winner?: boolean;
              form?: string;
              records?: Array<{ summary?: string }>;
              team?: {
                id?: string;
                displayName?: string;
                shortDisplayName?: string;
                abbreviation?: string;
                logo?: string;
                color?: string;
              };
            }>;
            odds?: Array<{
              moneyline?: {
                home?: { close?: { odds?: string }; open?: { odds?: string } };
                away?: { close?: { odds?: string }; open?: { odds?: string } };
                draw?: { close?: { odds?: string }; open?: { odds?: string } };
              };
            }>;
          }>;
        }>) {
          const eventId = String(ev.id || '');
          if (!eventId) continue;

          // Keep the first feed that maps this event; if 'all' already added it and a named league arrives, prefer the named league label
          const existingMatch = matchMap.get(eventId);
          if (existingMatch && feed.slug === 'all') continue;

          const comp = ev.competitions?.[0];
          const competitors = comp?.competitors || [];
          const home = competitors.find((c) => c.homeAway === 'home') || competitors[0];
          const away = competitors.find((c) => c.homeAway === 'away') || competitors[1];
          if (!home?.team || !away?.team) continue;

          const rawState = ev.status?.type?.state;
          const state: 'pre' | 'in' | 'post' =
            rawState === 'in' ? 'in' : rawState === 'post' ? 'post' : 'pre';

          const parseScore = (val?: string) => {
            if (state === 'pre') return null;
            const n = Number(val);
            return Number.isFinite(n) ? n : 0;
          };

          const ml = comp?.odds?.[0]?.moneyline;
          const homeOdds = toDecimalOdds(ml?.home?.close?.odds ?? ml?.home?.open?.odds);
          const drawOdds = toDecimalOdds(ml?.draw?.close?.odds ?? ml?.draw?.open?.odds);
          const awayOdds = toDecimalOdds(ml?.away?.close?.odds ?? ml?.away?.open?.odds);
          const hasOdds =
            homeOdds !== undefined && drawOdds !== undefined && awayOdds !== undefined;

          const dateIso = String(ev.date || new Date().toISOString());
          const venueName = comp?.venue?.fullName || '';
          const venueCity = comp?.venue?.address?.city || '';
          const venue =
            venueName && venueCity
              ? `${venueName}, ${venueCity}`
              : venueName || venueCity || '';

          const statusText =
            ev.status?.type?.shortDetail ||
            ev.status?.type?.detail ||
            ev.status?.type?.description ||
            (state === 'in' ? 'LIVE' : state === 'post' ? 'FT' : 'Scheduled');

          const keyEvents = (comp?.details || [])
            .map((d) => {
              const athlete = d.athletesInvolved?.[0];
              const playerName = String(athlete?.shortName || athlete?.displayName || '').trim();
              if (!playerName) return null;
              const eventType: 'goal' | 'penalty' | 'own_goal' | 'yellow' | 'red' = d.ownGoal
                ? 'own_goal'
                : d.penaltyKick
                ? 'penalty'
                : d.scoringPlay
                ? 'goal'
                : d.redCard
                ? 'red'
                : 'yellow';
              return {
                minute: String(d.clock?.displayValue || ''),
                type: eventType,
                playerName,
                teamId: String(d.team?.id || ''),
                isScoring: Boolean(d.scoringPlay),
              };
            })
            .filter((x): x is NonNullable<typeof x> => Boolean(x))
            .slice(0, 12);

          matchMap.set(eventId, {
            id: eventId,
            league: feed.leagueName,
            leagueSlug: feed.slug,
            date: dateIso,
            kickoffLabel: formatKickoffLabel(dateIso),
            state,
            statusText,
            clock: String(ev.status?.displayClock || ''),
            completed: Boolean(ev.status?.type?.completed),
            venue,
            homeTeam: {
              id: String(home.team.id || ''),
              name: String(home.team.displayName || 'Home'),
              shortName: String(home.team.shortDisplayName || home.team.displayName || 'Home'),
              abbreviation: String(home.team.abbreviation || 'HOM'),
              logo: String(home.team.logo || ''),
              score: parseScore(home.score),
              winner: Boolean(home.winner),
              form: String(home.form || ''),
              record: String(home.records?.[0]?.summary || ''),
              color: String(home.team.color || '253141'),
            },
            awayTeam: {
              id: String(away.team.id || ''),
              name: String(away.team.displayName || 'Away'),
              shortName: String(away.team.shortDisplayName || away.team.displayName || 'Away'),
              abbreviation: String(away.team.abbreviation || 'AWY'),
              logo: String(away.team.logo || ''),
              score: parseScore(away.score),
              winner: Boolean(away.winner),
              form: String(away.form || ''),
              record: String(away.records?.[0]?.summary || ''),
              color: String(away.team.color || '253141'),
            },
            ...(keyEvents.length > 0 ? { keyEvents } : {}),
            ...(hasOdds
              ? {
                  odds: {
                    home: homeOdds,
                    draw: drawOdds,
                    away: awayOdds,
                  },
                }
              : {}),
          });
        }
      }

      const stateOrder: Record<'in' | 'pre' | 'post', number> = {
        in: 0,
        pre: 1,
        post: 2,
      };

      const matches = Array.from(matchMap.values()).sort((a, b) => {
        if (stateOrder[a.state] !== stateOrder[b.state]) {
          return stateOrder[a.state] - stateOrder[b.state];
        }
        const ta = new Date(a.date).getTime();
        const tb = new Date(b.date).getTime();
        return a.state === 'post' ? tb - ta : ta - tb;
      });

      const leagueCounts = new Map<string, { slug: string; name: string; count: number }>();
      for (const m of matches) {
        const existing = leagueCounts.get(m.leagueSlug);
        if (existing) {
          existing.count += 1;
        } else {
          leagueCounts.set(m.leagueSlug, {
            slug: m.leagueSlug,
            name: m.league,
            count: 1,
          });
        }
      }

      const payload = {
        updatedAt: new Date().toISOString(),
        serverTimeIso: new Date().toISOString(),
        day,
        league: leagueSlug,
        totalCount: matches.length,
        liveCount: matches.filter((m) => m.state === 'in').length,
        leagues: Array.from(leagueCounts.values()),
        matches,
      };

      liveScoreCache.set(cacheKey, {
        expiresAt: Date.now() + 15_000,
        payload,
      });

      res.json(payload);
    } catch (error) {
      console.error('Official LiveScore error:', error);
      res.status(502).json({
        error: 'Unable to reach Official LiveScore feed right now.',
      });
    }
  });

  // ---------------- REAL WORLD SOCCER PLAYERS & MATCH LINEUPS API ----------------

  app.get('/api/soccer/players', async (req: Request, res: Response) => {
    const rawLeague = String(req.query.league || 'all').trim();
    const rawTeamId = String(req.query.teamId || '').trim();
    const rawPos = String(req.query.position || 'ALL').trim().toUpperCase();
    const search = String(req.query.q || '').trim().toLowerCase();

    const activeLeagueMeta = WORLD_PLAYER_LEAGUES.find((l) => l.slug === rawLeague);
    const league = activeLeagueMeta ? activeLeagueMeta.slug : 'all';

    try {
      let teams: WorldTeamMeta[] = [];
      let players: WorldPlayerRecord[] = [];

      if (league === 'all') {
        const leagueTeamLists = await Promise.all(
          WORLD_PLAYER_LEAGUES.map((lg) => fetchLeagueTeamsCached(lg.slug, lg.name))
        );
        teams = leagueTeamLists.flat();

        if (rawTeamId) {
          const targetTeam = teams.find((t) => t.id === rawTeamId);
          if (targetTeam) {
            players = await fetchTeamRosterCached(targetTeam.leagueSlug, targetTeam);
          }
        } else {
          // Load top world clubs across all 6 global leagues
          const targetClubs: WorldTeamMeta[] = [];
          for (const lg of WORLD_PLAYER_LEAGUES) {
            const lgTeams = teams.filter((t) => t.leagueSlug === lg.slug);
            for (const fid of lg.featuredTeamIds) {
              const found = lgTeams.find((t) => t.id === fid);
              if (found) targetClubs.push(found);
            }
          }
          const rosters = await Promise.all(
            targetClubs.map((club) => fetchTeamRosterCached(club.leagueSlug, club))
          );
          players = rosters.flat();
        }
      } else if (activeLeagueMeta) {
        teams = await fetchLeagueTeamsCached(activeLeagueMeta.slug, activeLeagueMeta.name);
        if (rawTeamId) {
          const targetTeam = teams.find((t) => t.id === rawTeamId);
          if (targetTeam) {
            players = await fetchTeamRosterCached(activeLeagueMeta.slug, targetTeam);
          }
        } else {
          // If searching, load up to 10 teams in the league; otherwise load featured + top 6 teams
          const prioritized = [
            ...activeLeagueMeta.featuredTeamIds
              .map((id) => teams.find((t) => t.id === id))
              .filter((t): t is WorldTeamMeta => Boolean(t)),
            ...teams.filter((t) => !activeLeagueMeta.featuredTeamIds.includes(t.id)),
          ].slice(0, search ? 10 : 6);

          const rosters = await Promise.all(
            prioritized.map((club) => fetchTeamRosterCached(activeLeagueMeta.slug, club))
          );
          players = rosters.flat();
        }
      }

      if (rawPos === 'F' || rawPos === 'M' || rawPos === 'D' || rawPos === 'G') {
        players = players.filter((p) => p.positionAbbr === rawPos);
      }

      if (search) {
        players = players.filter((p) => {
          const hay = `${p.name} ${p.teamName} ${p.nationality} ${p.position} ${p.leagueName}`.toLowerCase();
          return hay.includes(search);
        });
      }

      players.sort((a, b) => {
        const scoreA = a.stats.goals * 5 + a.stats.assists * 3 + a.stats.appearances;
        const scoreB = b.stats.goals * 5 + b.stats.assists * 3 + b.stats.appearances;
        if (scoreB !== scoreA) return scoreB - scoreA;
        return a.name.localeCompare(b.name);
      });

      res.json({
        updatedAt: new Date().toISOString(),
        league,
        teamId: rawTeamId,
        leagues: [
          { slug: 'all', name: 'All World Leagues' },
          ...WORLD_PLAYER_LEAGUES.map((l) => ({ slug: l.slug, name: l.name })),
        ],
        teams,
        totalPlayers: players.length,
        players: players.slice(0, 120),
      });
    } catch (error) {
      console.error('World soccer players error:', error);
      res.status(502).json({
        error: 'Unable to reach official world soccer player database right now.',
      });
    }
  });

  app.get('/api/soccer/match/:eventId', async (req: Request, res: Response) => {
    const eventId = String(req.params.eventId || '').replace(/^ls-/, '').trim();
    const leagueSlug = String(req.query.league || 'all').trim() || 'all';
    const homeTeamId = String(req.query.homeTeamId || '').trim();
    const awayTeamId = String(req.query.awayTeamId || '').trim();
    const homeTeamName = String(req.query.homeTeamName || 'Home Team').trim();
    const awayTeamName = String(req.query.awayTeamName || 'Away Team').trim();
    const homeLogo = String(req.query.homeLogo || '').trim();
    const awayLogo = String(req.query.awayLogo || '').trim();

    if (!eventId) {
      res.status(400).json({ error: 'Match eventId is required.' });
      return;
    }

    const cacheKey = `${leagueSlug}:${eventId}`;
    const cached = matchSummaryCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      res.json(cached.payload);
      return;
    }

    try {
      const url = `https://site.api.espn.com/apis/site/v2/sports/soccer/${encodeURIComponent(
        leagueSlug
      )}/summary?event=${encodeURIComponent(eventId)}`;
      const resp = await fetch(url, {
        signal: AbortSignal.timeout(8000),
        headers: { Accept: 'application/json', 'User-Agent': 'Luckymate-Soccer/1.0' },
      });

      const sum = resp.ok
        ? ((await resp.json()) as {
            gameInfo?: { venue?: { fullName?: string; address?: { city?: string } } };
            header?: { league?: { name?: string } };
            rosters?: Array<{
              homeAway?: string;
              team?: { id?: string; displayName?: string; logos?: Array<{ href?: string }> };
              roster?: Array<{
                starter?: boolean;
                subbedIn?: boolean;
                subbedOut?: boolean;
                jersey?: string;
                athlete?: { id?: string; displayName?: string; shortName?: string };
                position?: { displayName?: string; abbreviation?: string };
                stats?: Array<{ name?: string; value?: number }>;
              }>;
            }>;
            keyEvents?: Array<{
              clock?: { displayValue?: string };
              type?: { text?: string };
              text?: string;
              shortText?: string;
              scoringPlay?: boolean;
              team?: { id?: string; displayName?: string };
              participants?: Array<{ athlete?: { displayName?: string } }>;
            }>;
          })
        : null;

      const parseRosterPlayers = (
        rosterArr?: Array<{
          starter?: boolean;
          subbedIn?: boolean;
          subbedOut?: boolean;
          jersey?: string;
          athlete?: { id?: string; displayName?: string; shortName?: string };
          position?: { displayName?: string; abbreviation?: string };
          stats?: Array<{ name?: string; value?: number }>;
        }>
      ) => {
        return (rosterArr || [])
          .filter((r) => Boolean(r.athlete?.displayName))
          .map((r) => {
            const statLookup = new Map<string, number>();
            for (const s of r.stats || []) {
              if (s.name && typeof s.value === 'number') statLookup.set(s.name, s.value);
            }
            return {
              id: String(r.athlete?.id || r.athlete?.displayName),
              name: String(r.athlete?.displayName),
              shortName: String(r.athlete?.shortName || r.athlete?.displayName),
              jersey: String(r.jersey || '-'),
              position: String(r.position?.abbreviation || r.position?.displayName || ''),
              starter: Boolean(r.starter),
              subbedIn: Boolean(r.subbedIn),
              subbedOut: Boolean(r.subbedOut),
              goals: statLookup.get('totalGoals') || 0,
              assists: statLookup.get('goalAssists') || 0,
              yellowCards: statLookup.get('yellowCards') || 0,
              redCards: statLookup.get('redCards') || 0,
              saves: statLookup.get('saves') || 0,
              shots: statLookup.get('totalShots') || 0,
            };
          });
      };

      const homeEntry = sum?.rosters?.find((r) => r.homeAway === 'home') || sum?.rosters?.[0];
      const awayEntry = sum?.rosters?.find((r) => r.homeAway === 'away') || sum?.rosters?.[1];

      let homePlayers = parseRosterPlayers(homeEntry?.roster);
      let awayPlayers = parseRosterPlayers(awayEntry?.roster);
      let sourceMode: 'match_lineups' | 'club_squads' = 'match_lineups';

      // Fallback to official club squad rosters when match hasn't kicked off yet
      if (homePlayers.length === 0 && awayPlayers.length === 0) {
        sourceMode = 'club_squads';
        const resolvedHomeId = String(homeEntry?.team?.id || homeTeamId);
        const resolvedAwayId = String(awayEntry?.team?.id || awayTeamId);
        const rosterLeague = leagueSlug === 'all' ? 'eng.1' : leagueSlug;

        const [hSquad, aSquad] = await Promise.all([
          resolvedHomeId
            ? fetchTeamRosterCached(rosterLeague, {
                id: resolvedHomeId,
                name: homeEntry?.team?.displayName || homeTeamName,
                shortName: homeTeamName,
                abbreviation: homeTeamName.slice(0, 3).toUpperCase(),
                logo: homeEntry?.team?.logos?.[0]?.href || homeLogo,
                color: '253141',
                leagueSlug: rosterLeague,
                leagueName: sum?.header?.league?.name || rosterLeague,
              })
            : Promise.resolve([]),
          resolvedAwayId
            ? fetchTeamRosterCached(rosterLeague, {
                id: resolvedAwayId,
                name: awayEntry?.team?.displayName || awayTeamName,
                shortName: awayTeamName,
                abbreviation: awayTeamName.slice(0, 3).toUpperCase(),
                logo: awayEntry?.team?.logos?.[0]?.href || awayLogo,
                color: '253141',
                leagueSlug: rosterLeague,
                leagueName: sum?.header?.league?.name || rosterLeague,
              })
            : Promise.resolve([]),
        ]);

        const mapSquad = (list: WorldPlayerRecord[]) =>
          list
            .slice()
            .sort((a, b) => b.stats.appearances - a.stats.appearances)
            .slice(0, 18)
            .map((p, idx) => ({
              id: p.id,
              name: p.name,
              shortName: p.shortName,
              jersey: p.jersey,
              position: p.positionAbbr,
              nationality: p.nationality,
              starter: idx < 11,
              subbedIn: false,
              subbedOut: false,
              goals: p.stats.goals,
              assists: p.stats.assists,
              yellowCards: p.stats.yellowCards,
              redCards: p.stats.redCards,
              saves: p.stats.saves,
              shots: p.stats.shots,
              appearances: p.stats.appearances,
            }));

        homePlayers = mapSquad(hSquad);
        awayPlayers = mapSquad(aSquad);
      }

      const keyEvents = (sum?.keyEvents || [])
        .filter((e) => Boolean(e.type?.text || e.text))
        .map((e) => ({
          minute: String(e.clock?.displayValue || ''),
          type: String(e.type?.text || 'Event'),
          text: String(e.text || e.shortText || e.type?.text || ''),
          teamId: String(e.team?.id || ''),
          teamName: String(e.team?.displayName || ''),
          playerName: String(e.participants?.[0]?.athlete?.displayName || ''),
          scoringPlay: Boolean(e.scoringPlay),
        }))
        .slice(0, 30);

      const venueFull = sum?.gameInfo?.venue?.fullName || '';
      const venueCity = sum?.gameInfo?.venue?.address?.city || '';
      const payload = {
        eventId,
        league: String(sum?.header?.league?.name || leagueSlug),
        venue: venueFull && venueCity ? `${venueFull}, ${venueCity}` : venueFull || venueCity,
        sourceMode,
        homeTeam: {
          id: String(homeEntry?.team?.id || homeTeamId),
          name: String(homeEntry?.team?.displayName || homeTeamName),
          logo: String(homeEntry?.team?.logos?.[0]?.href || homeLogo),
          players: homePlayers,
        },
        awayTeam: {
          id: String(awayEntry?.team?.id || awayTeamId),
          name: String(awayEntry?.team?.displayName || awayTeamName),
          logo: String(awayEntry?.team?.logos?.[0]?.href || awayLogo),
          players: awayPlayers,
        },
        keyEvents,
      };

      matchSummaryCache.set(cacheKey, {
        expiresAt: Date.now() + 25_000,
        payload,
      });

      res.json(payload);
    } catch (error) {
      console.error('Match summary details error:', error);
      res.status(502).json({
        error: 'Unable to fetch official match players right now.',
      });
    }
  });

  // ---------------- GEMINI AI ANALYSER API ----------------

  app.post('/api/analyze-match', async (req: Request, res: Response) => {
    const body = req.body ?? {};
    const homeTeam = String(body.homeTeam ?? '').trim();
    const awayTeam = String(body.awayTeam ?? '').trim();
    const league = String(body.league ?? 'Football Fixture').trim();
    const homeOdds = Number(body.homeOdds) || 2.1;
    const drawOdds = Number(body.drawOdds) || 3.4;
    const awayOdds = Number(body.awayOdds) || 3.2;

    if (!homeTeam || !awayTeam) {
      res.status(400).json({ error: 'Both homeTeam and awayTeam are required.' });
      return;
    }

    const apiKey = process.env.GEMINI_API_KEY;
    if (!apiKey) {
      res.status(503).json({
        error: 'Gemini API key is not configured in server environment secrets.',
      });
      return;
    }

    try {
      const ai = new GoogleGenAI({
        apiKey,
        httpOptions: {
          headers: {
            'User-Agent': 'aistudio-build',
          },
        },
      });

      const prompt = `Analyze this football matchup for a sports analytics dashboard:
Home Team: ${homeTeam}
Away Team: ${awayTeam}
Competition: ${league}
Sample Reference Odds (1 / X / 2): ${homeOdds.toFixed(2)} / ${drawOdds.toFixed(2)} / ${awayOdds.toFixed(2)}

Provide an objective breakdown covering:
1. A headline prediction call (e.g., "${homeTeam} to Win" or "Draw / Low-Scoring Edge")
2. A concise comparison of tactical profiles, recent scoring/conceding form, and head-to-head trends (under 65 words).
3. Estimated outcome probabilities (homeWin, draw, awayWin) as integers summing to 100.
4. Three crisp analytical key factors (each under 18 words).
5. Confidence percentage (integer 55-95) and confidence level ("High", "Moderate", or "Low"), plus a short risk note explaining match variance.`;

      const analysisConfig = {
        systemInstruction:
          'You are a careful football statistical analyst for a demonstration sports dashboard. Never promise guaranteed profits. Keep copy crisp, objective, and analytical.',
        thinkingConfig: { thinkingLevel: ThinkingLevel.LOW },
        responseMimeType: 'application/json',
        responseSchema: {
          type: Type.OBJECT,
          properties: {
            headlineCall: { type: Type.STRING },
            confidencePercent: { type: Type.INTEGER },
            formSummary: { type: Type.STRING },
            probabilities: {
              type: Type.OBJECT,
              properties: {
                homeWin: { type: Type.INTEGER },
                draw: { type: Type.INTEGER },
                awayWin: { type: Type.INTEGER },
              },
              required: ['homeWin', 'draw', 'awayWin'],
            },
            keyFactors: {
              type: Type.ARRAY,
              items: { type: Type.STRING },
            },
            confidenceLevel: { type: Type.STRING },
            riskNote: { type: Type.STRING },
          },
          required: [
            'headlineCall',
            'confidencePercent',
            'formSummary',
            'probabilities',
            'keyFactors',
            'confidenceLevel',
            'riskNote',
          ],
        },
      };

      let response;
      try {
        response = await ai.models.generateContent({
          model: 'gemini-4-hydrogen',
          contents: prompt,
          config: analysisConfig,
        });
      } catch {
        response = await ai.models.generateContent({
          model: 'gemini-3.1-flash-lite',
          contents: prompt,
          config: analysisConfig,
        });
      }

      const rawText = (response.text ?? '{}').trim();
      const parsed = JSON.parse(rawText);

      const h = Number(parsed?.probabilities?.homeWin) || 45;
      const d = Number(parsed?.probabilities?.draw) || 28;
      const a = Number(parsed?.probabilities?.awayWin) || 27;
      const total = h + d + a || 100;

      const normHome = Math.round((h / total) * 100);
      const normDraw = Math.round((d / total) * 100);
      const normAway = Math.max(0, 100 - normHome - normDraw);

      const rawConf = String(parsed?.confidenceLevel ?? 'Moderate');
      const confidenceLevel =
        rawConf === 'High' || rawConf === 'Low' || rawConf === 'Moderate' ? rawConf : 'Moderate';

      const confPct = Math.min(96, Math.max(52, Number(parsed?.confidencePercent) || 82));

      res.json({
        homeTeam,
        awayTeam,
        league,
        headlineCall: String(parsed.headlineCall || `${homeTeam} Slight Edge`),
        confidencePercent: confPct,
        formSummary: String(
          parsed.formSummary ||
            'Balanced tactical matchup with contrasting possession and transition styles.'
        ),
        probabilities: {
          homeWin: normHome,
          draw: normDraw,
          awayWin: normAway,
        },
        keyFactors: Array.isArray(parsed.keyFactors) ? parsed.keyFactors.slice(0, 3).map(String) : [],
        confidenceLevel,
        riskNote: String(
          parsed.riskNote ||
            'Statistical probabilities reflect historical form and tactical variance; no model guarantees an outcome.'
        ),
      });
    } catch (error) {
      console.error('Gemini match analysis error:', error);
      const message = error instanceof Error ? error.message : 'Unable to complete AI analysis.';
      res.status(502).json({
        error: `AI analysis unavailable: ${message}`,
      });
    }
  });

  function escapeHtmlAttr(value: string): string {
    return value
      .replace(/&/g, '&amp;')
      .replace(/"/g, '&quot;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;');
  }

  function injectLuckymateShareMeta(html: string, req: Request): string {
    const rawHost = req.get('x-forwarded-host') || req.get('host') || '';
    const proto = req.headers['x-forwarded-proto']
      ? String(req.headers['x-forwarded-proto']).split(',')[0].trim()
      : req.protocol || 'https';
    const configuredUrl = process.env.APP_URL?.trim()?.replace(/\/+$/, '');
    const origin = configuredUrl || (rawHost ? `${proto}://${rawHost}` : '');
    const ogImageUrl = origin ? `${origin}/luckymate-og.png?v=3` : '/luckymate-og.png?v=3';
    const refRaw = typeof req.query.ref === 'string' ? req.query.ref.trim().toUpperCase().replace(/[^A-Z0-9]/g, '') : '';
    const referrerAccountId = refRaw ? accountIdByReferralCode.get(refRaw) : undefined;
    const referrerAccount = referrerAccountId ? accountsById.get(referrerAccountId) : undefined;

    const pageTitle = refRaw
      ? referrerAccount
        ? `Join Luckymate – Invited by ${referrerAccount.username}`
        : 'Join Luckymate – Sportsbook, Aviator & Crash Games'
      : 'Luckymate – Live Sportsbook, Aviator & Crash Casino';

    const pageDesc = refRaw
      ? `Register on Luckymate with invite code ${refRaw}. Bet on live football, play Aviator & Crash games, and invite friends to earn $3 USD.`
      : 'Bet on live football matches, play Aviator & Crash games, and invite friends to earn $3 USD on Luckymate with instant mobile money wallets.';

    const canonicalUrl = origin
      ? `${origin}${req.originalUrl && req.originalUrl !== '/' ? req.originalUrl : '/'}`
      : '';

    let out = html
      .replace(/<title>[\s\S]*?<\/title>/i, `<title>${escapeHtmlAttr(pageTitle)}</title>`)
      .replace(
        /<meta\s+name="description"\s+content="[^"]*"\s*\/?>/i,
        `<meta name="description" content="${escapeHtmlAttr(pageDesc)}" />`
      )
      .replace(
        /<meta\s+property="og:title"\s+content="[^"]*"\s*\/?>/i,
        `<meta property="og:title" content="${escapeHtmlAttr(pageTitle)}" />`
      )
      .replace(
        /<meta\s+property="og:description"\s+content="[^"]*"\s*\/?>/i,
        `<meta property="og:description" content="${escapeHtmlAttr(pageDesc)}" />`
      )
      .replace(
        /<meta\s+property="og:image"\s+content="[^"]*"\s*\/?>/i,
        `<meta property="og:image" content="${escapeHtmlAttr(ogImageUrl)}" />`
      )
      .replace(
        /<meta\s+name="twitter:title"\s+content="[^"]*"\s*\/?>/i,
        `<meta name="twitter:title" content="${escapeHtmlAttr(pageTitle)}" />`
      )
      .replace(
        /<meta\s+name="twitter:description"\s+content="[^"]*"\s*\/?>/i,
        `<meta name="twitter:description" content="${escapeHtmlAttr(pageDesc)}" />`
      )
      .replace(
        /<meta\s+name="twitter:image"\s+content="[^"]*"\s*\/?>/i,
        `<meta name="twitter:image" content="${escapeHtmlAttr(ogImageUrl)}" />`
      );

    if (canonicalUrl) {
      const urlTags = `<meta property="og:url" content="${escapeHtmlAttr(canonicalUrl)}" />\n    <link rel="canonical" href="${escapeHtmlAttr(canonicalUrl)}" />\n  </head>`;
      out = out.replace(/<\/head>/i, urlTags);
    }

    return out;
  }

  app.all('/api/*', (_req: Request, res: Response) => {
    res.status(404).json({ error: 'API route not found.' });
  });

  app.get('/favicon.ico', (_req: Request, res: Response) => {
    const devFavicon = path.resolve(__dirname, 'public', 'favicon.svg');
    const prodFavicon = path.resolve(__dirname, 'dist', 'favicon.svg');
    const target = fs.existsSync(devFavicon) ? devFavicon : prodFavicon;
    if (fs.existsSync(target)) {
      res.setHeader('Content-Type', 'image/svg+xml');
      res.setHeader('Cache-Control', 'public, max-age=86400');
      res.sendFile(target);
      return;
    }
    res.status(204).end();
  });

  if (process.env.NODE_ENV !== 'production') {
    const { createServer: createViteServer } = await import('vite');
    const vite = await createViteServer({
      server: {
        middlewareMode: true,
        hmr: false,
        ws: false,
        watch: process.env.DISABLE_HMR === 'true' ? null : undefined,
      },
      appType: 'custom',
    });
    app.get('/@vite/client', (_req: Request, res: Response) => {
      res.setHeader('Content-Type', 'application/javascript; charset=utf-8');
      res.setHeader('Cache-Control', 'no-cache');
      res.end(`
const sheetsMap = new Map();
let lastInsertedStyle;
export function updateStyle(id, content) {
  let style = sheetsMap.get(id);
  if (!style) {
    style = document.createElement('style');
    style.setAttribute('type', 'text/css');
    style.setAttribute('data-vite-dev-id', id);
    style.textContent = content;
    if (!lastInsertedStyle) {
      document.head.appendChild(style);
      setTimeout(() => { lastInsertedStyle = undefined; }, 0);
    } else {
      lastInsertedStyle.insertAdjacentElement('afterend', style);
    }
    lastInsertedStyle = style;
  } else if (style.textContent !== content) {
    style.textContent = content;
  }
  sheetsMap.set(id, style);
}
export function removeStyle(id) {
  const style = sheetsMap.get(id);
  if (style) {
    style.remove();
    sheetsMap.delete(id);
  }
}
export function createHotContext() {
  return {
    data: {},
    accept() {},
    acceptDeps() {},
    acceptExports() {},
    dispose() {},
    prune() {},
    invalidate() {},
    on() {},
    off() {},
    send() {},
  };
}
export function injectQuery(url) {
  return url;
}
export class ErrorOverlay extends HTMLElement {}
`);
    });
    app.use(vite.middlewares);
    app.get(['/predictor', '/predictor/', '/predictor.html', '/predictor/*'], async (req: Request, res: Response, next) => {
      try {
        const rawHtml = fs.readFileSync(path.resolve(__dirname, 'predictor.html'), 'utf8');
        const transformed = await vite.transformIndexHtml('/predictor.html', rawHtml);
        res.status(200).setHeader('Content-Type', 'text/html; charset=utf-8').end(transformed);
      } catch (err) {
        vite.ssrFixStacktrace(err as Error);
        next(err);
      }
    });
    app.get('*', async (req: Request, res: Response, next) => {
      if (req.originalUrl.startsWith('/api') || req.originalUrl.startsWith('/ws')) {
        next();
        return;
      }
      try {
        const rawHtml = fs.readFileSync(path.resolve(__dirname, 'index.html'), 'utf8');
        const transformed = await vite.transformIndexHtml(req.originalUrl, rawHtml);
        const finalHtml = injectLuckymateShareMeta(transformed, req);
        res.status(200).setHeader('Content-Type', 'text/html; charset=utf-8').end(finalHtml);
      } catch (err) {
        vite.ssrFixStacktrace(err as Error);
        next(err);
      }
    });
  } else {
    const distPath = path.resolve(__dirname, 'dist');
    app.use(express.static(distPath, { index: false }));
    app.get(['/predictor', '/predictor/', '/predictor.html', '/predictor/*'], (_req: Request, res: Response) => {
      res.sendFile(path.join(distPath, 'predictor.html'));
    });
    app.get('*', (req: Request, res: Response) => {
      try {
        const rawHtml = fs.readFileSync(path.join(distPath, 'index.html'), 'utf8');
        const finalHtml = injectLuckymateShareMeta(rawHtml, req);
        res.status(200).setHeader('Content-Type', 'text/html; charset=utf-8').end(finalHtml);
      } catch {
        res.sendFile(path.join(distPath, 'index.html'));
      }
    });
  }

  const server = http.createServer(app);
  const wss = new WebSocketServer({ noServer: true });

  server.on('upgrade', (request, socket, head) => {
    const url = new URL(request.url || '/', `http://${request.headers.host || 'localhost'}`);
    const match = url.pathname.match(/^\/ws\/crash\/([a-z0-9-]+)$/);
    if (!match) {
      return;
    }

    const game = match[1] as CrashGameId;
    if (!CRASH_GAME_IDS.includes(game)) {
      socket.destroy();
      return;
    }

    wss.handleUpgrade(request, socket, head, (ws) => {
      const room = rooms[game];
      room.clients.add(ws);

      ws.send(
        JSON.stringify({
          type: 'init',
          ...buildRoomSnapshot(room),
        })
      );

      broadcastRoom(room, {
        type: 'presence',
        game: room.game,
        connectedPlayers: getRoomConnectedPlayers(room),
      });

      ws.on('close', () => {
        room.clients.delete(ws);
        broadcastRoom(room, {
          type: 'presence',
          game: room.game,
          connectedPlayers: getRoomConnectedPlayers(room),
        });
      });

      ws.on('error', () => {
        room.clients.delete(ws);
      });
    });
  });

  setInterval(tickCrashRooms, TICK_MS);

  server.listen(PORT, '0.0.0.0', () => {
    console.log(`Luckymate HTTP + WebSocket server running on http://0.0.0.0:${PORT}`);
  });
}

startServer();
