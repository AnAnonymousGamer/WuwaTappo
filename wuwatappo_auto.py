"""WuWaTappo background automation. Local CDP only; no system mouse input."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import base64
import ctypes
from ctypes import wintypes
import hashlib
import json
import logging
import math
import mmap
import os
from pathlib import Path
import socket
import shutil
import struct
import subprocess
import sys
import time
import urllib.request
import uuid
from urllib.parse import urlsplit, urlencode

ROOT = Path(__file__).resolve().parent
DATA = ROOT / 'debug'
STATUS = DATA / 'automation-status.json'
STOP = DATA / 'automation.stop'
LOG = ROOT / 'log' / 'automation.log'
MUTEX = 'Local\\WuWaTappoBackgroundAutomation'
POLICY_KEY = r'SOFTWARE\Policies\Microsoft\Edge\WebView2\AdditionalBrowserArguments'
POLICY_NAME = 'WuwaTappo.exe'
APP_IDS = {'cn': 'com.kuro.wuwatappo.cn', 'global': 'com.kuro.wuwatappo.global'}
CONFIG = ROOT / 'config.json'


QUIT_APP = r"""
(async () => {
  const urls = performance.getEntriesByType('resource').map(r => r.name)
    .filter(u => u.startsWith(location.origin + '/assets/') && /\.js(?:\?|$)/.test(u));
  for (const url of urls) {
    const source = await (await fetch(url)).text();
    const match = source.match(/["'](\.\/quitApp-[\w-]+\.js)["']/);
    if (match) {
      const module = await import(new URL(match[1], url).href);
      // App-owned exit flushes pending clicks before exiting.
      await module.quitApp();
      return true;
    }
  }
  throw new Error('App quit handler not found');
})()
"""


BOOTSTRAP = r"""
(async () => {
  if (window.__TAURI_INTERNALS__?.metadata?.currentWindow?.label !== 'main')
    throw new Error('Not the WuWaTappo main window');
  const previous = window.__wuwaBackground;
  if (previous?.version === 10) return previous.snapshot();
  const prior = previous?.snapshot() || {};
  if (prior.busy) throw new Error('Wait for the current chest operation before upgrading');
  previous?.disableAutoLogin?.();
  const urls = [...new Set([
    ...[...document.scripts].map(s => s.src),
    ...performance.getEntriesByType('resource').map(r => r.name)
  ])].filter(u => u.startsWith(location.origin + '/assets/') && /\.js(?:\?|$)/.test(u));
  let store, locked, coreSource, coreModule, coreUrl;
  for (const url of urls) {
    const source = await (await fetch(url)).text();
    const match = source.match(/\bglobalStore as ([\w$]+)/);
    if (!match) continue;
    const module = await import(url);
    store = module[match[1]];
    coreSource = source; coreModule = module; coreUrl = url;
    const lockExport = source.match(/\bisForceUpdateLocked as ([\w$]+)/);
    locked = lockExport ? module[lockExport[1]] : null;
    break;
  }
  if (!store || typeof store.incrementLocalClickCount !== 'function' || !locked)
    throw new Error('Unsupported app build: original click action not found');
  function exported(name) {
    const match = [...coreSource.matchAll(/\b([\w$]+) as ([\w$]+)/g)].find(m => m[1] === name);
    return match ? coreModule[match[2]] : undefined;
  }
  let restoreAuth = exported('bootstrapAuthIfInfoToken');
  let loginMethods = exported('loginMethods');
  // CN keeps its login service in a separate lazily imported module.
  if (!restoreAuth || !loginMethods) {
    for (const match of coreSource.matchAll(/["'](\.\/useLogin-[\w-]+\.js)["']/g)) {
      const module = await import(new URL(match[1], coreUrl).href);
      const namespace = Object.values(module).find(v => v &&
        typeof v.bootstrapAuthIfInfoToken === 'function' && v.loginMethods);
      if (namespace) {
        restoreAuth = namespace.bootstrapAuthIfInfoToken;
        loginMethods = namespace.loginMethods;
        break;
      }
    }
  }
  const getCookie = exported('getCookie');
  const domesticLogin = exported('Login');
  const isGlobal = exported('isGlobalApp') === true;
  const isDomestic = exported('isDomesticApp') === true;
  let added = prior.generated_clicks || 0, draws = prior.successful_draws || 0;
  let lastDrawAttempt = 0, busy = false;
  // Secrets leave this closure only through exportSession for local DPAPI storage.
  let session = null, binding = null, authPending = false, autoLogin = false, manualLogout = false;
  let queryPending = false, nextQuery = 0;
  let manualLogoutSawLoggedOut = false, accountMismatch = false;
  let authState = 'initializing', authAttempts = 0, authRecoveries = 0, authFailures = 0;
  let authError = null, nextAuth = Date.now() + 15000;
  let updatePending = false, updatePhase = 'idle', updatePercent = null;
  let updateError = null;
  let synthesisJob = null, synthesisNext = null, synthesisStopped = false;
  let synthesisTrigger = 0;
  let observedDrawAccount = store.isLoggedIn ? JSON.stringify(currentBinding()) : null;
  let observedDrawSpend = Number(store.userInfo?.total_click_consume || 0);
  let synthesisState = 'disabled', synthesisError = null;
  let synthesisCollection = [];
  let enhanced = prior.successful_enhance || 0, sameTier = prior.successful_same_tier || 0;
  const synthesisFns = Object.fromEntries(['getBagList', 'normalizeBagList', 'atlas',
    'normalizeAtlasList', 'normalizeBagRarity', 'compareBagRarityOrder',
    'sortBagAppearancesByRarityAndCollect', 'unwrapApiData', 'synthesisAtlas',
    'synthesisAtlasSame'].map(name => [name, exported(name)]));
  const itemEvents = [];
  const itemEventSession = String(Date.now()) + '-' + Math.random().toString(36).slice(2);
  let itemEventSequence = 0, itemLogPending = Promise.resolve(), itemLogError = null;
  let drawInventory = null, drawInventoryAccount = null;
  function rememberDrawInventory(items, account) {
    if (!store.isLoggedIn || account !== JSON.stringify(currentBinding())) return;
    drawInventory = items.map(item => ({asset_id:item.asset_id, asset_type:item.asset_type,
      asset_name:item.asset_name, quantity:item.quantity}));
    drawInventoryAccount = account;
  }
  function assetName(item) {
    return String(item.asset_name || '').trim().replace(/\.png$/i, '').toLowerCase();
  }
  function itemNovelty(reward, inventory) {
    if (!inventory) throw new Error('Pre-action inventory unavailable');
    const owned = inventory.some(item => Number(item.quantity) > 0 &&
      synthesisType(item) === synthesisType(reward) &&
      (Number(item.asset_id) === Number(reward.asset_id) ||
       (assetName(item) && assetName(item) === assetName(reward))));
    return owned ? 'dup' : 'new';
  }
  function logItem(item, catalog, quantity = 1) {
    const meta = catalog.find(e => Number(e.asset_id) === Number(item.asset_id)) ||
      catalog.find(e => synthesisType(e) === synthesisType(item) && assetName(e) && assetName(e) === assetName(item)) || {};
    const field = name => item[name] ?? meta[name] ?? null;
    const type = synthesisType(item) || synthesisType(meta), filename = field('asset_name');
    return {asset_id:field('asset_id'), asset_code:field('asset_code'),
      name:exported('resolveAssetDisplayName')?.(type, filename) || null,
      asset_name:filename, asset_type:type || null,
      rarity:item.rarity_type ?? field('rarity'), role_id:field('role_id'),
      series_name:field('series_name'), region_code:field('region_code'),
      star_level:field('star_level'), quantity};
  }
  function queueItemEvent(type, result, inventory, materials = [], catalog = []) {
    const event = {id:itemEventSession + ':' + (++itemEventSequence), time:Date.now(), type,
      novelty:itemNovelty(result, inventory)};
    // Serialize item events in response order; logItem whitelists public fields.
    itemLogPending = itemLogPending.then(async () => {
      let metadata = catalog;
      try {
        if (!metadata.length && typeof synthesisFns.atlas === 'function')
          metadata = synthesisFns.normalizeAtlasList(synthesisFns.unwrapApiData(await synthesisFns.atlas()));
      } catch { itemLogError = 'item_metadata_unavailable'; }
      const detail = {result:logItem(result, metadata)};
      if (materials.length) detail.materials = materials.map(item => logItem(item, metadata, item.quantity));
      itemEvents.push({...event, detail});
    }).catch(() => { itemLogError = 'item_event_unavailable'; });
  }
  async function getItemEvents() {
    await itemLogPending;
    return itemEvents.slice(0,100);
  }
  function ackItemEvents(ids) {
    const acknowledged = new Set(ids);
    for (let i=itemEvents.length-1; i>=0; i--) if (acknowledged.has(itemEvents[i].id)) itemEvents.splice(i,1);
  }
  function synthesisSupported(options) {
    return Object.entries(synthesisFns).every(([name, fn]) =>
      (!options.auto && !options.enhance && ['atlas','normalizeAtlasList','synthesisAtlas'].includes(name)) ||
      (!options.auto && !options.same_tier && name === 'synthesisAtlasSame') || typeof fn === 'function');
  }
  function synthesisAllowed() {
    return !synthesisStopped && store.isLoggedIn && !locked() && !updatePending &&
      !authPending && !manualLogout && !accountMismatch;
  }
  function observeDraw() {
    const account = store.isLoggedIn ? JSON.stringify(currentBinding()) : null;
    const spent = Number(store.userInfo?.total_click_consume || 0);
    if (account !== observedDrawAccount || spent < observedDrawSpend) {
      synthesisTrigger++; synthesisNext = null; synthesisState = 'waiting_draw';
    } else if (account !== null && Number.isFinite(spent) && spent > observedDrawSpend) {
      // The app updates this counter after a successful chest claim, including
      // manual claims. Initial historical totals never arm synthesis.
      synthesisTrigger++; synthesisNext = Date.now() + 30000;
      synthesisState = 'waiting_after_draw'; synthesisError = null;
    }
    observedDrawAccount = account; observedDrawSpend = spent;
  }
  function synthesisType(item) {
    return String(item.asset_type ?? '').trim().replace(/_atlas$/, '');
  }
  function synthesisGroups(items) {
    const f = synthesisFns;
    const groups = new Map(), seen = new Set();
    for (const item of items) {
      const rarity = f.normalizeBagRarity(item.rarity), type = synthesisType(item);
      if (!Number.isSafeInteger(item.asset_id) || item.asset_id <= 0 || seen.has(item.asset_id) ||
          !Number.isSafeInteger(item.quantity) || item.quantity < 1 || !rarity || !type)
        throw new Error('Unsupported inventory');
      seen.add(item.asset_id);
      const key = type + ':' + rarity;
      if (!groups.has(key)) groups.set(key, {type, rarity, items:[], usable:0});
      const group = groups.get(key);
      group.items.push(item); group.usable += item.quantity - 1;
    }
    return [...groups.values()];
  }
  function synthesisMaterials(group, required) {
    const ids = [];
    for (const item of synthesisFns.sortBagAppearancesByRarityAndCollect(group.items)) {
      const count = Math.min(item.quantity - 1, required - ids.length);
      for (let i=0; i<count; i++) ids.push(item.asset_id);
      if (ids.length === required) break;
    }
    return ids.length === required ? ids : null;
  }
  function collectionProgress(items, catalog) {
    const f = synthesisFns, types = new Map();
    // The client's atlas matches normalized asset_name first, then asset_id.
    // asset_code can be shared by different skins; it is not an ownership key.
    const names = new Set(), ids = new Set();
    for (const item of items) {
      const prefix = synthesisType(item) + ':' + f.normalizeBagRarity(item.rarity) + ':';
      if (assetName(item)) names.add(prefix + assetName(item));
      ids.add(prefix + item.asset_id);
    }
    for (const entry of catalog) {
      const type = synthesisType(entry), rarity = f.normalizeBagRarity(entry.rarity);
      const name = assetName(entry), id = entry.asset_id;
      if (!type || !rarity || (!name && (!Number.isSafeInteger(id) || id <= 0)))
        throw new Error('Unsupported atlas');
      if (!types.has(type)) types.set(type, new Map());
      const tiers = types.get(type);
      if (!tiers.has(rarity)) tiers.set(rarity, new Map());
      const prefix = type + ':' + rarity + ':';
      const owned = (name && names.has(prefix + name)) || (id > 0 && ids.has(prefix + id));
      const identity = name ? 'name:' + name : 'id:' + id;
      tiers.get(rarity).set(identity, !!owned || tiers.get(rarity).get(identity) === true);
    }
    return [...types].map(([type, tiers]) => {
      const progress = [...tiers].sort(([a],[b]) => f.compareBagRarityOrder(a,b)).map(([rarity, entries]) => {
        const owned = [...entries.values()].filter(Boolean).length;
        return {rarity, total:entries.size, owned, complete:owned === entries.size};
      });
      return {type, complete:progress.every(t => t.complete), tiers:progress};
    });
  }
  function synthesisPlan(items, catalog, options) {
    const groups = synthesisGroups(items), f = synthesisFns;
    const typeOrder = [...new Set(catalog.length ? catalog.map(synthesisType) : groups.map(g => g.type))];
    synthesisCollection = options.auto ? collectionProgress(items, catalog) : [];
    const candidates = [];
    for (const group of groups) {
      let mode = options.same_tier ? 'same_tier' : 'enhance';
      if (options.auto) {
        const collection = synthesisCollection.find(c => c.type === group.type);
        const index = collection?.tiers.findIndex(t => t.rarity === group.rarity) ?? -1;
        if (index < 0) throw new Error('Inventory tier missing from atlas');
        if (collection.complete) continue;
        const higherComplete = collection.tiers.slice(0,index).every(t => t.complete);
        if (higherComplete) {
          if (collection.tiers[index].complete) continue;
          mode = 'same_tier';
        }
      } else if (options.enhance && !catalog.some(entry =>
          synthesisType(entry) === group.type &&
          f.compareBagRarityOrder(entry.rarity, group.rarity) < 0)) continue;
      const required = mode === 'enhance' ? 10 : 5;
      if (group.usable >= required) candidates.push({group, mode, required});
    }
    // Prefer upgrades, then the latest atlas's category order and client tier order.
    candidates.sort((a,b) => Number(a.mode === 'same_tier') - Number(b.mode === 'same_tier') ||
      typeOrder.indexOf(a.group.type) - typeOrder.indexOf(b.group.type) ||
      f.compareBagRarityOrder(b.group.rarity, a.group.rarity));
    const chosen = candidates[0];
    return chosen ? {mode:chosen.mode, ids:synthesisMaterials(chosen.group, chosen.required)} : null;
  }
  function beginSynthesis(options) {
    if (!options.auto && !options.enhance && !options.same_tier) {
      synthesisNext = null; synthesisState = 'disabled'; return;
    }
    if (!synthesisSupported(options)) { synthesisState = 'unsupported_app'; return; }
    if (synthesisNext === null) {
      if (synthesisState === 'disabled') synthesisState = 'waiting_draw';
      return;
    }
    if (busy || !synthesisAllowed() || Date.now() < synthesisNext) return;
    busy = true; synthesisState = 'checking'; synthesisError = null;
    const account = JSON.stringify(currentBinding());
    const trigger = synthesisTrigger;
    synthesisJob = (async () => {
      try {
        const f = synthesisFns;
        const items = f.normalizeBagList(f.unwrapApiData(await f.getBagList()));
        let catalog = [];
        if (options.enhance || options.auto) {
          catalog = f.normalizeAtlasList(f.unwrapApiData(await f.atlas()));
          if (!catalog.length) throw new Error('Atlas unavailable');
        }
        observeDraw();
        // A new draw during the read requests restarts the full 30-second wait.
        if (trigger !== synthesisTrigger || !synthesisAllowed() || account !== JSON.stringify(currentBinding())) return;
        const plan = synthesisPlan(items, catalog, options);
        if (!plan) {
          synthesisState = options.auto && synthesisCollection.every(c => c.complete) ? 'collection_complete' : 'waiting_materials';
          synthesisNext = null; return;
        }
        const {ids, mode} = plan;
        // Re-check after the read requests; never spend after logout, update, or stop.
        if (!synthesisAllowed() || account !== JSON.stringify(currentBinding())) return;
        synthesisState = mode;
        const materials = [...new Set(ids)].map(id => ({...items.find(item => item.asset_id === id), quantity:ids.filter(value => value === id).length}));
        const result = f.unwrapApiData(await (mode === 'enhance' ? f.synthesisAtlas(ids) : f.synthesisAtlasSame(ids)));
        queueItemEvent(mode === 'enhance' ? 'ten2one' : 'five2one', result, items, materials, catalog);
        if (mode === 'enhance') enhanced++; else sameTier++;
        observeDraw();
        if (trigger === synthesisTrigger) {
          synthesisState = 'ready'; synthesisNext = Date.now() + 30000;
        }
        const panel = document.querySelectorAll('.synthesis-panel')[0]?.__vueParentComponent;
        if (panel?.type?.__name === 'MainPanelExchangeTab') panel.emit('synthesis-success');
      } catch (error) {
        observeDraw();
        if (trigger === synthesisTrigger) {
          synthesisState = 'waiting_draw'; synthesisNext = null;
        }
        synthesisError = Number.isFinite(Number(error?.code)) ? Number(error.code) : 'request_failed';
      } finally { busy = false; synthesisJob = null; }
    })();
  }
  async function stopAutomation() {
    synthesisStopped = true;
    synthesisNext = null;
    if (synthesisJob) await synthesisJob;
    await itemLogPending;
    disableAutoLogin();
  }
  function currentBinding() {
    const u = store.userInfo;
    if (!u?.cuid || !Number.isSafeInteger(Number(u.player_id)) || Number(u.player_id) <= 0 || !u.server_id) return null;
    return {cuid:String(u.cuid), playerId:Number(u.player_id), serverId:String(u.server_id)};
  }
  function configureAuth(enabled, record = null) {
    autoLogin = !!enabled;
    if (!enabled) { session = null; binding = null; authState = 'disabled'; return; }
    const current = store.isLoggedIn ? currentBinding() : null;
    binding = current || record?.binding || binding;
    if (record?.session && binding && record.session.info?.cuid === binding.cuid &&
        record.session.playerId === binding.playerId && record.session.serverId === binding.serverId)
      session = record.session;
    if (authState === 'disabled' || authState === 'waiting_user') nextAuth = Date.now();
  }
  function matchesSession(saved) {
    return String(store.userInfo?.cuid) === saved.info.cuid &&
      Number(store.userInfo?.player_id) === saved.playerId &&
      String(store.userInfo?.server_id) === saved.serverId;
  }
  function rememberSession() {
    if (!store.isLoggedIn || !autoLogin || authPending) return;
    binding = currentBinding() || binding;
    authState = 'ready'; authFailures = 0; authError = null;
    const user = store.userInfo;
    try {
      const sdk = JSON.parse(localStorage.getItem('__KrSDK_USER_INFO__') || 'null');
      const query = store.sdkPlayerQuery;
      // Keep the in-memory session after the app clears its SDK storage on
      // expiry. Never keep it if the user has switched account or role.
      if ((!sdk || !query) && session && matchesSession(session)) return;
      if (!sdk || !query || String(sdk.cuid) !== String(user.cuid) ||
          String(query.cuid) !== String(user.cuid)) { session = null; return; }
      const playerId = Number(user.player_id), serverId = String(user.server_id || '');
      const channelId = Number(query.channelId);
      if (!Number.isSafeInteger(playerId) || playerId <= 0 || !serverId ||
          query.channelId == null || !Number.isFinite(channelId)) { session = null; return; }
      // Exact current role only; never choose the first role in the SDK list.
      if (!(query.items || []).some(item => Number(item.playerId) === playerId &&
          String(item.serverId) === serverId)) { session = null; return; }
      if (isGlobal && typeof loginMethods?.handleForeignLogin === 'function') {
        const accessToken = sdk.access_token || localStorage.getItem('__KrSDK_USER_TOKEN__');
        if (!accessToken) { session = null; return; }
        session = {kind:'global', playerId, serverId, query,
          info:{cuid:String(sdk.cuid), puid:String(sdk.puid || sdk.cuid), channelId,
                userId:String(sdk.userId || sdk.userName || sdk.cuid),
                userName:String(sdk.userName || sdk.userId || ''), accessToken}};
      } else if (isDomestic && typeof domesticLogin === 'function' &&
                 typeof loginMethods?.afterLogin === 'function' && sdk.sdk_openid != null) {
        const accessToken = sdk.token || localStorage.getItem('__KrSDK_USER_TOKEN__');
        if (!accessToken) { session = null; return; }
        session = {kind:'cn', playerId, serverId, query,
          info:{cuid:String(sdk.cuid), puid:String(sdk.sdk_openid), channelId,
                userId:String(sdk.sdk_openid), userName:String(sdk.username || ''), accessToken}};
      } else session = null;
    } catch { session = null; }
  }
  // Respect a deliberate logout. Observe the app's existing request without
  // changing its URL, headers, body, response, or dispatching a new request.
  let originalOpen, observedOpen;
  const chestObservers = new WeakMap();
  if (typeof XMLHttpRequest !== 'undefined') {
    originalOpen = XMLHttpRequest.prototype.open;
    observedOpen = function(...args) {
      const previous = chestObservers.get(this);
      if (previous) { this.removeEventListener('load', previous); chestObservers.delete(this); }
      const result = originalOpen.apply(this, args);
      try {
        const path = new URL(String(args[1]), location.href).pathname;
        const requestAccount = JSON.stringify(currentBinding());
        const inventoryBefore = drawInventoryAccount === requestAccount ? drawInventory : null;
        if (path === '/api/frontend/user/logout') {
          manualLogout = true; manualLogoutSawLoggedOut = false;
          session = null; authState = 'manual_logout';
        }
        if (['/api/frontend/chests/open','/api/frontend/bags/list'].includes(path) && typeof this.addEventListener === 'function') {
          const observe = () => {
            chestObservers.delete(this);
            try {
              if (this.status < 200 || this.status >= 300) return;
              const envelope = this.responseType === 'json' ? this.response : JSON.parse(this.responseText);
              if (!exported('isApiSuccess')?.(Number(envelope?.code))) return;
              const data = envelope.data ?? envelope.result;
              if (path === '/api/frontend/bags/list') {
                rememberDrawInventory(synthesisFns.normalizeBagList(data), requestAccount);
              } else if (data && Number(data.asset_id) > 0) {
                queueItemEvent('draw', data, inventoryBefore);
              }
            } catch { itemLogError = 'draw_inventory_or_result_unavailable'; }
          };
          chestObservers.set(this, observe);
          this.addEventListener('load', observe, {once:true});
        }
      } catch {}
      return result;
    };
    XMLHttpRequest.prototype.open = observedOpen;
  }
  function retryAuth(error) {
    const code = Number(error?.code);
    authError = Number.isFinite(code) ? code : 'request_failed';
    authFailures++;
    if (code === 10002 || code === 10003) {
      session = null; authState = 'waiting_user'; nextAuth = Infinity;
    } else {
      authState = 'retry_wait'; nextAuth = Date.now() + Math.min(300000, 30000 * 2 ** Math.min(4, authFailures - 1));
    }
  }
  async function recoverAuth() {
    authPending = true; authState = 'recovering'; authAttempts++;
    try {
      if (typeof getCookie === 'function' && getCookie('infoToken') && typeof restoreAuth === 'function') {
        await restoreAuth({emitLoginSuccess:true});
        if (store.isLoggedIn) {
          if (session && !matchesSession(session)) {
            accountMismatch = true; autoLogin = false; session = null; authState = 'account_mismatch'; return;
          }
          authRecoveries++; authState = 'ready'; return;
        }
        if (getCookie('infoToken')) throw new Error('Session restore temporarily unavailable');
      }
      if (!session) { authState = 'waiting_user'; nextAuth = Infinity; return; }
      const saved = session;
      if (manualLogout || !autoLogin) return;
      if (saved.kind === 'global') {
        await loginMethods.handleForeignLogin(saved.info, saved.playerId, saved.serverId);
      } else {
        const i = saved.info;
        const response = await domesticLogin(i.cuid, i.puid, i.channelId, i.userId,
          i.userName, i.accessToken, 'sdk', saved.playerId, saved.serverId, 1);
        await loginMethods.afterLogin(response);
      }
      if (!store.isLoggedIn) throw new Error('Login did not restore the account');
      if (!matchesSession(saved)) {
        accountMismatch = true; autoLogin = false; session = null; authState = 'account_mismatch'; return;
      }
      // The normal logout handler cleared this non-secret role query state.
      store.setSdkPlayerQuery(saved.query);
      authRecoveries++; authState = 'ready'; authFailures = 0; authError = null;
    } catch (error) { retryAuth(error); }
    finally { authPending = false; }
  }
  function maintainAuth(enabled) {
    if (accountMismatch) { authState = 'account_mismatch'; return; }
    autoLogin = enabled;
    if (!enabled) { session = null; authState = 'disabled'; return; }
    if (authPending) return;
    if (authState === 'role_selection_required' && !store.isLoggedIn) return;
    if (manualLogout) {
      if (!store.isLoggedIn) manualLogoutSawLoggedOut = true;
      if (!store.isLoggedIn || !manualLogoutSawLoggedOut) { authState = 'manual_logout'; return; }
      manualLogout = false; manualLogoutSawLoggedOut = false;
    }
    if (store.isLoggedIn) {
      rememberSession(); nextAuth = 0;
      // Cookie-based boot restores userInfo but does not restore the role query.
      if (!session && isGlobal && !store.sdkPlayerQuery && !queryPending && Date.now() >= nextQuery &&
          typeof loginMethods?.prepareForeignCharacterSwitch === 'function') {
        queryPending = true; nextQuery = Date.now() + 300000;
        Promise.resolve(loginMethods.prepareForeignCharacterSwitch()).then(() => {
          if (autoLogin) rememberSession();
          exported('useForeignRoleSelectDialog')?.().closeForeignRoleSelectDialog({clearPending:true});
        }).catch(() => {}).finally(() => {queryPending = false;});
      }
      return;
    }
    if (Date.now() >= nextAuth) void recoverAuth();
  }
  function snapshot() {
    return {
      logged_in: !!store.isLoggedIn,
      update_locked: !!locked(),
      available_clicks: Number(store.totalClickCount),
      cumulative_clicks: Number(store.cumulativeClickCount),
      local_clicks: Number(store.localClickCount),
      generated_clicks: added,
      successful_draws: draws,
      auto_login: autoLogin,
      login_state: authState,
      login_attempts: authAttempts,
      login_recoveries: authRecoveries,
      login_cached_session: !!session,
      login_error_code: authError,
      password_login_supported: isGlobal && typeof loginMethods?.prepareForeignCharacterSwitch === 'function',
      update_phase: updatePhase,
      update_percent: updatePercent,
      update_error: updateError,
      synthesis_state: synthesisState,
      synthesis_error: synthesisError,
      synthesis_collection: synthesisCollection,
      synthesis_due_in: synthesisNext === null ? null : Math.max(0, Math.ceil((synthesisNext - Date.now()) / 1000)),
      item_log_error: itemLogError,
      successful_enhance: enhanced,
      successful_same_tier: sameTier,
      cooldowns: [...document.querySelectorAll('.reward-countdown__text')].map(e => e.textContent.trim()),
      ready_chests: [...document.querySelectorAll('button.reward-btn')].filter(e => !e.disabled).length,
      busy
    };
  }
  function originalHandler(element) {
    // Vue's event invoker is keyed by Symbol('_vei') in this installed build.
    for (const key of Reflect.ownKeys(element)) {
      if (String(key) !== '_vei' && String(key) !== 'Symbol(_vei)') continue;
      const events = element[key];
      const value = events?.onClick?.value;
      if (typeof value === 'function') return value;
    }
    return null;
  }
  async function tick(count, autoDraw, recoverLogin = true, synthesis = {}) {
    if ([synthesis.enhance, synthesis.same_tier, synthesis.auto].filter(Boolean).length > 1)
      throw new Error('Synthesis modes are mutually exclusive');
    if (synthesisStopped) return snapshot();
    if (observedOpen && XMLHttpRequest.prototype.open === originalOpen)
      XMLHttpRequest.prototype.open = observedOpen;
    observeDraw();
    if (locked() || updatePending || busy) return snapshot();
    maintainAuth(recoverLogin);
    if (!store.isLoggedIn || authPending || authState === 'account_mismatch' || authState === 'manual_logout') return snapshot();
    if (!Number.isInteger(count) || count < 0 || count > 20)
      throw new Error('Invalid click batch');
    for (let i = 0; i < count; i++) {
      store.incrementLocalClickCount();
      added++;
    }
    // Let Vue update button readiness before invoking its handler.
    await Promise.resolve();
    if (autoDraw && !busy && store.totalClickCount >= 1000 && Date.now() - lastDrawAttempt > 15000) {
      const button = [...document.querySelectorAll('button.reward-btn')].find(e => !e.disabled);
      if (button) {
        const handler = originalHandler(button);
        if (!handler) throw new Error('Original reward handler not found; no fallback click is used');
        lastDrawAttempt = Date.now();
        busy = true;
        const spentBefore = Number(store.userInfo?.total_click_consume || 0);
        try {
          const drawAccount = JSON.stringify(currentBinding());
          rememberDrawInventory(synthesisFns.normalizeBagList(synthesisFns.unwrapApiData(await synthesisFns.getBagList())), drawAccount);
          if (!store.isLoggedIn || locked() || synthesisStopped || drawAccount !== JSON.stringify(currentBinding())) return snapshot();
          // Satisfy Vue's stop modifier without dispatching an event.
          await handler({stopPropagation() {}});
          if (Number(store.userInfo?.total_click_consume || 0) > spentBefore) draws++;
        } finally { observeDraw(); busy = false; }
      }
    }
    beginSynthesis(synthesis);
    return snapshot();
  }
  function disableAutoLogin() {
    autoLogin = false; session = null; authState = 'disabled';
    if (observedOpen && XMLHttpRequest.prototype.open === observedOpen)
      XMLHttpRequest.prototype.open = originalOpen;
  }
  function exportSession() {
    return autoLogin && !manualLogout && !accountMismatch && binding ? {binding, session} : null;
  }
  function beginPasswordLogin(sdk) {
    if (!autoLogin || manualLogout || accountMismatch || authPending || store.isLoggedIn || locked()) return false;
    if (!isGlobal || typeof loginMethods?.prepareForeignCharacterSwitch !== 'function') return false;
    if (binding && binding.cuid !== String(sdk.cuid)) {
      accountMismatch = true; authState = 'account_mismatch'; return false;
    }
    authPending = true; authState = 'recovering'; authAttempts++;
    (async () => {
      try {
        localStorage.setItem('__KrSDK_USER_INFO__', JSON.stringify(sdk));
        localStorage.setItem('__KrSDK_USER_TOKEN__', sdk.access_token);
        if (!await loginMethods.prepareForeignCharacterSwitch()) throw new Error('Role query failed');
        if (!autoLogin || manualLogout) return;
        const query = store.sdkPlayerQuery;
        if (!query || String(query.cuid) !== String(sdk.cuid)) throw new Error('Account query mismatch');
        const roles = query.items || [];
        const role = binding ? roles.find(r => Number(r.playerId) === binding.playerId && String(r.serverId) === binding.serverId)
                             : roles.length === 1 ? roles[0] : null;
        if (!role) { authState = 'role_selection_required'; return; }
        const info = {cuid:String(sdk.cuid),puid:String(sdk.puid),userId:String(sdk.userId),
          userName:String(sdk.userName),accessToken:sdk.access_token,channelId:Number(query.channelId)};
        if (!Number.isFinite(info.channelId)) throw new Error('Channel unavailable');
        await loginMethods.handleForeignLogin(info,Number(role.playerId),String(role.serverId));
        const selected = currentBinding();
        if (!store.isLoggedIn || !selected || selected.cuid !== info.cuid ||
            selected.playerId !== Number(role.playerId) || selected.serverId !== String(role.serverId)) {
          accountMismatch = true; authState = 'account_mismatch'; return;
        }
        binding = selected;
        session = {kind:'global',info,query,playerId:selected.playerId,serverId:selected.serverId};
        authRecoveries++; authFailures = 0; authError = null; authState = 'ready';
      } catch (error) { retryAuth(error); }
      finally {
        authPending = false;
        exported('useForeignRoleSelectDialog')?.().closeForeignRoleSelectDialog({clearPending:true});
        exported('dispatchLoginOverlayOpen')?.(false);
      }
    })();
    return true;
  }
  function beginUpdate() {
    if (!locked() || updatePending || busy || authPending) return false;
    const install = exported('requestAppUpdateInstall');
    if (typeof install !== 'function') throw new Error('Official updater unavailable');
    updatePending = true; updatePhase = 'requested'; updateError = null;
    Promise.resolve().then(() => install(progress => {
      updatePhase = ['downloading','installing'].includes(progress.phase) ? progress.phase : 'requested';
      updatePercent = Number.isFinite(progress.percent) ? progress.percent : null;
    })).then(() => {updatePhase = 'restarting';}).catch(() => {
      updateError = 'official_update_failed'; updatePhase = 'failed'; updatePending = false;
    });
    return true;
  }
  window.__wuwaBackground = {version:10, snapshot, tick, disableAutoLogin, stopAutomation,
    configureAuth, exportSession, beginPasswordLogin, beginUpdate, getItemEvents, ackItemEvents};
  return snapshot();
})()
"""


def login_config(path=None):
    """Read only at runtime. Never return configuration through logs/status/CLI."""
    try:
        value = json.loads((path or CONFIG).read_text(encoding='utf-8-sig'))
        if not isinstance(value, dict):
            return None
        username, password = value.get('username'), value.get('password')
        if not isinstance(username, str) or not username.strip():
            return None
        if not isinstance(password, str) or not password.strip():
            return None
        return {'username': username.strip(), 'password': password}
    except (OSError, ValueError, UnicodeError):
        return None


def credential_key(credentials):
    if not credentials:
        return None
    return hashlib.sha256(json.dumps(credentials, sort_keys=True).encode()).hexdigest()


def protect_session(data, decrypt=False):
    """DPAPI current-user scope, with no UI or machine-wide key."""
    class Blob(ctypes.Structure):
        _fields_ = [('size', wintypes.DWORD), ('data', ctypes.POINTER(ctypes.c_ubyte))]
    buffer = ctypes.create_string_buffer(data)
    source = Blob(len(data), ctypes.cast(buffer, ctypes.POINTER(ctypes.c_ubyte)))
    result = Blob()
    crypt = ctypes.WinDLL('crypt32', use_last_error=True)
    func = crypt.CryptUnprotectData if decrypt else crypt.CryptProtectData
    func.argtypes = [ctypes.POINTER(Blob), ctypes.c_void_p, ctypes.c_void_p,
                     ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(Blob)]
    if not func(ctypes.byref(source), None, None, None, None, 1, ctypes.byref(result)):
        raise RuntimeError('Session encryption unavailable')
    try:
        return ctypes.string_at(result.data, result.size)
    finally:
        kernel = ctypes.WinDLL('kernel32', use_last_error=True)
        kernel.LocalFree.argtypes = [ctypes.c_void_p]
        kernel.LocalFree(result.data)


def load_session(cn, key):
    if not key:
        return None
    try:
        target = DATA / ('session-cn.bin' if cn else 'session-global.bin')
        record = json.loads(protect_session(target.read_bytes(), True))
        if isinstance(record, dict) and record.get('key') == key and record.get('cn') is cn:
            return record.get('session')
    except (OSError, ValueError, RuntimeError):
        pass
    return None


def save_session(cn, key, session):
    target = DATA / ('session-cn.bin' if cn else 'session-global.bin')
    if not key or not session:
        target.unlink(missing_ok=True)
        return
    record = json.dumps({'key': key, 'cn': cn, 'session': session}).encode()
    tmp = target.with_suffix('.tmp')
    tmp.write_bytes(protect_session(record))
    tmp.replace(target)


class LoginRequired(RuntimeError):
    def __init__(self, code):
        self.code = code
        super().__init__('Interactive login required')


def login_device_id():
    path = DATA / 'login-device-id.txt'
    try:
        return str(uuid.UUID(path.read_text(encoding='ascii').strip()))
    except (OSError, ValueError):
        value = str(uuid.uuid4())
        path.write_text(value, encoding='ascii')
        return value


def sdk_password_login(credentials, opener=None):
    """Official global H5 SDK email-password and authorization-code exchange.

    Credentials are sent only to the HTTPS KURO SDK endpoint. Redirects are
    refused so neither passwords nor authorization codes can change origin.
    Human verification/invalid credentials stop retries; no CAPTCHA bypass.
    """
    class NoRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, req, fp, code, msg, headers, newurl):
            return None
    opener = opener or urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())
    # Public application identifiers from the official desktop-pet login page.
    common = dict(redirect_uri='1', __e__='1', pack_mark='1', platform='h5',
                  version='2.3.0', sdkVersion='2.3.0', deviceNum=login_device_id(),
                  projectId='G153', productId='A1823', client_id='7rxmydkibzzsf12om5asjnoo',
                  channelId='173', response_type='code')
    def post(endpoint, values):
        request = urllib.request.Request('https://sdkapi.kurogame-service.com/sdkcom' + endpoint,
            data=urlencode({**common, **values}).encode(), headers={
                'Content-Type': 'application/x-www-form-urlencoded', 'Kr-Ver': '2.3.0',
                'Accept-Language': 'en', 'Origin': 'https://sdk-prod-cdn-aws.kurogame-service.com',
                'User-Agent': 'Mozilla/5.0'})
        with opener.open(request, timeout=12) as response:
            result = json.load(response)
        if not isinstance(result, dict) or not isinstance(result.get('code'), int):
            raise RuntimeError('Unexpected SDK response')
        if result['code'] != 0:
            raise LoginRequired(result['code'])
        data = result.get('data')
        if not isinstance(data, dict):
            raise RuntimeError('Unexpected SDK data')
        return data
    try:
        encoded = list(base64.b64encode(credentials['password'].encode('latin-1')).decode())
    except UnicodeError:
        raise LoginRequired('unsupported_password_encoding') from None
    for offset in (0, 1):
        for index in range(offset, len(encoded) - 2, 4):
            encoded[index], encoded[index + 2] = encoded[index + 2], encoded[index]
    account = post('/v2/login/emailPwd.lg', {'email': credentials['username'], 'password': ''.join(encoded)})
    if account.get('realNameUrl') or not account.get('code') or not account.get('cuid'):
        raise LoginRequired('verification_required')
    token = post('/v2/auth/getToken.lg', {'code': account['code'],
        'grant_type': 'authorization_code', 'client_secret': '32gh5r0p35ullmxrzzwk40ly'})
    if not token.get('access_token'):
        raise RuntimeError('SDK did not return a session')
    return {'access_token': token['access_token'], 'cuid': str(account['cuid']),
            'puid': str(account['id']), 'userId': str(account['sdkuserid']),
            'userName': str(account.get('username', ''))}


def write_status(**values):
    values['updated_at'] = time.strftime('%Y-%m-%d %H:%M:%S')
    values['pid'] = os.getpid()
    values['elevated'] = bool(ctypes.windll.shell32.IsUserAnAdmin())
    tmp = STATUS.with_suffix('.tmp')
    tmp.write_text(json.dumps(values, ensure_ascii=False, indent=2), encoding='utf-8')
    tmp.replace(STATUS)


class ItemLogHandler(logging.FileHandler):
    def handleError(self, record):
        raise  # Keep the event pending until its line is actually written.


def configure_logging():
    handler = ItemLogHandler(LOG, mode='a', encoding='utf-8')
    handler.setFormatter(logging.Formatter('%(message)s'))
    logger = logging.getLogger('wuwatappo.items')
    for previous in logger.handlers[:]:
        logger.removeHandler(previous)
        previous.close()
    logger.setLevel(logging.INFO)
    logger.propagate = False
    logger.addHandler(handler)


def write_item_events(client, written):
    events = client.evaluate('window.__wuwaBackground.getItemEvents()')
    acknowledged = []
    for event in events:
        event_id = event['id']
        if event_id not in written:
            kind = event['type']
            novelty = event['novelty']
            if kind not in ('draw', 'ten2one', 'five2one') or novelty not in ('new', 'dup'):
                raise ValueError('Invalid item event type')
            timestamp = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(event['time'] / 1000))
            detail = json.dumps(event['detail'], ensure_ascii=False, separators=(',', ':'))
            logging.getLogger('wuwatappo.items').info('%s %-3s %-8s %s', timestamp, novelty, kind, detail)
            written.add(event_id)
        acknowledged.append(event_id)
    if acknowledged:
        client.evaluate('window.__wuwaBackground.ackItemEvents(' + json.dumps(acknowledged) + ')')


def close_handle(handle):
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel.CloseHandle(handle)


def worker_running():
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.OpenMutexW.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.LPCWSTR]
    kernel.OpenMutexW.restype = wintypes.HANDLE
    handle = kernel.OpenMutexW(0x100000, False, MUTEX)
    if handle:
        close_handle(handle)
        return True
    error = ctypes.get_last_error()
    if error not in (0, 2):
        raise ctypes.WinError(error)
    return False


def acquire_mutex(name=MUTEX):
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.CreateMutexW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
    kernel.CreateMutexW.restype = wintypes.HANDLE
    handle = kernel.CreateMutexW(None, False, name)
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())
    if ctypes.get_last_error() == 183:
        kernel.CloseHandle.argtypes = [wintypes.HANDLE]
        kernel.CloseHandle(handle)
        raise RuntimeError('Another automation worker is already running')
    return handle


def debug_flags(port):
    return (f'--remote-debugging-port={port} --remote-debugging-address=127.0.0.1 '
            '--no-proxy-server')


@contextmanager
def temporary_debug_policy(port):
    """Restore the exact per-app registry value, even if startup fails."""
    import winreg
    backup_path = DATA / 'debug-policy-backup.json'
    with winreg.CreateKeyEx(winreg.HKEY_LOCAL_MACHINE, POLICY_KEY, 0,
                           winreg.KEY_READ | winreg.KEY_WRITE) as key:
        # Recover an interrupted previous startup before making a new backup.
        def restore(record):
            if record['exists']:
                winreg.SetValueEx(key, POLICY_NAME, 0, record['kind'], record['value'])
            else:
                try:
                    winreg.DeleteValue(key, POLICY_NAME)
                except FileNotFoundError:
                    pass
        if backup_path.exists():
            previous = json.loads(backup_path.read_text(encoding='utf-8'))
            if not previous.get('restored', False):
                restore(previous)
        try:
            value, kind = winreg.QueryValueEx(key, POLICY_NAME)
            if kind not in (winreg.REG_SZ, winreg.REG_EXPAND_SZ):
                raise RuntimeError('Unexpected existing WebView2 policy type')
            record = dict(exists=True, value=value, kind=kind, restored=False)
        except FileNotFoundError:
            record = dict(exists=False, value=None, kind=None, restored=False)
        backup_path.write_text(json.dumps(record), encoding='utf-8')
        try:
            winreg.SetValueEx(key, POLICY_NAME, 0, winreg.REG_SZ, debug_flags(port))
            yield
        finally:
            restore(record)
            try:
                actual = winreg.QueryValueEx(key, POLICY_NAME)
            except FileNotFoundError:
                actual = None
            expected = (record['value'], record['kind']) if record['exists'] else None
            if actual != expected:
                raise RuntimeError('Registry restoration verification failed')
            record['restored'] = True
            backup_path.write_text(json.dumps(record), encoding='utf-8')


def app_processes(executable):
    """Only return processes with the exact selected executable path."""
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    class Entry(ctypes.Structure):
        _fields_ = [('size', wintypes.DWORD), ('usage', wintypes.DWORD),
                    ('pid', wintypes.DWORD), ('heap', ctypes.c_size_t),
                    ('module', wintypes.DWORD), ('threads', wintypes.DWORD),
                    ('parent', wintypes.DWORD), ('priority', wintypes.LONG),
                    ('flags', wintypes.DWORD), ('exe', wintypes.WCHAR * 260)]
    kernel.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
    kernel.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
    kernel.Process32FirstW.argtypes = kernel.Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(Entry)]
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD,
                                               wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
    snapshot = kernel.CreateToolhelp32Snapshot(2, 0)
    if snapshot == ctypes.c_void_p(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    result = []
    expected = os.path.normcase(str(executable.resolve()))
    try:
        entry = Entry(); entry.size = ctypes.sizeof(entry)
        more = kernel.Process32FirstW(snapshot, ctypes.byref(entry))
        while more:
            if entry.exe.lower() == executable.name.lower():
                handle = kernel.OpenProcess(0x1000, False, entry.pid)
                if not handle:
                    raise ctypes.WinError(ctypes.get_last_error())
                try:
                    buf = ctypes.create_unicode_buffer(32768); size = wintypes.DWORD(len(buf))
                    if not kernel.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                        raise ctypes.WinError(ctypes.get_last_error())
                    if os.path.normcase(str(Path(buf.value).resolve())) == expected:
                        result.append(entry.pid)
                finally:
                    close_handle(handle)
            more = kernel.Process32NextW(snapshot, ctypes.byref(entry))
    finally:
        close_handle(snapshot)
    return result


def terminate_app(executable):
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    kernel.TerminateProcess.argtypes = [wintypes.HANDLE, wintypes.UINT]
    kernel.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    for pid in app_processes(executable):
        handle = kernel.OpenProcess(0x100001, False, pid)
        if not handle:
            raise ctypes.WinError(ctypes.get_last_error())
        try:
            if not kernel.TerminateProcess(handle, 0):
                raise ctypes.WinError(ctypes.get_last_error())
            if kernel.WaitForSingleObject(handle, 10000) != 0:
                raise RuntimeError('WuWaTappo did not exit')
        finally:
            close_handle(handle)


def process_is_elevated(pid):
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    advapi = ctypes.WinDLL('advapi32', use_last_error=True)
    kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel.OpenProcess.restype = wintypes.HANDLE
    advapi.OpenProcessToken.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.POINTER(wintypes.HANDLE)]
    advapi.GetTokenInformation.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p,
                                         wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
    process = kernel.OpenProcess(0x1000, False, pid)
    if not process:
        raise ctypes.WinError(ctypes.get_last_error())
    token = wintypes.HANDLE()
    try:
        if not advapi.OpenProcessToken(process, 8, ctypes.byref(token)):
            raise ctypes.WinError(ctypes.get_last_error())
        elevated, size = wintypes.DWORD(), wintypes.DWORD()
        if not advapi.GetTokenInformation(token, 20, ctypes.byref(elevated), ctypes.sizeof(elevated), ctypes.byref(size)):
            raise ctypes.WinError(ctypes.get_last_error())
        return bool(elevated.value)
    finally:
        if token:
            close_handle(token)
        close_handle(process)


def app_identity(executable):
    with executable.open('rb') as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as data:
        for identifier in APP_IDS.values():
            if data.find((identifier + 'index.html').encode()) >= 0:
                return identifier
    raise RuntimeError(f'Cannot identify the application variant: {executable}')


def install_candidates(cn=False):
    import winreg
    folder = 'WuwaTappo' if cn else 'WuwaTappoGlobal'
    candidates = []
    for root in (os.environ.get('ProgramFiles', r'C:\Program Files'),
                 os.environ.get('ProgramFiles(x86)', r'C:\Program Files (x86)'),
                 str(Path(os.environ.get('LOCALAPPDATA', '')) / 'Programs')):
        candidates.append(Path(root) / folder / 'WuwaTappo.exe')
    for hive in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
        try:
            with winreg.OpenKey(hive, 'Software\\kuro\\' + folder) as key:
                for name in ('', 'InstallLocation', 'InstallDir'):
                    try:
                        value, _ = winreg.QueryValueEx(key, name)
                        if isinstance(value, str) and value:
                            path = Path(value)
                            candidates.append(path if path.suffix.lower() == '.exe' else path / 'WuwaTappo.exe')
                    except FileNotFoundError:
                        pass
        except OSError:
            pass
    return list(dict.fromkeys(candidates))


def locate_app(value=None, cn=False):
    candidates = [Path(value)] if value else install_candidates(cn)
    found = []
    for path in candidates:
        if path.is_file() and path.name.lower() == 'wuwatappo.exe':
            identifier = app_identity(path)
            if identifier != (APP_IDS['cn'] if cn else APP_IDS['global']):
                continue
            found.append(path.resolve())
    if not found:
        raise RuntimeError(f'No matching {"CN" if cn else "Global"} WuwaTappo.exe found; install that variant or specify its path with --exe')
    if len(found) > 1:
        raise RuntimeError('Multiple installations of the selected variant found; specify the application path with --exe')
    return found[0]


def connection_ready(port, expected_identifier=None):
    client = None
    try:
        client = find_main(port, expected_identifier)
        client.evaluate(BOOTSTRAP)
        return True
    except (OSError, RuntimeError, ValueError):
        return False
    finally:
        if client:
            client.close()


def ensure_port_free(port):
    # A closed local endpoint can time out under host firewall rules. Binding
    # checks actual ownership without interpreting a timeout as occupancy.
    with socket.socket() as probe:
        if hasattr(socket, 'SO_EXCLUSIVEADDRUSE'):
            probe.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        try:
            probe.bind(('127.0.0.1', port))
        except OSError as error:
            raise RuntimeError(f'Local port {port} is already in use') from error


def read_status():
    try:
        value = json.loads(STATUS.read_text(encoding='utf-8'))
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError):
        return {}


def active_port():
    port = read_status().get('port')
    if type(port) is not int or not 1 <= port <= 65535:
        raise RuntimeError(f'No debug connection available; run {command_hint("start", sys.stderr)} first')
    return port


def available_port():
    with socket.socket() as probe:
        probe.bind(('127.0.0.1', 0))
        return probe.getsockname()[1]


def command_arguments(args, command):
    result = [str(Path(__file__).resolve()), command,
              '--frequency', str(args.frequency), '--duration', str(args.duration)]
    for name, flag in [('cn', '--cn'), ('enhance', '--enhance'), ('same_tier', '--same-tier'), ('auto', '--auto')]:
        if getattr(args, name):
            result.append(flag)
    if args.exe:
        result += ['--exe', str(args.exe)]
    return result


def setup_app(args):
    executable = locate_app(args.exe, args.cn)
    identifier = app_identity(executable)
    if connection_ready(args.port, identifier):
        return
    ensure_port_free(args.port)
    cache = Path(os.environ['APPDATA']) / identifier
    backup = DATA / 'backup-before-automation' / identifier / time.strftime('%Y%m%d-%H%M%S')
    backup.mkdir(parents=True, exist_ok=True)
    for path in cache.glob('*.dat'):
        shutil.copy2(path, backup / path.name)
    with temporary_debug_policy(args.port):
        terminate_app(executable)
        # Give the old WebView browser time to release its user-data directory.
        time.sleep(2)
        subprocess.Popen([str(executable)], cwd=executable.parent)
        deadline = time.monotonic() + 45
        while time.monotonic() < deadline:
            if connection_ready(args.port, identifier):
                return
            time.sleep(0.5)
        raise RuntimeError('WuWaTappo debug connection timed out; the temporary configuration has been restored')


def elevate(args):
    """Re-run the same documented command with the approved admin token."""
    command = command_arguments(args, args.command)
    class ShellInfo(ctypes.Structure):
        _fields_ = [('cbSize', wintypes.DWORD), ('fMask', wintypes.ULONG),
                    ('hwnd', wintypes.HWND), ('lpVerb', wintypes.LPCWSTR),
                    ('lpFile', wintypes.LPCWSTR), ('lpParameters', wintypes.LPCWSTR),
                    ('lpDirectory', wintypes.LPCWSTR), ('nShow', ctypes.c_int),
                    ('hInstApp', wintypes.HINSTANCE), ('lpIDList', ctypes.c_void_p),
                    ('lpClass', wintypes.LPCWSTR), ('hkeyClass', wintypes.HKEY),
                    ('dwHotKey', wintypes.DWORD), ('hIcon', wintypes.HANDLE),
                    ('hProcess', wintypes.HANDLE)]
    info = ShellInfo(); info.cbSize = ctypes.sizeof(info); info.fMask = 0x40
    info.lpVerb = 'runas'; info.lpFile = sys.executable
    info.lpParameters = subprocess.list2cmdline(command)
    info.lpDirectory = str(ROOT); info.nShow = 1 if args.command == 'run' else 0
    shell = ctypes.WinDLL('shell32', use_last_error=True)
    shell.ShellExecuteExW.argtypes = [ctypes.POINTER(ShellInfo)]
    if not shell.ShellExecuteExW(ctypes.byref(info)):
        raise ctypes.WinError(ctypes.get_last_error())
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    kernel.GetExitCodeProcess.argtypes = [wintypes.HANDLE, ctypes.POINTER(wintypes.DWORD)]
    try:
        while kernel.WaitForSingleObject(info.hProcess, 200) == 258:
            pass
        code = wintypes.DWORD()
        if not kernel.GetExitCodeProcess(info.hProcess, ctypes.byref(code)) or code.value:
            raise RuntimeError(f'The administrator command did not complete; run {command_hint("status", sys.stderr)} for details')
        print(f'Command completed; run {command_hint("status")} to check the current state.')
    finally:
        close_handle(info.hProcess)


def ensure_connection(args):
    executable = locate_app(args.exe, args.cn)
    args.exe = str(executable)
    identifier = app_identity(executable)
    if connection_ready(args.port, identifier) and ctypes.windll.shell32.IsUserAnAdmin():
        # The app, not Python, starts its native updater. Both must hold the
        # approved admin token or the installer could request UAC again.
        if any(not process_is_elevated(pid) for pid in app_processes(executable)):
            client = find_main(args.port, identifier)
            try:
                client.evaluate(QUIT_APP)
            except (OSError, RuntimeError, ValueError):
                pass
            finally:
                client.close()
            deadline = time.monotonic() + 10
            while app_processes(executable) and time.monotonic() < deadline:
                time.sleep(.2)
            if app_processes(executable):
                raise RuntimeError('WuWaTappo has not finished saving and exiting; an elevated restart has been deferred')
    if not connection_ready(args.port, identifier):
        try:
            ensure_port_free(args.port)
        except RuntimeError:
            args.port = available_port()
        print('Starting the WuWaTappo debug connection; approve the Windows administrator prompt if shown.', flush=True)
        setup_app(args)
    if not connection_ready(args.port, identifier):
        raise RuntimeError('Failed to establish a WuWaTappo connection')


def stop_all(args):
    STOP.touch()
    deadline = time.monotonic() + 40
    while worker_running() and time.monotonic() < deadline:
        time.sleep(0.2)
    if worker_running():
        raise RuntimeError(f'Automation is finishing the current request; retry {command_hint("stop", sys.stderr)} shortly. WuWaTappo is still open')
    executable = locate_app(args.exe, args.cn)
    client = None
    try:
        client = find_main(args.port, app_identity(executable))
        client.evaluate(QUIT_APP)
    except (OSError, RuntimeError, ValueError):
        pass  # Exit commonly closes CDP before sending the final response.
    finally:
        if client:
            client.close()
    deadline = time.monotonic() + 5
    while app_processes(executable) and time.monotonic() < deadline:
        time.sleep(0.2)
    if app_processes(executable):
        terminate_app(executable)
    if app_processes(executable):
        raise RuntimeError('WuWaTappo has not exited yet')
    write_status(state='stopped', app_running=False, port=args.port, executable=str(executable))
    print('Automation and WuWaTappo have both stopped.')


def find_main(port=None, expected_identifier=None):
    for target in targets(port):
        if target.get('type') != 'page':
            continue
        u = urlsplit(target.get('url', ''))
        if u.hostname != 'tauri.localhost':
            continue
        client = CDP(target['webSocketDebuggerUrl'])
        try:
            label = client.evaluate('window.__TAURI_INTERNALS__?.metadata?.currentWindow?.label')
            if label == 'main':
                identifier = client.evaluate("window.__TAURI_INTERNALS__.invoke('plugin:app|identifier')")
                if identifier in APP_IDS.values() and (not expected_identifier or identifier == expected_identifier):
                    return client
        except Exception:
            client.close()
            raise
        client.close()
    raise RuntimeError('WuWaTappo main WebView is not available')


def targets(port=None):
    if port is None:
        port = active_port()
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    with opener.open(f"http://127.0.0.1:{port}/json/list", timeout=3) as response:
        return json.load(response)


class CDP:
    """Small synchronous RFC6455/CDP client; never uses environment proxies."""

    def __init__(self, url):
        u = urlsplit(url)
        if u.scheme != "ws" or u.hostname not in ("127.0.0.1", "localhost"):
            raise ValueError("Only local WebView debugging connections are allowed")
        self.sock = socket.create_connection((u.hostname, u.port), timeout=15)
        self.seq = 0
        self.buffer = b""
        key = base64.b64encode(os.urandom(16)).decode()
        request = (f"GET {u.path} HTTP/1.1\r\nHost: {u.netloc}\r\n"
                   f"Upgrade: websocket\r\nConnection: Upgrade\r\n"
                   f"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n\r\n")
        self.sock.sendall(request.encode())
        while b"\r\n\r\n" not in self.buffer:
            chunk = self.sock.recv(4096)
            if not chunk:
                raise ConnectionError("WebSocket handshake closed")
            self.buffer += chunk
        header, self.buffer = self.buffer.split(b"\r\n\r\n", 1)
        expected = base64.b64encode(hashlib.sha1(
            (key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode()).digest())
        if b" 101 " not in header.split(b"\r\n")[0] or expected not in header:
            self.close()
            raise ConnectionError("Invalid WebSocket handshake")

    def close(self):
        self.sock.close()

    def _read(self, count):
        while len(self.buffer) < count:
            chunk = self.sock.recv(max(4096, count - len(self.buffer)))
            if not chunk:
                raise ConnectionError("WebView connection closed")
            self.buffer += chunk
        data, self.buffer = self.buffer[:count], self.buffer[count:]
        return data

    def _send(self, data, opcode=1):
        mask = os.urandom(4)
        length = len(data)
        head = bytes([0x80 | opcode])
        if length < 126:
            head += bytes([0x80 | length])
        elif length < 65536:
            head += b"\xfe" + struct.pack("!H", length)
        else:
            head += b"\xff" + struct.pack("!Q", length)
        payload = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
        self.sock.sendall(head + mask + payload)

    def _message(self):
        parts = []
        while True:
            a, b = self._read(2)
            length = b & 127
            if length == 126:
                length = struct.unpack("!H", self._read(2))[0]
            elif length == 127:
                length = struct.unpack("!Q", self._read(8))[0]
            if length > 32 * 1024 * 1024:
                raise ValueError("Oversized WebSocket frame")
            mask = self._read(4) if b & 128 else None
            data = self._read(length)
            if mask:
                data = bytes(x ^ mask[i % 4] for i, x in enumerate(data))
            opcode = a & 15
            if opcode == 8:
                raise ConnectionError("WebView closed WebSocket")
            if opcode == 9:
                self._send(data, 10)
                continue
            if opcode == 10:
                continue
            parts.append(data)
            if a & 128:
                return json.loads(b"".join(parts))

    def call(self, method, **params):
        self.seq += 1
        self._send(json.dumps({"id": self.seq, "method": method, "params": params}).encode())
        while True:
            reply = self._message()
            if reply.get("id") == self.seq:
                if "error" in reply:
                    raise RuntimeError(reply["error"])
                return reply.get("result", {})

    def evaluate(self, expression):
        result = self.call("Runtime.evaluate", expression=expression,
                           returnByValue=True, awaitPromise=True)
        if "exceptionDetails" in result:
            raise RuntimeError(result["exceptionDetails"].get("exception", {}).get(
                "description", str(result["exceptionDetails"])))
        return result.get("result", {}).get("value")


def file_version(path):
    library = ctypes.WinDLL('version', use_last_error=True)
    library.GetFileVersionInfoSizeW.argtypes = [wintypes.LPCWSTR, ctypes.c_void_p]
    library.GetFileVersionInfoW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p]
    library.VerQueryValueW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR, ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(wintypes.UINT)]
    size = library.GetFileVersionInfoSizeW(str(path), None)
    if not size:
        return None
    data = ctypes.create_string_buffer(size)
    if not library.GetFileVersionInfoW(str(path), 0, size, data):
        return None
    pointer, length = ctypes.c_void_p(), wintypes.UINT()
    if not library.VerQueryValueW(data, '\\', ctypes.byref(pointer), ctypes.byref(length)) or length.value < 16:
        return None
    _, _, high, low = struct.unpack('<4I', ctypes.string_at(pointer, 16))
    return '.'.join(str(x) for x in (high >> 16, high & 65535, low >> 16, low & 65535))


def installer_running():
    """Observe only; never terminate an installer while it is writing files."""
    class Entry(ctypes.Structure):
        _fields_ = [('size', wintypes.DWORD), ('usage', wintypes.DWORD), ('pid', wintypes.DWORD),
                    ('heap', ctypes.c_size_t), ('module', wintypes.DWORD), ('threads', wintypes.DWORD),
                    ('parent', wintypes.DWORD), ('priority', wintypes.LONG),
                    ('flags', wintypes.DWORD), ('exe', wintypes.WCHAR * 260)]
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
    kernel.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
    kernel.Process32FirstW.argtypes = kernel.Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(Entry)]
    snapshot = kernel.CreateToolhelp32Snapshot(2, 0)
    if snapshot == ctypes.c_void_p(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        entry = Entry(); entry.size = ctypes.sizeof(entry)
        more = kernel.Process32FirstW(snapshot, ctypes.byref(entry))
        while more:
            name = entry.exe.casefold()
            if 'wuwatappo' in name and ('setup' in name or 'installer' in name):
                return True
            more = kernel.Process32NextW(snapshot, ctypes.byref(entry))
    finally:
        close_handle(snapshot)
    return False


class UpdateGuard:
    def __init__(self, executable, clock=time.time):
        self.executable, self.clock = executable, clock
        self.path = DATA / 'update-state.json'
        self.record = None
        self.next_attempt = 0
        try:
            value = json.loads(self.path.read_text(encoding='utf-8'))
            if (isinstance(value, dict) and value.get('executable') == executable and value.get('active') and
                    isinstance(value.get('started'), (int, float)) and math.isfinite(value['started'])):
                self.record = value
        except (OSError, ValueError):
            pass

    def begin(self):
        self.record = dict(active=True, executable=self.executable,
                           version=file_version(self.executable), started=self.clock())
        self.persist()

    def persist(self):
        tmp = self.path.with_suffix('.tmp')
        tmp.write_text(json.dumps(self.record), encoding='utf-8')
        tmp.replace(self.path)

    def finish(self, result):
        if self.record:
            self.record.update(active=False, result=result, finished=self.clock())
            self.persist()
        self.record = None
        self.next_attempt = self.clock() + 300

    def waiting(self, installing):
        if installing:
            return 'update_needs_attention' if self.record and self.clock() - self.record['started'] > 900 else 'updating'
        if self.record and self.clock() - self.record['started'] < 30:
            return 'restarting_after_update'
        return None

    def connected(self, snapshot):
        if not self.record:
            return
        if not snapshot['update_locked'] and file_version(self.executable) != self.record['version']:
            self.finish('updated_and_reconnected')
        elif snapshot.get('update_phase') == 'failed':
            self.finish('official_update_failed')
        elif self.clock() - self.record['started'] > 900:
            self.finish('update_timeout')
        elif snapshot.get('update_phase') == 'idle' and self.clock() - self.record['started'] > 30:
            self.finish('restarted_without_update')


def run_worker(args, mutex=None):
    if not ctypes.windll.shell32.IsUserAnAdmin():
        raise RuntimeError(f'Use {command_hint("start", sys.stderr)} or {command_hint("run", sys.stderr)} to retain the administrator privileges required for updates')
    configure_logging()
    mutex = mutex or acquire_mutex()
    executable = str(locate_app(args.exe, args.cn))
    identifier = app_identity(Path(executable))
    STOP.unlink(missing_ok=True)
    client = None
    started = time.monotonic()
    last_report = 0.0
    failures = 0
    current = {}
    written_events = set()
    credentials, key = None, None
    config_checked = 0.0
    session_digest = None
    session_checked = 0.0
    password_retry = 0.0
    password_failures = 0
    password_state = 'disabled'
    recovery_after = 0.0
    guard = UpdateGuard(executable)
    try:
        write_status(state='connecting', frequency=args.frequency, port=args.port, executable=executable)
        while not STOP.exists():
            if args.duration and time.monotonic() - started >= args.duration:
                break
            try:
                if time.monotonic() - config_checked >= 5:
                    updated_credentials = login_config()
                    updated_key = credential_key(updated_credentials)
                    if updated_key != key:
                        credentials, key = updated_credentials, updated_key
                        password_retry = 0.0; password_failures = 0
                        password_state = 'ready' if credentials else 'disabled'
                        session_digest = None
                        if client:
                            saved = load_session(args.cn, key)
                            client.evaluate('window.__wuwaBackground.configureAuth(' +
                                            json.dumps(bool(credentials)) + ',' + json.dumps(saved) + ')')
                    config_checked = time.monotonic()
                if client is None:
                    client = find_main(args.port, identifier)
                    current = client.evaluate(BOOTSTRAP)
                    client.evaluate('window.__wuwaBackground.configureAuth(' +
                                    json.dumps(bool(credentials)) + ',' + json.dumps(load_session(args.cn, key)) + ')')
                before = time.monotonic()
                current = client.evaluate(
                    f'window.__wuwaBackground.tick(1, true, '
                    f'{str(bool(credentials)).lower()}, {json.dumps(dict(enhance=args.enhance, same_tier=args.same_tier, auto=args.auto))})')
                write_item_events(client, written_events)
                failures = 0
                guard.connected(current)
                if current['update_locked'] and not guard.record and time.time() >= guard.next_attempt:
                    if client.evaluate('window.__wuwaBackground.beginUpdate()'):
                        guard.begin()
                if credentials and time.monotonic() - session_checked >= 10:
                    session = client.evaluate('window.__wuwaBackground.exportSession()')
                    digest = hashlib.sha256(json.dumps(session, sort_keys=True).encode()).digest()
                    if digest != session_digest:
                        save_session(args.cn, key, session)
                        session_digest = digest
                    session_checked = time.monotonic()
                if (credentials and not current['logged_in'] and not current['update_locked'] and
                        current.get('login_state') == 'waiting_user' and time.monotonic() >= password_retry):
                    if args.cn or not current.get('password_login_supported'):
                        password_state = 'unsupported_app'; password_retry = float('inf')
                    else:
                        write_status(state='recovering_login', port=args.port, executable=executable,
                                     password_login_state='authenticating', **current)
                        try:
                            sdk = sdk_password_login(credentials)
                            # A removed/changed config or stop request cancels the pending result.
                            if not STOP.exists() and credential_key(login_config()) == key:
                                accepted = client.evaluate('window.__wuwaBackground.beginPasswordLogin(' + json.dumps(sdk) + ')')
                                password_state = 'restoring_role' if accepted else 'cancelled'
                            sdk = None
                            password_retry = time.monotonic() + 60
                            password_failures = 0
                        except LoginRequired as error:
                            password_state = 'manual_verification_required' if error.code in (41000, 71001, 'verification_required') else 'credentials_rejected'
                            password_retry = float('inf')
                        except (OSError, RuntimeError, ValueError, KeyError):
                            password_failures += 1
                            password_state = 'network_retry'
                            password_retry = time.monotonic() + min(300, 30 * 2 ** min(4, password_failures - 1))
                if current['logged_in'] and current.get('login_state') == 'ready':
                    password_state = 'ready' if credentials else 'disabled'
                    password_retry = 0.0; password_failures = 0
                elif current.get('login_state') == 'role_selection_required':
                    password_state = 'role_selection_required'
                state = ('updating' if guard.record else
                         'recovering_login' if current.get('login_state') == 'recovering' else
                         'waiting_login' if not current['logged_in'] or current.get('login_state') == 'manual_logout' else
                         'paused_account_mismatch' if current.get('login_state') == 'account_mismatch' else
                         'waiting_update' if current['update_locked'] else 'running')
                if time.monotonic() - last_report >= 5:
                    write_status(state=state, frequency=args.frequency, port=args.port, executable=executable,
                                 password_login_state=password_state, **current)
                    last_report = time.monotonic()
                wait_until = before + 1.0 / args.frequency
                while not STOP.exists() and time.monotonic() < wait_until:
                    time.sleep(min(0.1, max(0, wait_until - time.monotonic())))
            except (OSError, ValueError, RuntimeError) as exc:
                if client is not None:
                    client.close()
                    client = None
                failures += 1
                write_status(state='waiting_connection', error=type(exc).__name__,
                             retry=failures, port=args.port, executable=executable, **current)
                waiting = guard.waiting(installer_running())
                if waiting:
                    write_status(state=waiting, port=args.port, executable=executable)
                elif time.monotonic() >= recovery_after and failures >= 2:
                    recovery_after = time.monotonic() + 60
                    try:
                        ensure_connection(args)
                    except (OSError, RuntimeError, ValueError) as recovery_error:
                        write_status(state='waiting_connection', port=args.port, executable=executable,
                                     restart_error=type(recovery_error).__name__, **current)
                for _ in range(min(300, 20 * failures)):
                    if STOP.exists():
                        break
                    time.sleep(0.1)
    except KeyboardInterrupt:
        pass
    finally:
        if client:
            try:
                if credentials:
                    save_session(args.cn, key, client.evaluate('window.__wuwaBackground.exportSession()'))
                client.evaluate('window.__wuwaBackground?.stopAutomation?.()')
                write_item_events(client, written_events)
            except (OSError, RuntimeError, ValueError):
                pass
            client.close()
        try:
            write_status(state='stopped', port=args.port, executable=executable, **current)
        finally:
            close_handle(mutex)


def start_background(args):
    if worker_running():
        print(f'Automation is already running; run {command_hint("stop")} before restarting with different options.')
        return
    if app_processes(locate_app(args.exe, args.cn)):
        command = 'python wuwatappo_auto.py stop' + (' --cn' if args.cn else '')
        if args.exe:
            command += ' --exe ' + subprocess.list2cmdline([str(args.exe)])
        print(f'WuWaTappo is already running; run {command_hint(command)} before {command_hint("start")}.')
        return
    if not ctypes.windll.shell32.IsUserAnAdmin():
        elevate(args)
        return
    pythonw = Path(sys.executable).with_name('pythonw.exe')
    executable = str(pythonw if pythonw.exists() else Path(sys.executable))
    child = subprocess.Popen([executable, *command_arguments(args, 'run')], cwd=ROOT,
                             stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL,
                             creationflags=subprocess.CREATE_NO_WINDOW | subprocess.DETACHED_PROCESS)
    deadline = time.monotonic() + 70
    while time.monotonic() < deadline:
        if child.poll() is not None:
            raise RuntimeError(f'Background startup failed (exit code {child.returncode}); run {command_hint("status", sys.stderr)} for details')
        status = read_status()
        if status.get('pid') == child.pid and status.get('state') in (
                'running', 'waiting_login', 'recovering_login', 'waiting_update',
                'updating', 'restarting_after_update', 'update_needs_attention', 'paused_account_mismatch'):
            print(f'Background automation started: PID {child.pid}, state {status["state"]}.')
            return
        time.sleep(0.2)
    raise RuntimeError(f'Background automation is not ready yet; run {command_hint("status", sys.stderr)} to check it. No duplicate process will be created')


def command_hint(command, stream=None):
    stream = sys.stdout if stream is None else stream
    return f'\033[32m{command}\033[0m' if stream and stream.isatty() else command


def argument_parser():
    parser = argparse.ArgumentParser(
        description='WuWaTappo background clicking and automatic chest opening.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Commands:
  start   Start in the background (default); request stop first if WuWaTappo is running
  run     Run in the foreground; Ctrl+C stops automation and closes WuWaTappo
  stop    Stop automation and close WuWaTappo
  status  Show the current state and automatically assigned port
  check   Check the existing connection without clicking, opening chests, or synthesizing

Examples:
  python wuwatappo_auto.py start -a
  python wuwatappo_auto.py start -e
  python wuwatappo_auto.py start -s
  python wuwatappo_auto.py start --cn -e
  python wuwatappo_auto.py stop

Defaults: Global variant, automatic chest opening, continuous operation.
Synthesis preserves one copy of each item; -e, -s, and -a are mutually exclusive.
-a checks collection progress by type and tier: upgrade while higher tiers are incomplete;
use same-tier synthesis when all higher tiers are complete and the current tier is incomplete.
After a successful draw, perform at most one synthesis every 30 seconds.
Auto-login is enabled when config.json beside this script contains username/password.""")
    parser.add_argument('command', choices=['start', 'run', 'stop', 'status', 'check'],
                        nargs='?', default='start', help='command to execute (default: start)')
    parser.add_argument('--cn', action='store_true', help='CN switch: True when specified, False otherwise (Global). \033[1;31mNote: the CN variant has not been tested\033[0m')
    synthesis = parser.add_mutually_exclusive_group()
    synthesis.add_argument('-e', '--enhance', action='store_true', help='upgrade only: combine 10 items of the same type and rarity into 1; mutually exclusive with -s and -a')
    synthesis.add_argument('-s', '--same-tier', action='store_true', help='same-tier only: combine 5 items of the same type and rarity into 1; mutually exclusive with -e and -a')
    synthesis.add_argument('-a', '--auto', action='store_true', help='choose upgrade or same-tier synthesis based on collection progress; mutually exclusive with -e and -s')
    parser.add_argument('-f', '--frequency', type=float, default=5, help='clicks per second (default: 5; range: 0.2-20)')
    parser.add_argument('-d', '--duration', type=float, default=0, help='duration in seconds; 0 runs continuously (default)')
    parser.add_argument('-x', '--exe', help='full path to WuwaTappo.exe; detected automatically by default')
    return parser


def main():
    parser = argument_parser()
    args = parser.parse_args()
    if not 0.2 <= args.frequency <= 20 or not math.isfinite(args.duration) or args.duration < 0:
        parser.error('Invalid frequency or duration')
    if os.name != 'nt':
        parser.error('Windows is required')
    DATA.mkdir(exist_ok=True)
    LOG.parent.mkdir(exist_ok=True)
    previous = read_status()
    if args.command in ('stop', 'status') and not args.exe and not args.cn:
        args.exe = previous.get('executable')
        if args.exe:
            args.cn = app_identity(Path(args.exe)) == APP_IDS['cn']
    if args.command == 'status':
        previous['worker_running'] = worker_running()
        previous['app_running'] = bool(app_processes(locate_app(args.exe, args.cn)))
        print(json.dumps(previous, ensure_ascii=False, indent=2))
        return
    if args.command == 'check':
        client = find_main(active_port(), app_identity(locate_app(args.exe, args.cn)))
        try:
            print(json.dumps(client.evaluate(BOOTSTRAP), ensure_ascii=False, indent=2))
        finally:
            client.close()
        return
    if args.command == 'start':
        start_background(args)
        return
    if not ctypes.windll.shell32.IsUserAnAdmin():
        elevate(args)
        return
    guard = acquire_mutex(MUTEX + 'Lifecycle')
    mutex = None
    try:
        # Re-read under the lifecycle lock: another command may have just started.
        try:
            args.port = active_port()
        except RuntimeError:
            args.port = available_port()
        if args.command == 'stop':
            stop_all(args)
            return
        if worker_running():
            raise RuntimeError(f'An automation instance is already running; run {command_hint("stop", sys.stderr)} first')
        mutex = acquire_mutex()
        ensure_connection(args)
    except BaseException:
        close_handle(mutex)
        raise
    finally:
        close_handle(guard)
    try:
        run_worker(args, mutex)
    finally:
        # An external stop owns shutdown when its stop marker is present.
        if not STOP.exists():
            stop_all(args)


if __name__ == '__main__':
    try:
        main()
    except (OSError, RuntimeError, ValueError) as error:
        if sys.stderr:
            print(f'Startup/connection failed: {error}', file=sys.stderr)
        sys.exit(1)
