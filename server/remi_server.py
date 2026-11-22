#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Remi Online - server de joc multiplayer (Remi Etalat / Rummy 45)
=================================================================
Server minimal, fara dependinte externe (doar biblioteca standard Python 3.8+).

Contine:
  * motorul de joc complet (106 piese, 2 jokeri, reguli Remi Etalat romanesti)
  * server HTTP + API de tip long-polling (functioneaza prin orice proxy / WebView)
  * servirea clientului web (index.html) din ../app/assets

Pornire:
    python3 remi_server.py --port 8080
Apoi deschizi http://<ip>:8080  in browser sau conectezi aplicatia Android.
"""

import json
import os
import random
import secrets
import string
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

import table_engine

# ----------------------------------------------------------------------------
#  CONSTANTE JOC
# ----------------------------------------------------------------------------

COLORS = ("R", "Y", "B", "K")          # rosu, galben, albastru, negru
COLOR_NAMES = {"R": "roșu", "Y": "galben", "B": "albastru", "K": "negru"}
JOKER_COLOR = "J"

TURN_SECONDS_DEFAULT = 45
LONG_POLL_SECONDS = 8
ROOM_IDLE_TIMEOUT = 60 * 60          # 1 ora fara activitate -> camera este stearsa
MAX_PLAYERS_DEFAULT = 4
MAX_ROOMS = 800
MAX_BODY = 64 * 1024
TARGET_SCORE_DEFAULT = 500
NEXT_ROUND_DELAY = 12                # secunde pana la runda urmatoare


# ----------------------------------------------------------------------------
#  PIESE
# ----------------------------------------------------------------------------

def build_tiles():
    """Returneaza dict: tile_id -> {"c": culoare|"J", "v": valoare 0..13}."""
    tiles = {}
    tid = 0
    for c in COLORS:
        for v in range(1, 14):
            for _copy in range(2):
                tiles[tid] = {"c": c, "v": v}
                tid += 1
    # 2 jokeri
    for _ in range(2):
        tiles[tid] = {"c": JOKER_COLOR, "v": 0}
        tid += 1
    assert len(tiles) == 106
    return tiles


TILES = build_tiles()


def is_joker(t):
    return TILES[t]["c"] == JOKER_COLOR


def tile_color(t):
    return TILES[t]["c"]


def tile_number(t):
    return TILES[t]["v"]


def tile_value(t):
    """Valoarea piesei la punctaj (dupa etalare): 1=25, 10-13=10, 2-9=5, joker=50."""
    if is_joker(t):
        return 50
    v = tile_number(t)
    if v == 1:
        return 25
    if v >= 10:
        return 10
    return 5


def plain_value(v):
    """Valoarea unei piese numerice fara regula speciala pentru 1: 1..9 = 5, 10..13 = 10."""
    return 10 if v >= 10 else 5


# ----------------------------------------------------------------------------
#  VALIDARE FORMATII
# ----------------------------------------------------------------------------

def _seq_expansions(order_vals, jokers):
    """
    order_vals: valorile pieselor naturale in ordine crescatoare (1 poate fi 14 la final)
    jokers: numarul de jokeri
    Returneaza lista de variante (lista completa de valori, cu jokerii inclusi).
    """
    n = len(order_vals) + jokers
    results = []
    for start in range(1, 14):
        end = start + n - 1
        if end > 14:
            continue
        expected = list(range(start, end + 1))
        # potrivim naturalii, in ordine, ca subsecventa a lui expected
        positions = []
        pi = 0
        ok = True
        for v in order_vals:
            found = None
            while pi < len(expected):
                if expected[pi] == v:
                    found = pi
                    pi += 1
                    break
                pi += 1
            if found is None:
                ok = False
                break
            positions.append(found)
        if not ok:
            continue
        # valorile pentru jokeri = pozitiile nefolosite (in ordinea din sir)
        used = set(positions)
        joker_vals = [expected[i] for i in range(len(expected)) if i not in used]
        if len(joker_vals) != jokers:
            continue
        results.append(expected)
    return results


def resolve_sequence(tiles):
    """
    Incearca sa interpreteze lista de piese (in orice ordine) ca suita valida.
    Returneaza (lista de valori efective aliniata la `tiles`, puncte_pre_etalare) sau None.
    Valoarea 14 este folosita intern pentru piesa 1 asezata dupa 13.
    """
    n = len(tiles)
    if n < 3 or n > 13:
        return None
    naturals = [t for t in tiles if not is_joker(t)]
    jokers = n - len(naturals)
    if len(naturals) < 1:
        return None
    if jokers and len(naturals) < 2:
        return None
    if jokers >= 2 and n < 6:
        return None
    colors = {tile_color(t) for t in naturals}
    if len(colors) != 1:
        return None
    nums = [tile_number(t) for t in naturals]
    if nums.count(1) > 1:
        return None

    # piesa 1 poate fi folosita ca 1 (la inceput: 1-2-3) sau ca 14 (la final: 12-13-1)
    variants = []
    if 1 in nums:
        variants.append(sorted(nums))                                  # 1 folosit ca 1
        if (12 in nums and 13 in nums) or (jokers >= 1 and any(v >= 11 for v in nums if v != 1)):
            variants.append(sorted([v for v in nums if v != 1]) + [14])  # 1 folosit ca 14
    else:
        variants.append(sorted(nums))

    best = None
    for order in variants:
        for expected in _seq_expansions(order, jokers):
            # puncte pre-etalare: 1 in 1-2-3 = 5 ; 1 in 12-13-1 = 10 ; restul 5/10 ; joker = piesa inlocuita
            pts = sum(10 if v >= 10 else 5 for v in expected)
            if best is None or pts > best[0]:
                best = (pts, expected)
    if best is None:
        return None
    pts, expected = best

    # aliniem valorile efective la ordinea de intrare a pieselor
    used = [False] * len(expected)
    eff = [None] * n
    free_vals = list(expected)
    nat_idx = [i for i, t in enumerate(tiles) if not is_joker(t)]
    # naturalii se potrivesc dupa valoare; piesa 1 se potriveste si cu 14
    val_positions = {}
    for pos, v in enumerate(expected):
        val_positions.setdefault(v, []).append(pos)

    def sort_key(i):
        v = tile_number(tiles[i])
        if v == 1 and 14 in val_positions and 1 not in val_positions:
            return 15
        return v

    ok = True
    for i in sorted(nat_idx, key=sort_key):
        v = tile_number(tiles[i])
        cand = None
        if val_positions.get(v):
            cand = val_positions[v].pop(0)
        elif v == 1 and val_positions.get(14):
            cand = val_positions[14].pop(0)
        if cand is None:
            ok = False
            break
        eff[i] = 1 if expected[cand] == 14 else tile_number(tiles[i])
        used[cand] = True
    if not ok:
        return None
    free = [expected[i] for i in range(len(expected)) if not used[i]]
    ji = 0
    for i in range(n):
        if is_joker(tiles[i]):
            if ji < len(free):
                eff[i] = 1 if free[ji] == 14 else free[ji]
                ji += 1
            else:
                return None
    assert all(x is not None for x in eff)
    return eff, pts


def resolve_set(tiles):
    """Terta: 3-4 piese cu aceeasi valoare, culori diferite."""
    n = len(tiles)
    if n < 3 or n > 4:
        return None
    naturals = [t for t in tiles if not is_joker(t)]
    jokers = n - len(naturals)
    if len(naturals) < 2:
        return None
    if jokers > 1:
        return None  # ambii jokeri intr-o terta nu este permis
    vals = {tile_number(t) for t in naturals}
    if len(vals) != 1:
        return None
    val = vals.pop()
    colors = [tile_color(t) for t in naturals]
    if len(set(colors)) != len(colors):
        return None
    used_colors = set(colors)
    available = [c for c in COLORS if c not in used_colors]
    if jokers > len(available):
        return None
    # valoare joker = valoarea tertzei
    eff = []
    for t in tiles:
        eff.append(val if is_joker(t) else tile_number(t))
    pts = (25 if val == 1 else plain_value(val)) * n
    return eff, pts


def resolve_group(tiles):
    """
    Returneaza dict {type:'seq'|'set', eff:[...], points_pre:int} sau None daca nu e formatie valida.
    """
    if not tiles or len(set(tiles)) != len(tiles):
        return None
    r = resolve_sequence(tiles)
    if r:
        return {"type": "seq", "eff": r[0], "points_pre": r[1]}
    r = resolve_set(tiles)
    if r:
        return {"type": "set", "eff": r[0], "points_pre": r[1]}
    return None


def group_final_points(tile_ids):
    """Punctele finale ale unui grup (dupa etalare): 1=25, joker=50, 2-9=5, 10-13=10."""
    return sum(tile_value(t) for t in tile_ids)


def gen_valid_groups(tiles):
    """Generează toate formațiile valide (suite și terțe) posibile din `tiles`."""
    from itertools import combinations, product
    tiles = sorted(tiles)
    jokers = [t for t in tiles if is_joker(t)]
    nats = [t for t in tiles if not is_joker(t)]
    out = []
    # 1) Terțe
    by_val = {}
    for t in nats:
        by_val.setdefault(tile_number(t), []).append(t)
    for v, grp in by_val.items():
        by_col = {}
        for t in grp:
            by_col.setdefault(tile_color(t), []).append(t)
        cols = list(by_col.keys())
        for k in range(2, min(4, len(cols)) + 1):
            for csub in combinations(cols, k):
                for prod in product(*(by_col[c] for c in csub)):
                    g = list(prod)
                    if len(g) >= 3 and resolve_set(g):
                        out.append(g)
                    if len(g) <= 3:
                        for j in jokers:
                            cand = g + [j]
                            if resolve_set(cand):
                                out.append(cand)
    # 2) Suite
    by_c = {}
    for t in nats:
        by_c.setdefault(tile_color(t), []).append(t)
    for c, grp in by_c.items():
        by_num = {}
        for t in grp:
            by_num.setdefault(tile_number(t), []).append(t)
        for s in range(1, 13):
            for e in range(s + 2, min(15, s + 13)):
                length = e - s + 1
                if length > len(grp) + len(jokers):
                    continue
                req = []
                miss = 0
                for n in range(s, e + 1):
                    val = 1 if n == 14 else n
                    if val in by_num:
                        req.append(by_num[val])
                    else:
                        miss += 1
                if miss > len(jokers):
                    continue
                if miss == 2 and length < 6:
                    continue
                if length - miss < 2:
                    continue
                for j_use in combinations(jokers, miss):
                    for prod in product(*req):
                        cand = list(prod) + list(j_use)
                        if resolve_sequence(cand):
                            out.append(cand)
    seen = set()
    uniq = []
    for g in out:
        fs = frozenset(g)
        if fs not in seen:
            seen.add(fs)
            uniq.append(g)
    return uniq


def find_complete_partition(tiles):
    """Returnează o partiție completă în formații valide sau None."""
    if not tiles:
        return []
    groups = gen_valid_groups(tiles)
    by_tile = {t: [] for t in tiles}
    for g in groups:
        for t in g:
            by_tile[t].append(g)

    def rec(rem):
        if not rem:
            return []
        t0 = min(rem, key=lambda t: sum(1 for g in by_tile[t] if all(x in rem for x in g)))
        cands = [g for g in by_tile[t0] if all(x in rem for x in g)]
        for g in cands:
            res = rec(rem - frozenset(g))
            if res is not None:
                return [g] + res
        return None

    return rec(frozenset(tiles))


def best_partial_partition(tiles):
    """Găsește grupurile valide care acoperă cele mai multe puncte (pentru scor Remi pe tablă)."""
    groups = gen_valid_groups(tiles)
    if not groups:
        return []
    g_info = [(frozenset(g), sum(tile_value(t) for t in g), g) for g in groups]
    g_info.sort(key=lambda x: -x[1])
    best = {"pts": 0, "groups": []}

    def rec(idx, rem, acc, pts):
        if pts > best["pts"]:
            best["pts"] = pts
            best["groups"] = list(acc)
        if idx >= len(g_info):
            return
        max_rem_pts = sum(tile_value(t) for t in rem)
        if pts + max_rem_pts <= best["pts"]:
            return
        for i in range(idx, len(g_info)):
            fs, pval, raw = g_info[i]
            if fs.issubset(rem):
                acc.append(raw)
                rec(i + 1, rem - fs, acc, pts + pval)
                acc.pop()

    rec(0, frozenset(tiles), [], 0)
    return best["groups"]


# ----------------------------------------------------------------------------
#  CAMERA / STARE DE JOC
# ----------------------------------------------------------------------------

def new_code():
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    return "".join(secrets.choice(alphabet) for _ in range(5))


class GameError(Exception):
    pass


def _sort_group_tiles(gtype, items):
    if gtype != "seq" or not items:
        return items
    effs = {it["eff"] for it in items}
    ace_high = 1 in effs and (12 in effs or 13 in effs or (len(items) >= 3 and any(v >= 11 for v in effs if v != 1)))
    return sorted(items, key=lambda it: 14 if (it["eff"] == 1 and ace_high) else it["eff"])


class Room:
    def __init__(self, opts=None):
        self.code = new_code()
        self.created = time.time()
        self.last_activity = time.time()
        self.lock = threading.RLock()
        self.cond = threading.Condition(self.lock)
        self.version = 0
        self.opts = {
            "max_players": MAX_PLAYERS_DEFAULT,
            "turn_seconds": TURN_SECONDS_DEFAULT,
            "target": TARGET_SCORE_DEFAULT,
            "mode": "etalat",
        }
        if opts:
            for k in ("max_players", "turn_seconds", "target"):
                if k in opts:
                    try:
                        self.opts[k] = int(opts[k])
                    except (TypeError, ValueError):
                        pass
            if str(opts.get("mode", "")).lower() == "tabla":
                self.opts["mode"] = "tabla"
        self.opts["max_players"] = max(2, min(4, self.opts["max_players"]))
        self.opts["turn_seconds"] = max(10, min(120, self.opts["turn_seconds"]))
        self.phase = "lobby"          # lobby | playing | round_end | game_over
        self.players = []             # lista de dict
        self.seat_order = []
        self.round_no = 0
        self.starter = 0
        self.turn_pid = None
        self.turn_deadline = 0
        self.turn_seconds_left = 0
        self.stock = []
        self.discard = []
        self.opening_discard_locked = False
        self.atu_tile = None
        self.groups = {}              # gid -> {"id":gid,"type":..,"owner":pid,"tiles":[{"t":id,"eff":v,"by":pid}]}
        self.next_gid = 1
        self.turns_completed = 0
        self.log = []
        self.chat = []
        self.round_scores = None      # rezultate runda curenta/ultima
        self.history = []             # punctaje cumulate per runda
        self.next_round_at = 0
        self.winner_pid = None

        # stare pe tura
        self.drew = False
        self.drawn_from = None
        self.taken_discard_tile = None
        self.placed_this_turn = set()
        self.placed_in_new_group = set()
        self.melded_this_turn = False

    # ---------------------------------------------------------------- utils
    def add_log(self, text):
        self.log.append({"t": int(time.time()), "x": text})
        if len(self.log) > 80:
            self.log = self.log[-80:]

    def add_chat(self, pid, name, text):
        text = (text or "").strip()[:200]
        if not text:
            return
        self.chat.append({"t": int(time.time()), "pid": pid, "name": name, "text": text})
        if len(self.chat) > 60:
            self.chat = self.chat[-60:]

    def bump(self):
        self.version += 1
        self.last_activity = time.time()
        try:
            self.cond.notify_all()
        except RuntimeError:
            pass

    def player(self, pid):
        for p in self.players:
            if p["id"] == pid:
                return p
        return None

    def player_by_token(self, token):
        for p in self.players:
            if p["token"] == token:
                return p
        return None

    def alive_players(self):
        return self.players

    def active_players(self):
        return [p for p in self.players if p.get("connected") or p.get("ready")]

    def is_full(self):
        return len(self.players) >= self.opts["max_players"]

    # ---------------------------------------------------------- lobby logic
    def add_player(self, name, avatar=""):
        name = (name or "").strip()[:18] or "Jucător"
        if self.is_full():
            raise GameError("Camera este plină.")
        names = {p["name"].lower() for p in self.players}
        base = name
        i = 2
        while name.lower() in names:
            name = f"{base}{i}"
            i += 1
        av = avatar if isinstance(avatar, str) and len(avatar) <= 24000 else ""
        pid = secrets.token_hex(6)
        token = secrets.token_hex(24)
        p = {
            "id": pid,
            "token": token,
            "name": name,
            "avatar": av,
            "seat": len(self.players),
            "connected": True,
            "ready": False,
            "hand": [],
            "first_meld": False,
            "atu": False,
            "atu_declared": False,
            "first_turn_done": False,
            "score": 0,
            "round_score": 0,
            "is_bot": False,
            "last_seen": time.time(),
        }
        self.players.append(p)
        self.add_log(f"{name} a intrat în cameră.")
        self.bump()
        return p

    def set_ready(self, pid, ready=True):
        p = self.player(pid)
        if not p:
            raise GameError("Jucător inexistent.")
        if self.phase != "lobby":
            return
        p["ready"] = bool(ready)
        self.add_log(f"{p['name']} este {'gata' if ready else 'nepregătit'}.")
        self.bump()

    def maybe_start(self):
        if self.phase != "lobby":
            return
        ps = self.players
        if len(ps) < 2:
            return
        if all(p["ready"] for p in ps) and len(ps) >= 2:
            self.start_round(first=True)

    # ----------------------------------------------------------- start runda
    def start_round(self, first=False):
        n = len(self.players)
        if n < 2:
            raise GameError("Este nevoie de minim 2 jucători.")
        self.round_no += 1
        deck = list(TILES.keys())
        random.shuffle(deck)
        for p in self.players:
            p["hand"] = []
            p["first_meld"] = False
            p["atu"] = False
            p["atu_declared"] = False
            p["first_turn_done"] = False
            p["ready"] = True
        self.starter = (self.round_no - 1) % n
        order = [p for p in self.players]
        # impartire: primul jucator primeste 15 piese, ceilalti 14
        for i, p in enumerate(order):
            count = 15 if i == self.starter else 14
            for _ in range(count):
                p["hand"].append(deck.pop())
        # piesa de atu (vizibila, ramane in gramada)
        self.atu_tile = deck.pop()
        # anuntarea atuului: cine are perechea piesei de atu
        if not is_joker(self.atu_tile):
            pair_id = self.atu_tile ^ 1
            for p in self.players:
                if pair_id in p["hand"]:
                    p["atu"] = True
        self.stock = deck
        self.discard = []
        self.opening_discard_locked = False
        self.groups = {}
        self.next_gid = 1
        self.turns_completed = 0
        self.phase = "playing"
        self.round_scores = None
        self.next_round_at = 0
        self.add_log(f"—— Runda {self.round_no} ——")
        self.add_log(f"Piesa de atu: {tile_label(self.atu_tile)}")
        self.turn_pid = order[self.starter]["id"]
        self._begin_turn()
        self.bump()

    # -------------------------------------------------------------- tura
    def _begin_turn(self):
        self.drew = False
        self.drawn_from = None
        self.taken_discard_tile = None
        self.placed_this_turn = set()
        self.placed_in_new_group = set()
        self.melded_this_turn = False
        self.turn_deadline = time.time() + self.opts["turn_seconds"]
        self.turn_seconds_left = self.opts["turn_seconds"]
        p = self.player(self.turn_pid)
        if not p:
            return
        # primul jucator al rundei nu trage piesa (are 15)
        if self.turns_completed == 0 and p["seat"] == self.starter:
            self.drew = True
            self.drawn_from = "starter"

    def _next_turn(self):
        idx = [p["id"] for p in self.players].index(self.turn_pid)
        self.turn_pid = self.players[(idx + 1) % len(self.players)]["id"]
        self._begin_turn()

    def handle_timeout(self):
        if self.phase != "playing":
            return
        now = time.time()
        if now < self.turn_deadline:
            return
        pid = self.turn_pid
        p = self.player(pid)
        if not p:
            return
        self.add_log(f"⏰ {p['name']} a depășit timpul — se joacă automat.")
        try:
            if not self.drew:
                self._draw_stock(pid, auto=True)
            if p["hand"]:
                # arunca piesa cu cea mai mica valoare (evita inchiderea accidentala daca are multe piese)
                cand = sorted(p["hand"], key=lambda t: tile_value(t))
                tile = cand[0]
                self._discard(pid, tile, auto=True)
        except GameError as e:
            self.add_log(f"Automat: {e}")
            try:
                self._next_turn()
            except Exception:
                pass
        self.bump()

    # ------------------------------------------------------------- trageri
    def _draw_stock(self, pid, auto=False):
        p = self.player(pid)
        if self.turn_pid != pid:
            raise GameError("Nu este rândul tău.")
        if self.drew:
            raise GameError("Ai tras deja o piesă în această tură.")
        if not self.stock:
            # gramada s-a terminat -> runda se incheie (ca la masa reala)
            self._end_round(closer=None, closing_tile=None, reason="stock")
            return
        t = self.stock.pop()
        p["hand"].append(t)
        self.drew = True
        self.drawn_from = "stock"
        if not auto:
            self.add_log(f"{p['name']} a tras o piesă din grămadă.")
        self.bump()

    def _refill_stock(self):
        if len(self.discard) > 1:
            top = self.discard[-1]
            rest = self.discard[:-1]
            random.shuffle(rest)
            self.stock = rest
            self.discard = [top]
            self.opening_discard_locked = False
            self.add_log("Grămada a fost reconstruită din piesa aruncată.")

    def can_use_discard(self, pid, tile=None):
        """Poate jucatorul sa foloseasca imediat piesa de jos intr-o formatie?"""
        p = self.player(pid)
        if not p or not p["first_turn_done"]:
            return False
        if not self.discard:
            return False
        avail = self.discard[1:] if self.opening_discard_locked else self.discard
        if not avail:
            return False
        if tile is None:
            tile = self.discard[-1]
        if tile not in avail:
            return False
        hand = list(p["hand"])
        hand_plus = hand + [tile]
        if p["first_meld"]:
            # cu 1 sau 2 piese pe tabla nu mai ai voie sa iei din cele aruncate
            if len(hand) <= 2:
                return False
            # cu 3 piese pe tabla poti lua doar ultima piesa aruncata
            if len(hand) == 3 and tile != self.discard[-1]:
                return False
            # trebuie sa creeze o formatie noua cu piesele de pe tabla si sa ramana >=1 piesa de aruncat
            max_used = len(hand_plus) - 1
            for g in gen_valid_groups(hand_plus):
                if tile in g and len(g) <= max_used:
                    return True
            return False

        # ne-etalat: doar ultima piesa aruncata, pentru deschidere >=45p + minim o suita + >=1 piesa de aruncat
        if tile != self.discard[-1]:
            return False
        all_g = gen_valid_groups(hand_plus)
        g_info = []
        for g in all_g:
            r = resolve_group(g)
            if r:
                g_info.append((g, set(g), r["points_pre"], r["type"] == "seq"))
        with_tile = [x for x in g_info if tile in x[1]]
        if not with_tile:
            return False
        with_tile.sort(key=lambda x: (-int(x[3]), -x[2]))
        other_g = sorted([x for x in g_info if tile not in x[1]], key=lambda x: (-x[2], -int(x[3])))
        max_used = max(0, len(hand_plus) - 1)
        nodes = [0]

        def rec(idx, used_set, pts, has_seq):
            nodes[0] += 1
            if nodes[0] > 1800:
                return False
            if has_seq and pts >= 45 and len(used_set) <= max_used:
                return True
            if len(used_set) >= max_used:
                return False
            for i in range(idx, len(other_g)):
                g, gset, gp, gseq = other_g[i]
                if len(used_set) + len(gset) > max_used:
                    continue
                if used_set & gset:
                    continue
                if rec(i + 1, used_set | gset, pts + gp, has_seq or gseq):
                    return True
            return False

        for g, gset, gp, gseq in with_tile:
            if len(gset) <= max_used and rec(0, gset, gp, gseq):
                return True
        return False

    def _draw_discard(self, pid, tile=None):
        p = self.player(pid)
        if self.turn_pid != pid:
            raise GameError("Nu este rândul tău.")
        if self.drew:
            raise GameError("Ai tras deja o piesă în această tură.")
        if not self.discard:
            raise GameError("Nu există piese aruncate.")
        is_tabla = (self.opts.get("mode") == "tabla")
        if tile is not None:
            try:
                tile = int(tile)
            except (TypeError, ValueError):
                raise GameError("Piesă invalidă.")
        if not is_tabla:
            if not p["first_turn_done"]:
                raise GameError("În prima ta tură nu poți lua de jos și nu poți etala — trage din grămadă (+).")
            if self.opening_discard_locked and len(self.discard) <= 1:
                raise GameError("Prima piesă aruncată la începutul rundei nu se poate ridica nicicum.")
            if p["first_meld"] and len(p["hand"]) <= 2:
                raise GameError("Când mai ai doar 1 sau 2 piese pe tablă, nu mai poți lua din cele aruncate.")
        if tile is None or tile == self.discard[-1]:
            t = self.discard[-1]
            if not is_tabla and not self.can_use_discard(pid, tile=t):
                if p["first_meld"]:
                    raise GameError("Poți lua ultima piesă doar dacă creează imediat o formație cu piesele de pe tablă.")
                raise GameError("Poți lua ultima piesă doar dacă formează imediat o etalare de minim 45p cu suită.")
            self.discard.pop()
        else:
            if is_tabla or not p["first_meld"]:
                raise GameError("Până nu te etalezi (45p), poți lua doar ultima piesă aruncată (cea din stânga).")
            if len(p["hand"]) == 3:
                raise GameError("Când mai ai doar 3 piese pe tablă, poți lua doar ultima piesă aruncată (cea din stânga).")
            avail = self.discard[1:] if self.opening_discard_locked else self.discard
            if tile not in avail:
                if self.opening_discard_locked and tile == self.discard[0]:
                    raise GameError("Prima piesă aruncată la începutul rundei nu se poate ridica nicicum.")
                raise GameError("Piesa aleasă nu mai este disponibilă în șirul de jos.")
            if not self.can_use_discard(pid, tile=tile):
                raise GameError(f"Nu poți lua {tile_label(tile)} — trebuie să formeze imediat o formație cu piesele de pe tablă.")
            start_idx = 1 if self.opening_discard_locked else 0
            idx = len(self.discard) - 1 - self.discard[start_idx:][::-1].index(tile)
            t = self.discard.pop(idx)
        p["hand"].append(t)
        self.drew = True
        self.drawn_from = "discard"
        self.taken_discard_tile = t
        self.add_log(f"{p['name']} a luat piesa de jos ({tile_label(t)}).")
        self.bump()

    # ------------------------------------------------------------ etalare
    def _can_meld_now(self, pid):
        if self.opts.get("mode") == "tabla":
            raise GameError("În Remi pe tablă nu se etalează pe masă — formează pe suport și apasă Închide.")
        if self.turn_pid != pid:
            raise GameError("Nu este rândul tău.")
        if self.phase != "playing":
            raise GameError("Jocul nu este în desfășurare.")
        if not self.drew:
            raise GameError("Trage întâi o piesă.")
        p = self.player(pid)
        if not p or not p["first_turn_done"]:
            raise GameError("Nu poți etala din prima ta tură! Etalarea începe de la a doua tură.")

    def action_meld(self, pid, groups):
        self._can_meld_now(pid)
        p = self.player(pid)
        hand = set(p["hand"])
        all_ids = []
        resolved = []
        for g in groups:
            if not isinstance(g, list) or not g:
                raise GameError("Formație invalidă.")
            if len(set(g)) != len(g):
                raise GameError("Piese duplicate în formație.")
            for t in g:
                if t not in hand:
                    raise GameError("Ai selectat o piesă care nu este în mâna ta.")
                if t in all_ids:
                    raise GameError("Aceeași piesă apare în două formații.")
            r = resolve_group(g)
            if not r:
                raise GameError("Formație invalidă: " + ", ".join(tile_label(t) for t in g))
            all_ids.extend(g)
            resolved.append((g, r))

        first = not p["first_meld"]
        if first:
            total = sum(r["points_pre"] for _, r in resolved)
            has_seq = any(r["type"] == "seq" for _, r in resolved)
            if total < 45:
                raise GameError(f"Prima etalare trebuie să valoreze minim 45 de puncte (ai {total}).")
            if not has_seq:
                raise GameError("Prima etalare trebuie să conțină cel puțin o suită (nu doar terțe).")
        for g, r in resolved:
            gid = self.next_gid
            self.next_gid += 1
            items = [{"t": t, "eff": r["eff"][i], "by": pid} for i, t in enumerate(g)]
            self.groups[gid] = {
                "id": gid,
                "type": r["type"],
                "owner": pid,
                "tiles": _sort_group_tiles(r["type"], items),
            }
            self.placed_this_turn.update(g)
            self.placed_in_new_group.update(g)
        for t in all_ids:
            p["hand"].remove(t)
        if first:
            self.melded_this_turn = True
            p["first_meld"] = True
            self.add_log(f"{p['name']} s-a etalat cu {len(all_ids)} piese.")
        else:
            self.add_log(f"{p['name']} a mai coborât {len(resolved)} formație/formații.")
        self._check_empty_hand(pid)
        self.bump()

    def action_add(self, pid, gid, tile):
        self._can_meld_now(pid)
        p = self.player(pid)
        if not p["first_meld"]:
            raise GameError("Trebuie să te etalezi mai întâi (minim 45 de puncte).")
        g = self.groups.get(int(gid))
        if not g:
            raise GameError("Formația nu există.")
        if tile not in p["hand"]:
            raise GameError("Piesa nu este în mâna ta.")
        tiles = [x["t"] for x in g["tiles"]]
        best = None
        opts = []
        if g["type"] == "seq":
            opts.append(tiles + [tile])
            opts.append([tile] + tiles)
        else:
            opts.append(tiles + [tile])
        for cand in opts:
            r = resolve_group(cand)
            if r and r["type"] == g["type"]:
                best = (cand, r)
                break
        if not best:
            raise GameError("Piesa nu poate fi lipită la această formație.")
        cand, r = best
        order = cand
        old_by = {x["t"]: x["by"] for x in g["tiles"]}
        items = [{"t": t, "eff": r["eff"][i], "by": pid if t == tile else old_by.get(t, pid)} for i, t in enumerate(order)]
        g["tiles"] = _sort_group_tiles(g["type"], items)
        p["hand"].remove(tile)
        self.placed_this_turn.add(tile)
        self.add_log(f"{p['name']} a lipit {tile_label(tile)} la o formație.")
        self._check_empty_hand(pid)
        self.bump()

    def action_swap_joker(self, pid, gid, tile):
        self._can_meld_now(pid)
        p = self.player(pid)
        if not p["first_meld"]:
            raise GameError("Trebuie să te etalezi mai întâi.")
        g = self.groups.get(int(gid))
        if not g:
            raise GameError("Formația nu există.")
        if tile not in p["hand"] or is_joker(tile):
            raise GameError("Alege o piesă potrivită din mâna ta.")
        tiles = [x["t"] for x in g["tiles"]]
        jidx = [i for i, t in enumerate(tiles) if is_joker(t)]
        if not jidx:
            raise GameError("Formația nu conține joker.")
        done = False
        for i in jidx:
            cand = list(tiles)
            cand[i] = tile
            r = resolve_group(cand)
            if r and r["type"] == g["type"]:
                old_by = {x["t"]: x["by"] for x in g["tiles"]}
                items = [{"t": t, "eff": r["eff"][k], "by": pid if t == tile else old_by.get(t, pid)}
                         for k, t in enumerate(cand)]
                g["tiles"] = _sort_group_tiles(g["type"], items)
                p["hand"].remove(tile)
                p["hand"].append(tiles[i])  # jokerul intra in mana
                done = True
                self.add_log(f"{p['name']} a înlocuit un joker și l-a luat în mână.")
                break
        if not done:
            raise GameError("Piesa ta nu poate înlocui jokerul din această formație.")
        self._check_empty_hand(pid)
        self.bump()

    def _check_empty_hand(self, pid):
        p = self.player(pid)
        if p and not p["hand"]:
            self._end_round(closer=pid, closing_tile=None, reason="meld_all")

    # ------------------------------------------------------------- aruncare
    def action_discard(self, pid, tile):
        if self.turn_pid != pid:
            raise GameError("Nu este rândul tău.")
        if self.phase != "playing":
            raise GameError("Jocul nu este în desfășurare.")
        p = self.player(pid)
        if not self.drew:
            raise GameError("Trage întâi o piesă.")
        if tile not in p["hand"]:
            raise GameError("Piesa nu este în mâna ta.")
        self._discard(pid, tile)
        self.bump()

    def _discard(self, pid, tile, auto=False):
        p = self.player(pid)
        if self.opts.get("mode") == "tabla":
            if self.drawn_from == "discard" and self.taken_discard_tile == tile and not auto:
                raise GameError("Nu poți arunca imediat aceeași piesă pe care ai luat-o de jos.")
            p["hand"].remove(tile)
            self.discard.append(tile)
            p["first_turn_done"] = True
            self.turns_completed += 1
            if not auto:
                self.add_log(f"{p['name']} a aruncat {tile_label(tile)}.")
            self._next_turn()
            return
        if self.drawn_from == "discard" and self.taken_discard_tile is not None:
            if self.taken_discard_tile not in self.placed_in_new_group:
                raise GameError("Ai luat piesa de jos — trebuie să formezi imediat o suită/terță nouă cu ea pe masă.")
        was_opening = (self.turns_completed == 0 and len(self.discard) == 0)
        p["hand"].remove(tile)
        closing = (len(p["hand"]) == 0 and p["first_meld"])
        if closing:
            self._end_round(closer=pid, closing_tile=tile, reason="close")
            return
        self.discard.append(tile)
        if was_opening:
            self.opening_discard_locked = True
        p["first_turn_done"] = True
        self.turns_completed += 1
        if not auto:
            self.add_log(f"{p['name']} a aruncat {tile_label(tile)}.")
        self._next_turn()

    def action_close_tabla(self, pid, closing_tile):
        if self.opts.get("mode") != "tabla":
            raise GameError("Această acțiune este doar pentru Remi pe tablă.")
        if self.turn_pid != pid:
            raise GameError("Nu este rândul tău.")
        if self.phase != "playing":
            raise GameError("Jocul nu este în desfășurare.")
        p = self.player(pid)
        if not self.drew:
            raise GameError("Trage întâi o piesă.")
        if closing_tile not in p["hand"] or len(p["hand"]) != 15:
            raise GameError("Trebuie să ai 15 piese și să alegi ultima piesă pentru închidere.")
        if self.drawn_from == "discard" and self.taken_discard_tile == closing_tile:
            raise GameError("Nu poți închide aruncând exact piesa luată de jos.")
        rem = [t for t in p["hand"] if t != closing_tile]
        part = find_complete_partition(rem)
        if not part:
            raise GameError("Celelalte 14 piese nu sunt încă toate în suite sau terțe valide!")
        # Afișează formațiile câștigătorului pe masă
        self.groups.clear()
        for g in part:
            r = resolve_group(g)
            gid = self.next_gid
            self.next_gid += 1
            self.groups[gid] = {
                "id": gid,
                "type": r["type"],
                "owner": pid,
                "tiles": [{"t": t, "eff": r["eff"][i], "by": pid} for i, t in enumerate(g)],
            }
        p["hand"] = []
        p["first_meld"] = True
        self._end_round(closer=pid, closing_tile=closing_tile, reason="close")
        self.bump()

    # ---------------------------------------------------------------- atu
    def action_announce_atu(self, pid):
        p = self.player(pid)
        if self.phase != "playing":
            raise GameError("Jocul nu este în desfășurare.")
        if not p["atu"]:
            raise GameError("Nu ai piesa pereche cu cea de atu.")
        if p["atu_declared"]:
            raise GameError("Ai anunțat deja atuul.")
        if p["first_turn_done"]:
            raise GameError("Atuul se poate anunța doar la prima tură.")
        p["atu_declared"] = True
        self.add_log(f"⭐ {p['name']} a anunțat atuul (+50 puncte).")
        self.bump()

    # ---------------------------------------------------------- final runda
    def _rack_points(self, p):
        return sum(tile_value(t) for t in p["hand"])

    def _end_round(self, closer=None, closing_tile=None, reason="close"):
        self.phase = "round_end"
        is_tabla = (self.opts.get("mode") == "tabla")
        is_double_tile = (
            closing_tile is not None
            and (is_joker(closing_tile) or tile_number(closing_tile) == 1)
        )
        is_double_atu = (
            self.atu_tile is not None
            and (is_joker(self.atu_tile) or tile_number(self.atu_tile) == 1)
        )
        results = []
        for p in self.players:
            atu_bonus = 50 if p["atu_declared"] else 0
            if is_tabla:
                close_bonus = 0
                if p["id"] == closer and reason == "close":
                    close_bonus = 500 if is_double_tile else 250
                    melded = sum(tile_value(x["t"]) for g in self.groups.values() for x in g["tiles"])
                    rack = 0
                    total = close_bonus + atu_bonus
                    if is_double_atu:
                        total *= 2
                    meld_ed = True
                else:
                    covered_groups = best_partial_partition(p["hand"])
                    covered_ids = {t for g in covered_groups for t in g}
                    deadwood = [t for t in p["hand"] if t not in covered_ids]
                    melded = sum(tile_value(t) for t in covered_ids)
                    rack = sum(tile_value(t) for t in deadwood)
                    meld_ed = bool(covered_groups)
                    total = (-rack + atu_bonus) if meld_ed else (-100 + atu_bonus)
                    if is_double_atu:
                        total *= 2
                p["round_score"] = total
                p["score"] += total
                results.append({
                    "pid": p["id"], "name": p["name"], "melded": melded, "rack": rack,
                    "atu": atu_bonus, "close": close_bonus,
                    "double": bool((p["id"] == closer and is_double_tile) or is_double_atu),
                    "meld_ed": meld_ed, "total": total,
                    "hand": list(p["hand"]),
                })
                continue
            melded = 0
            for g in self.groups.values():
                for x in g["tiles"]:
                    if x["by"] == p["id"]:
                        melded += tile_value(x["t"])
            rack = self._rack_points(p)
            close_bonus = 0
            if p["id"] == closer and reason != "stock":
                close_bonus = 50
            if not p["first_meld"]:
                total = -100 + atu_bonus
                melded = 0
                rack = 0
            else:
                total = melded - rack + atu_bonus + close_bonus
            if reason == "stock":
                total = (melded - rack + atu_bonus) if p["first_meld"] else (-100 + atu_bonus)
            if p["id"] == closer and reason != "stock" and is_double_tile:
                total *= 2
            if is_double_atu:
                total *= 2
            p["round_score"] = total
            p["score"] += total
            results.append({
                "pid": p["id"], "name": p["name"], "melded": melded, "rack": rack,
                "atu": atu_bonus, "close": close_bonus,
                "double": bool((p["id"] == closer and reason != "stock" and is_double_tile) or is_double_atu),
                "meld_ed": bool(p["first_meld"]), "total": total,
                "hand": list(p["hand"]),
            })
        self.round_scores = {
            "round": self.round_no,
            "mode": self.opts.get("mode", "etalat"),
            "closer": closer,
            "closing_tile": closing_tile,
            "double_close": bool(is_double_tile),
            "double_atu": bool(is_double_atu),
            "reason": reason,
            "results": results,
        }
        if closer:
            cp = self.player(closer)
            self.add_log(f"🏁 {cp['name']} a închis runda!")
        else:
            self.add_log("🏁 Rundele s-au terminat — grămada este goală.")
        # verificare final de joc
        target = self.opts.get("target", 0)
        self.winner_pid = None
        if target == 0:
            best = max(self.players, key=lambda p: p["score"])
            self.phase = "game_over"
            self.winner_pid = best["id"]
            self.add_log(f"👑 {best['name']} a câștigat runda cu {best['score']} puncte!")
        if target and max((p["score"] for p in self.players), default=0) >= target:
            best = max(self.players, key=lambda p: p["score"])
            if sum(1 for p in self.players if p["score"] == best["score"]) == 1:
                self.phase = "game_over"
                self.winner_pid = best["id"]
                self.add_log(f"👑 {best['name']} a câștigat jocul cu {best['score']} puncte!")
        if self.phase == "round_end":
            self.next_round_at = time.time() + NEXT_ROUND_DELAY
        self.bump()

    def action_next_round(self, pid):
        if self.phase != "round_end":
            return
        self.start_round()

    def action_new_game(self, pid):
        if self.phase not in ("game_over", "round_end"):
            return
        for p in self.players:
            p["score"] = 0
            p["round_score"] = 0
        self.round_no = 0
        self.phase = "lobby"
        for p in self.players:
            p["ready"] = True
        self.add_log("Joc nou.")
        self.bump()
        self.maybe_start()

    def remove_player(self, pid, reason="a părăsit jocul"):
        p = self.player(pid)
        if not p:
            return
        self.add_log(f"{p['name']} {reason}.")
        if self.phase == "playing":
            # jucatorul plecat este inlocuit automat (timeout) la randul lui
            p["connected"] = False
            p["left"] = True
        else:
            self.players = [x for x in self.players if x["id"] != pid]
            for i, x in enumerate(self.players):
                x["seat"] = i
        self.bump()

    # -------------------------------------------------------------- tick
    def tick(self, now):
        if self.phase == "playing":
            self.turn_seconds_left = max(0, int(self.turn_deadline - now))
            if now >= self.turn_deadline:
                self.handle_timeout()
        elif self.phase == "round_end":
            if self.next_round_at and now >= self.next_round_at and len([p for p in self.players if p["connected"]]) >= 2:
                try:
                    self.start_round()
                except GameError:
                    pass

    # ------------------------------------------------------------ snapshot
    def snapshot(self, viewer_pid):
        me = self.player(viewer_pid)
        now = time.time()
        players = []
        for p in self.players:
            players.append({
                "id": p["id"],
                "name": p["name"],
                "avatar": p.get("avatar", ""),
                "seat": p["seat"],
                "connected": p["connected"] and (time.time() - p.get("last_seen", time.time()) < 20),
                "ready": p["ready"],
                "handCount": len(p["hand"]),
                "firstMeld": p["first_meld"],
                "score": p["score"],
                "roundScore": p["round_score"],
                "atu": p["atu"] and not p["atu_declared"],
                "atuDeclared": p["atu_declared"],
                "isTurn": p["id"] == self.turn_pid,
                "isStarter": p["seat"] == self.starter if self.phase != "lobby" else False,
            })
        groups = []
        for g in self.groups.values():
            groups.append({
                "id": g["id"],
                "type": g["type"],
                "owner": g["owner"],
                "mine": g["owner"] == viewer_pid,
                "tiles": [{"t": x["t"], "eff": x["eff"], "by": x["by"]} for x in g["tiles"]],
                "points": group_final_points([x["t"] for x in g["tiles"]]),
            })
        groups.sort(key=lambda g: g["id"])
        is_tabla = (self.opts.get("mode") == "tabla")
        can_meld_round = (not is_tabla) and self.phase == "playing" and bool(me and me["first_turn_done"])
        me_state = None
        if me:
            avail_disc = self.discard[1:] if self.opening_discard_locked else self.discard
            can_take_disc = (me["id"] == self.turn_pid and not self.drew and bool(self.discard)
                             and self.phase == "playing"
                             and (True if is_tabla else self.can_use_discard(me["id"])))
            usable_disc = []
            if me["id"] == self.turn_pid and not self.drew and bool(self.discard) and self.phase == "playing":
                if is_tabla:
                    usable_disc = [self.discard[-1]]
                elif me["first_turn_done"] and avail_disc:
                    if me["first_meld"] and len(me["hand"]) <= 2:
                        usable_disc = []
                    elif me["first_meld"] and len(me["hand"]) == 3:
                        if self.can_use_discard(me["id"], tile=self.discard[-1]):
                            usable_disc = [self.discard[-1]]
                    elif me["first_meld"] and len(me["hand"]) >= 4:
                        seen_d = set()
                        for dt in reversed(avail_disc):
                            if dt not in seen_d:
                                seen_d.add(dt)
                                if self.can_use_discard(me["id"], tile=dt):
                                    usable_disc.append(dt)
                    elif self.can_use_discard(me["id"]):
                        usable_disc = [self.discard[-1]]
            me_state = {
                "id": me["id"],
                "name": me["name"],
                "hand": sorted(me["hand"], key=lambda t: (is_joker(t), tile_color(t), tile_number(t))),
                "firstMeld": me["first_meld"],
                "firstTurnDone": bool(me["first_turn_done"]),
                "atu": me["atu"],
                "atuDeclared": me["atu_declared"],
                "isTurn": me["id"] == self.turn_pid,
                "drew": self.drew,
                "drawnFrom": self.drawn_from,
                "takenDiscardTile": self.taken_discard_tile if (me["id"] == self.turn_pid and self.drawn_from == "discard") else None,
                "canDraw": (me["id"] == self.turn_pid and not self.drew and self.phase == "playing"),
                "canTakeDiscard": can_take_disc,
                "usableDiscardTiles": usable_disc,
                "canMeld": bool(me["id"] == self.turn_pid and self.drew and can_meld_round),
                "canDiscard": bool(me["id"] == self.turn_pid and self.drew and self.phase == "playing"),
                "canAnnounceAtu": bool(me["atu"] and not me["atu_declared"] and self.phase == "playing"
                                       and not me["first_turn_done"]),
                "canClose": bool((not is_tabla) and me["id"] == self.turn_pid and self.drew and me["first_meld"]
                                 and len(me["hand"]) == 1 and self.phase == "playing"),
                "canCloseTabla": bool(is_tabla and me["id"] == self.turn_pid and self.drew
                                      and len(me["hand"]) == 15 and self.phase == "playing"),
                "ready": me["ready"],
            }
        return {
            "v": self.version,
            "code": self.code,
            "game": "remi",
            "phase": self.phase,
            "opts": self.opts,
            "round": self.round_no,
            "players": players,
            "turnPid": self.turn_pid,
            "turnLeft": int(max(0, self.turn_deadline - now)) if self.phase == "playing" else 0,
            "turnSeconds": self.opts["turn_seconds"],
            "stockCount": len(self.stock),
            "discardTop": self.discard[-1] if self.discard else None,
            "discardTrail": list(reversed(self.discard[-24:])),
            "discardCount": len(self.discard),
            "openingDiscardLocked": bool(self.opening_discard_locked and len(self.discard) > 0),
            "atuTile": self.atu_tile,
            "groups": groups,
            "me": me_state,
            "log": self.log[-25:],
            "chat": self.chat[-30:],
            "roundScores": self.round_scores,
            "nextRoundIn": int(max(0, self.next_round_at - now)) if self.phase == "round_end" else 0,
            "winnerPid": self.winner_pid,
            "hostPid": self.players[0]["id"] if self.players else None,
        }


def tile_label(t):
    if is_joker(t):
        return "★Joker"
    names = {"R": "R", "Y": "G", "B": "A", "K": "N"}
    return f"{tile_number(t)}{names.get(tile_color(t), '?')}"


# ----------------------------------------------------------------------------
#  REGISTRU CAMERE + NOTIFICARI
# ----------------------------------------------------------------------------

ROOMS = {}
ROOMS_LOCK = threading.RLock()


def get_room(code):
    with ROOMS_LOCK:
        r = ROOMS.get((code or "").strip().upper())
        return r


def create_room(opts=None, private=True, game="remi"):
    with ROOMS_LOCK:
        if len(ROOMS) >= MAX_ROOMS:
            now = time.time()
            for c in [c for c, rr in ROOMS.items() if now - rr.last_activity > 600]:
                ROOMS.pop(c, None)
            if len(ROOMS) >= MAX_ROOMS:
                raise GameError("Serverul este plin. Încearcă din nou peste câteva minute.")
        r = table_engine.TableRoom(opts) if game == "table" else Room(opts)
        r.opts["private"] = private
        while r.code in ROOMS:
            r.code = new_code()
        ROOMS[r.code] = r
    return r


LEADERBOARD_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "leaderboard.json")
LEADERBOARD_LOCK = threading.Lock()


def _load_lb():
    try:
        with open(LEADERBOARD_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except Exception:
        return {}


LEADERBOARD = _load_lb()


def _save_lb():
    try:
        tmp = LEADERBOARD_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(LEADERBOARD, f, ensure_ascii=False)
        os.replace(tmp, LEADERBOARD_FILE)
    except Exception:
        pass


def record_leaderboard(entries):
    if not entries:
        return
    now = int(time.time())
    with LEADERBOARD_LOCK:
        for e in entries:
            name = (e.get("name") or "").strip()[:18]
            if not name:
                continue
            key = name.lower()
            cur = LEADERBOARD.get(key) or {
                "name": name, "avatar": "", "games": 0, "wins": 0, "points": 0, "updated": now
            }
            cur["name"] = name
            if e.get("avatar"):
                cur["avatar"] = e["avatar"][:24000]
            cur["games"] = int(cur.get("games", 0)) + 1
            if e.get("won"):
                cur["wins"] = int(cur.get("wins", 0)) + 1
            cur["points"] = int(cur.get("points", 0)) + max(0, int(e.get("points", 0)))
            cur["updated"] = now
            LEADERBOARD[key] = cur
        _save_lb()


def get_leaderboard_top10():
    with LEADERBOARD_LOCK:
        rows = list(LEADERBOARD.values())
    rows.sort(key=lambda r: (-int(r.get("wins", 0)), -int(r.get("points", 0)), int(r.get("games", 0))))
    out = []
    for r in rows[:10]:
        g = int(r.get("games", 0))
        w = int(r.get("wins", 0))
        out.append({
            "name": r.get("name", "Jucător"),
            "avatar": r.get("avatar", ""),
            "games": g,
            "wins": w,
            "points": int(r.get("points", 0)),
            "winRate": round((w * 100 / g)) if g > 0 else 0,
        })
    return out


def check_room_leaderboard(room):
    kind = getattr(room, "kind", "remi")
    if kind == "table":
        if room.phase == "match_end" and room.match_winner:
            key = f"{room.code}:m:{room.leg}:{room.match_winner}"
            if getattr(room, "_lb_key", None) != key:
                room._lb_key = key
                entries = [
                    {
                        "name": p["name"],
                        "avatar": p.get("avatar", ""),
                        "won": p["id"] == room.match_winner,
                        "points": max(0, int(p.get("score", 0))),
                    }
                    for p in room.players
                ]
                record_leaderboard(entries)
    else:
        if room.phase in ("round_end", "game_over"):
            key = f"{room.code}:r:{room.round_no}"
            if getattr(room, "_lb_key", None) != key:
                room._lb_key = key
                win_pid = room.winner_pid if room.phase == "game_over" else (
                    (room.round_scores or {}).get("closer")
                    or (max(room.players, key=lambda p: p.get("round_score", 0))["id"] if room.players else None)
                )
                entries = [
                    {
                        "name": p["name"],
                        "avatar": p.get("avatar", ""),
                        "won": p["id"] == win_pid,
                        "points": max(0, int(p.get("round_score", 0))),
                    }
                    for p in room.players
                ]
                record_leaderboard(entries)


def cleanup_rooms():
    now = time.time()
    with ROOMS_LOCK:
        dead = [c for c, r in ROOMS.items() if now - r.last_activity > ROOM_IDLE_TIMEOUT]
        for c in dead:
            del ROOMS[c]


def ticker():
    while True:
        try:
            with ROOMS_LOCK:
                rooms = list(ROOMS.values())
            for r in rooms:
                with r.lock:
                    r.tick(time.time())
                    check_room_leaderboard(r)
        except Exception as e:  # pragma: no cover
            print("ticker error:", e, file=sys.stderr)
        time.sleep(0.7)


# ----------------------------------------------------------------------------
#  SERVER HTTP
# ----------------------------------------------------------------------------

APP_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "app", "assets")
APP_DIR = os.path.normpath(APP_DIR)
MIME = {
    ".html": "text/html; charset=utf-8",
    ".js": "application/javascript; charset=utf-8",
    ".css": "text/css; charset=utf-8",
    ".png": "image/png",
    ".svg": "image/svg+xml",
    ".ico": "image/x-icon",
    ".json": "application/json; charset=utf-8",
    ".webmanifest": "application/manifest+json",
}


class Handler(BaseHTTPRequestHandler):
    server_version = "RemiOnline/1.0"
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):  # linistit
        pass

    # ------------------------------------------------------------ helpers
    def _cors(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Max-Age", "86400")

    def _json(self, obj, status=200):
        data = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self._cors()
        self.end_headers()
        self.wfile.write(data)

    def do_OPTIONS(self):
        self.send_response(204)
        self._cors()
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        try:
            parsed = urlparse(self.path)
            path = parsed.path
            qs = parse_qs(parsed.query)
            if path == "/api/state":
                return self.api_state(qs)
            if path == "/health":
                return self._json({"ok": True, "rooms": len(ROOMS), "time": int(time.time())})
            if path == "/api/rooms":
                with ROOMS_LOCK:
                    info = [{"code": r.code, "phase": r.phase, "players": len(r.players),
                             "max": r.opts["max_players"], "game": getattr(r, "kind", "remi")}
                            for r in ROOMS.values()]
                return self._json({"rooms": info})
            if path == "/api/leaderboard":
                return self._json({"top": get_leaderboard_top10()})
            return self.serve_static(path)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:  # pragma: no cover
            try:
                self._json({"error": f"Eroare server: {e}"}, 500)
            except Exception:
                pass

    def do_POST(self):
        try:
            parsed = urlparse(self.path)
            length = int(self.headers.get("Content-Length") or 0)
            if length > MAX_BODY:
                return self._json({"error": "Cerere prea mare."}, 413)
            raw = self.rfile.read(length) if length else b"{}"
            try:
                body = json.loads(raw.decode("utf-8") or "{}")
            except json.JSONDecodeError:
                return self._json({"error": "JSON invalid."}, 400)
            path = parsed.path
            if path == "/api/create":
                return self.api_create(body)
            if path == "/api/join":
                return self.api_join(body)
            if path == "/api/quick":
                return self.api_quick(body)
            if path == "/api/ready":
                return self.api_ready(body)
            if path == "/api/action":
                return self.api_action(body)
            if path == "/api/chat":
                return self.api_chat(body)
            if path == "/api/leave":
                return self.api_leave(body)
            self._json({"error": "Rută necunoscută."}, 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:  # pragma: no cover
            try:
                self._json({"error": f"Eroare server: {e}"}, 500)
            except Exception:
                pass

    # ------------------------------------------------------------- static
    def serve_static(self, path):
        if path in ("/", ""):
            path = "/index.html"
        rel = os.path.normpath(path).lstrip("/")
        full = os.path.join(APP_DIR, rel)
        if not full.startswith(APP_DIR) or not os.path.isfile(full):
            full = os.path.join(APP_DIR, "index.html")
            rel = "index.html"
        with open(full, "rb") as f:
            data = f.read()
        ext = os.path.splitext(full)[1].lower()
        self.send_response(200)
        self.send_header("Content-Type", MIME.get(ext, "application/octet-stream"))
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-cache")
        self._cors()
        self.end_headers()
        self.wfile.write(data)

    # ---------------------------------------------------------------- API
    def _room_from_body(self, body):
        code = (body.get("code") or "").strip().upper()
        token = (body.get("token") or "").strip()
        room = get_room(code)
        if not room:
            raise GameError("Camera nu există sau a fost închisă.")
        p = room.player_by_token(token)
        if not p:
            raise GameError("Nu ești în această cameră (reintră în joc).")
        return room, p

    def api_create(self, body):
        opts = body.get("opts") or {}
        game = (body.get("game") or "remi").lower()
        if game not in ("remi", "table"):
            game = "remi"
        try:
            room = create_room(opts, private=True, game=game)
        except GameError as e:
            return self._json({"error": str(e)}, 503)
        with room.lock:
            try:
                p = room.add_player(body.get("name"), body.get("avatar", ""))
            except GameError as e:
                return self._json({"error": str(e)}, 400)
            return self._json({"code": room.code, "token": p["token"], "pid": p["id"]})

    def api_join(self, body):
        room = get_room(body.get("code"))
        if not room:
            return self._json({"error": "Codul camerei nu este valid."}, 404)
        with room.lock:
            if room.phase != "lobby" and not (body.get("rejoin")):
                return self._json({"error": "Jocul a început deja în această cameră."}, 400)
            try:
                p = room.add_player(body.get("name"), body.get("avatar", ""))
            except GameError as e:
                return self._json({"error": str(e)}, 400)
            return self._json({"code": room.code, "token": p["token"], "pid": p["id"]})

    def api_quick(self, body):
        game = (body.get("game") or "remi").lower()
        if game not in ("remi", "table"):
            game = "remi"
        opts = body.get("opts") or {}
        want_mode = "tabla" if (game == "remi" and str(opts.get("mode", "")).lower() == "tabla") else "etalat"
        with ROOMS_LOCK:
            candidates = [r for r in ROOMS.values()
                          if r.phase == "lobby" and len(r.players) < r.opts["max_players"]
                          and len(r.players) >= 1 and not r.opts.get("private")
                          and getattr(r, "kind", "remi") == game
                          and (game != "remi" or r.opts.get("mode", "etalat") == want_mode)]
        room = None
        if candidates:
            random.shuffle(candidates)
            room = None
            best = max(candidates, key=lambda r: len(r.players))
            if len(best.players) < best.opts["max_players"]:
                room = best
        if room is None:
            room = create_room({"mode": want_mode} if game == "remi" else {}, private=False, game=game)
        with room.lock:
            try:
                p = room.add_player(body.get("name"), body.get("avatar", ""))
            except GameError as e:
                return self._json({"error": str(e)}, 400)
            # in camerele publice pornim automat cand sunt 2+ jucatori
            for x in room.players:
                x["ready"] = True
            room.maybe_start()
            return self._json({"code": room.code, "token": p["token"], "pid": p["id"]})

    def api_ready(self, body):
        try:
            room, p = self._room_from_body(body)
        except GameError as e:
            return self._json({"error": str(e)}, 400)
        with room.lock:
            room.set_ready(p["id"], bool(body.get("ready", True)))
            if body.get("start") and room.players and room.players[0]["id"] == p["id"]:
                with room.lock:
                    if room.phase == "lobby" and len(room.players) >= 2:
                        try:
                            if getattr(room, "kind", "remi") == "table":
                                room.start_match()
                            else:
                                room.start_round()
                        except Exception as e:
                            return self._json({"error": str(e)}, 400)
            else:
                room.maybe_start()
            return self._json({"ok": True})

    def api_action(self, body):
        try:
            room, p = self._room_from_body(body)
        except GameError as e:
            return self._json({"error": str(e)}, 400)
        action = body.get("action") or {}
        pid = p["id"]
        with room.lock:
            try:
                if getattr(room, "kind", "remi") == "table":
                    room.handle_action(pid, action)
                    check_room_leaderboard(room)
                    return self._json({"ok": True, "v": room.version})
                typ = action.get("type")
                if typ == "draw_stock":
                    room._draw_stock(pid)
                elif typ == "draw_discard":
                    room._draw_discard(pid, tile=action.get("tile"))
                elif typ == "meld":
                    room.action_meld(pid, action.get("groups") or [])
                elif typ == "add":
                    room.action_add(pid, action.get("gid"), action.get("tile"))
                elif typ == "swap_joker":
                    room.action_swap_joker(pid, action.get("gid"), action.get("tile"))
                elif typ == "discard":
                    room.action_discard(pid, action.get("tile"))
                elif typ == "close_tabla":
                    room.action_close_tabla(pid, action.get("tile"))
                elif typ == "announce_atu":
                    room.action_announce_atu(pid)
                elif typ == "next_round":
                    room.action_next_round(pid)
                elif typ == "new_game":
                    room.action_new_game(pid)
                elif typ == "update_opts":
                    if room.phase != "lobby":
                        raise GameError("Setările se pot schimba doar în lobby.")
                    if room.players and room.players[0]["id"] != pid:
                        raise GameError("Doar gazda poate schimba setările.")
                    o = action.get("opts") or {}
                    if "max_players" in o:
                        val = max(2, min(4, int(o["max_players"])))
                        if val < len(room.players):
                            raise GameError("Prea mulți jucători în cameră pentru această setare.")
                        room.opts["max_players"] = val
                    if "turn_seconds" in o:
                        room.opts["turn_seconds"] = max(10, min(120, int(o["turn_seconds"])))
                    if "target" in o:
                        room.opts["target"] = max(0, int(o["target"]))
                    if "mode" in o and str(o["mode"]).lower() in ("etalat", "tabla"):
                        room.opts["mode"] = str(o["mode"]).lower()
                    room.add_log("Setările mesei au fost actualizate.")
                    room.bump()
                else:
                    raise GameError("Acțiune necunoscută.")
                check_room_leaderboard(room)
            except GameError as e:
                return self._json({"error": str(e)}, 400)
            except Exception as e:
                return self._json({"error": f"Eroare: {e}"}, 500)
            return self._json({"ok": True, "v": room.version})

    def api_chat(self, body):
        try:
            room, p = self._room_from_body(body)
        except GameError as e:
            return self._json({"error": str(e)}, 400)
        with room.lock:
            room.add_chat(p["id"], p["name"], body.get("text"))
            room.bump()
            return self._json({"ok": True})

    def api_leave(self, body):
        try:
            room, p = self._room_from_body(body)
        except GameError as e:
            return self._json({"error": str(e)}, 400)
        with room.lock:
            room.remove_player(p["id"])
            if not room.players:
                with ROOMS_LOCK:
                    ROOMS.pop(room.code, None)
            return self._json({"ok": True})

    def api_state(self, qs):
        token = (qs.get("token") or [""])[0]
        code = (qs.get("code") or [""])[0]
        try:
            last_v = int((qs.get("v") or ["-1"])[0])
        except ValueError:
            last_v = -1
        room = get_room(code)
        if not room:
            return self._json({"error": "Camera nu există sau a fost închisă."}, 404)
        deadline = time.time() + LONG_POLL_SECONDS
        with room.cond:
            while True:
                p = room.player_by_token(token)
                if not p:
                    return self._json({"error": "Sesiune expirată. Reintră în cameră."}, 401)
                p["connected"] = True
                p["last_seen"] = time.time()
                room.last_activity = time.time()
                if room.version != last_v:
                    snap = room.snapshot(p["id"])
                    payload = {"state": snap, "you": p["id"]}
                    break
                remaining = deadline - time.time()
                if remaining <= 0:
                    snap = room.snapshot(p["id"])
                    payload = {"state": snap, "you": p["id"]}
                    break
                room.cond.wait(timeout=min(remaining, 2.0))
        return self._json(payload)


def main():
    port = 8080
    host = "0.0.0.0"
    args = sys.argv[1:]
    for i, a in enumerate(args):
        if a == "--port" and i + 1 < len(args):
            port = int(args[i + 1])
        if a == "--host" and i + 1 < len(args):
            host = args[i + 1]
    t = threading.Thread(target=ticker, daemon=True)
    t.start()
    def _cleaner():
        while True:
            time.sleep(60)
            cleanup_rooms()
    threading.Thread(target=_cleaner, daemon=True).start()
    srv = ThreadingHTTPServer((host, port), Handler)
    srv.daemon_threads = True
    print(f"🎲 Remi Online rulează pe http://{host}:{port}")
    print(f"    Client: {APP_DIR}")
    print("    Oprire: Ctrl+C")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nLa revedere!")


if __name__ == "__main__":
    main()
