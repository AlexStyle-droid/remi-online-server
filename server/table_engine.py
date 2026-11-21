#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Table (backgammon) — motor de joc pentru Remi Online.
Reguli clasice: 15 piese, zaruri, lovire (blot), bară, scoatere, gammon/backgammon.
Meci in N puncte. 2 jucători reali, sincronizare prin serverul Remi Online.

Punctele sunt numerotate 1..24:
  * alb (jucătorul 0) merge descrescător 24 -> 1 și scoate din 1..6
  * negru (jucătorul 1) merge crescător 1 -> 24 și scoate din 19..24
"""
import random
import secrets
import threading
import time

WHITE, BLACK = 0, 1
COLOR_RO = {WHITE: "alb", BLACK: "negru"}

TURN_SECONDS = 45
LEG_END_DELAY = 8

# poziția de start standard: punct -> (jucător, număr piese)
START = {
    24: (WHITE, 2), 13: (WHITE, 5), 8: (WHITE, 3), 6: (WHITE, 5),
    1: (BLACK, 2), 12: (BLACK, 5), 17: (BLACK, 3), 19: (BLACK, 5),
}


class TableError(Exception):
    pass


def new_code():
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    return "".join(secrets.choice(alphabet) for _ in range(5))


class TableRoom:
    kind = "table"

    def __init__(self, opts=None):
        self.code = new_code()
        self.created = time.time()
        self.last_activity = time.time()
        self.lock = threading.RLock()
        self.cond = threading.Condition(self.lock)
        self.version = 0
        self.opts = {"max_players": 2, "turn_seconds": TURN_SECONDS, "target": 5, "private": True}
        if opts:
            for k in ("turn_seconds", "target"):
                if k in opts:
                    try:
                        self.opts[k] = int(opts[k])
                    except (TypeError, ValueError):
                        pass
        self.opts["turn_seconds"] = max(20, min(120, self.opts["turn_seconds"]))
        self.opts["target"] = max(1, min(21, self.opts["target"]))
        self.opts["max_players"] = 2
        self.players = []
        self.phase = "lobby"          # lobby | playing | leg_end | match_end
        self.turn = WHITE
        self.turn_pid = None
        self.turn_deadline = 0
        self.log = []
        self.chat = []
        self.board = {}
        self.bar = [0, 0]
        self.off = [0, 0]
        self.dice = []
        self.dice_roll = []
        self.leg = 0
        self.last_leg = None
        self.match_winner = None
        self.next_leg_at = 0
        self.last_moves = []

    # ------------------------------------------------------------- utilitare
    def bump(self):
        self.version += 1
        self.last_activity = time.time()
        try:
            self.cond.notify_all()
        except RuntimeError:
            pass

    def add_log(self, txt):
        self.log.append({"t": int(time.time()), "x": txt})
        if len(self.log) > 60:
            self.log = self.log[-60:]

    def add_chat(self, pid, name, text):
        text = (text or "").strip()[:200]
        if not text:
            return
        self.chat.append({"t": int(time.time()), "pid": pid, "name": name, "text": text})
        if len(self.chat) > 60:
            self.chat = self.chat[-60:]

    def player(self, pid):
        for p in self.players:
            if p["id"] == pid:
                return p
        return None

    def player_by_token(self, tok):
        for p in self.players:
            if p["token"] == tok:
                return p
        return None

    def is_full(self):
        return len(self.players) >= 2

    # ------------------------------------------------------------- lobby
    def add_player(self, name, avatar=""):
        name = (name or "").strip()[:18] or "Jucător"
        if self.is_full():
            raise TableError("Masa este plină (2 jucători).")
        names = {p["name"].lower() for p in self.players}
        base, i = name, 2
        while name.lower() in names:
            name = f"{base}{i}"
            i += 1
        av = avatar if isinstance(avatar, str) and len(avatar) <= 24000 else ""
        p = {
            "id": secrets.token_hex(6), "token": secrets.token_hex(24), "name": name,
            "avatar": av,
            "seat": len(self.players), "connected": True, "last_seen": time.time(),
            "ready": False, "score": 0,
        }
        self.players.append(p)
        self.add_log(f"{name} a intrat la masă.")
        self.bump()
        return p

    def set_ready(self, pid, ready=True):
        p = self.player(pid)
        if not p:
            raise TableError("Jucător inexistent.")
        if self.phase != "lobby":
            return
        p["ready"] = bool(ready)
        self.add_log(f"{p['name']} este {'gata' if ready else 'nepregătit'}.")
        self.bump()

    def maybe_start(self):
        if self.phase == "lobby" and len(self.players) == 2 and all(p["ready"] for p in self.players):
            self.start_match()

    # ------------------------------------------------------------- meci/leg
    def start_match(self):
        if len(self.players) != 2:
            raise TableError("Este nevoie de 2 jucători.")
        for p in self.players:
            p["score"] = 0
            p["ready"] = True
        self.leg = 0
        self.match_winner = None
        self.start_leg()

    def start_leg(self):
        self.leg += 1
        self.board = {}
        for pt, (owner, cnt) in START.items():
            self.board[pt] = [owner, cnt]
        self.bar = [0, 0]
        self.off = [0, 0]
        self.dice = []
        self.dice_roll = []
        self.last_moves = []
        self.phase = "playing"
        # cel care începe: alternativ pe leguri
        self.turn = (self.leg - 1) % 2
        self.turn_pid = self.players[self.turn]["id"]
        self.turn_deadline = time.time() + self.opts["turn_seconds"]
        self.add_log(f"— Leg {self.leg} — începe {self.players[self.turn]['name']} ({COLOR_RO[self.turn]})")
        self.bump()

    def _home_points(self, p):
        return range(1, 7) if p == WHITE else range(19, 25)

    def _dir(self, p):
        return -1 if p == WHITE else 1

    def _count_on(self, p, pts):
        n = 0
        for i in pts:
            c = self.board.get(i)
            if c and c[0] == p:
                n += c[1]
        return n

    def _all_home_state(self, board, bar, off, p):
        if bar[p]:
            return False
        pts = self._home_points(p)
        n = sum(board[i][1] for i in pts if i in board and board[i][0] == p)
        return n + off[p] == 15

    def _all_home(self, p):
        return self._all_home_state(self.board, self.bar, self.off, p)

    def _can_land_state(self, board, p, to):
        c = board.get(to)
        if not c:
            return True
        if c[0] == p:
            return True
        return c[1] == 1

    def _can_land(self, p, to):
        return self._can_land_state(self.board, p, to)

    def _legal_for_die_state(self, board, bar, off, p, d, only_from=None):
        out = []
        if bar[p] > 0:
            if only_from is not None and only_from != "bar":
                return out
            to = 25 - d if p == WHITE else d
            if 1 <= to <= 24 and self._can_land_state(board, p, to):
                out.append({"from": "bar", "to": to, "die": d})
            return out
        home = self._all_home_state(board, bar, off, p)
        pts = [only_from] if (isinstance(only_from, int) and 1 <= only_from <= 24) else range(1, 25)
        for i in pts:
            c = board.get(i)
            if not c or c[0] != p:
                continue
            if not home:
                to = i + self._dir(p) * d
                if 1 <= to <= 24 and self._can_land_state(board, p, to):
                    out.append({"from": i, "to": to, "die": d})
            else:
                # în casa proprie se poate muta și normal, nu doar scoate
                to = i + self._dir(p) * d
                if 1 <= to <= 24 and self._can_land_state(board, p, to):
                    out.append({"from": i, "to": to, "die": d})
                dist = i if p == WHITE else (25 - i)
                if d == dist:
                    out.append({"from": i, "to": "off", "die": d})
                elif d > dist:
                    if p == WHITE:
                        further = sum(c2[1] for j, c2 in board.items() if c2[0] == p and j > i)
                    else:
                        further = sum(c2[1] for j, c2 in board.items() if c2[0] == p and j < i)
                    if further == 0:
                        out.append({"from": i, "to": "off", "die": d})
        return out

    def legal_for_die(self, p, d):
        return self._legal_for_die_state(self.board, self.bar, self.off, p, d)

    def _sim_step(self, board, bar, off, p, frm, to):
        hit = 0
        if frm == "bar":
            bar[p] -= 1
        else:
            c = board[frm]
            c[1] -= 1
            if c[1] == 0:
                del board[frm]
        if to == "off":
            off[p] += 1
            return hit
        c = board.get(to)
        if c and c[0] != p:
            bar[c[0]] += 1
            board[to] = [p, 1]
            hit = 1
        elif c:
            c[1] += 1
        else:
            board[to] = [p, 1]
        return hit

    def legal_moves(self, p=None):
        if p is None:
            p = self.turn
        best = {}
        # 1. Mutări cu un singur zar
        for d in sorted(set(self.dice)):
            for mv in self.legal_for_die(p, d):
                key = (mv["from"], mv["to"])
                if key not in best:
                    best[key] = {
                        "from": mv["from"],
                        "to": mv["to"],
                        "die": d,
                        "dice": [d],
                        "path": [mv["to"]],
                    }
        # 2. Mutări combinate ale aceleiași piese (2..N zaruri într-un singur clic)
        if len(self.dice) > 1:
            start_points = sorted({mv["from"] for mv in best.values()}, key=lambda x: (0 if x == "bar" else 1, str(x)))
            dice_avail = list(self.dice)
            # generăm secvențe distincte de zaruri de lungime 2..len(dice_avail)
            combos_by_len = {}
            def gen_seq(used_idx, seq):
                if len(seq) >= 2:
                    combos_by_len.setdefault(len(seq), set()).add(tuple(seq))
                if len(seq) == len(dice_avail):
                    return
                seen_d = set()
                for idx, val in enumerate(dice_avail):
                    if idx in used_idx or val in seen_d:
                        continue
                    seen_d.add(val)
                    used_idx.add(idx)
                    seq.append(val)
                    gen_seq(used_idx, seq)
                    seq.pop()
                    used_idx.remove(idx)
            gen_seq(set(), [])

            for frm in start_points:
                for k in sorted(combos_by_len):
                    best_for_k = {}
                    for seq in sorted(combos_by_len[k]):
                        sim_b = {pt: [c[0], c[1]] for pt, c in self.board.items()}
                        sim_bar = list(self.bar)
                        sim_off = list(self.off)
                        cur = frm
                        path = []
                        inter_hits = 0
                        ok = True
                        for step_i, d in enumerate(seq):
                            if cur == "off":
                                ok = False
                                break
                            cands = self._legal_for_die_state(sim_b, sim_bar, sim_off, p, d, only_from=cur)
                            if not cands:
                                ok = False
                                break
                            # dacă nu e ultimul pas, nu putem scoate piesa înainte de final
                            if step_i < k - 1:
                                cands = [c for c in cands if c["to"] != "off"]
                                if not cands:
                                    ok = False
                                    break
                            chosen = cands[0]
                            h = self._sim_step(sim_b, sim_bar, sim_off, p, cur, chosen["to"])
                            if step_i < k - 1:
                                inter_hits += h
                            cur = chosen["to"]
                            path.append(cur)
                        if not ok:
                            continue
                        key = (frm, cur)
                        if key in best:
                            continue
                        prev = best_for_k.get(key)
                        if prev is None or inter_hits < prev[0]:
                            best_for_k[key] = (inter_hits, {
                                "from": frm,
                                "to": cur,
                                "die": sum(seq),
                                "dice": list(seq),
                                "path": path,
                            })
                    for key, (_, mv) in best_for_k.items():
                        if key not in best:
                            best[key] = mv
        return list(best.values())

    # ------------------------------------------------------------- acțiuni
    def handle_action(self, pid, action):
        typ = (action or {}).get("type")
        if typ == "roll":
            return self.do_roll(pid)
        if typ == "move":
            return self.do_move(pid, action.get("from"), action.get("to"))
        if typ == "next_leg":
            return self.do_next_leg(pid)
        if typ == "new_match":
            return self.do_new_match(pid)
        if typ == "update_opts":
            self.do_update_opts(pid, action.get("opts") or {})
            return {"ok": True}
        raise TableError("Acțiune necunoscută pentru Table.")

    def _turn_player(self, pid):
        p = self.player(pid)
        if not p:
            raise TableError("Jucător inexistent.")
        if self.phase != "playing":
            raise TableError("Jocul nu este în desfășurare.")
        if p["seat"] != self.turn or pid != self.turn_pid:
            raise TableError("Nu este rândul tău.")
        return p

    def do_roll(self, pid):
        self._turn_player(pid)
        if self.dice:
            raise TableError("Ai aruncat deja zarurile.")
        d1, d2 = random.randint(1, 6), random.randint(1, 6)
        self.dice_roll = [d1, d2]
        self.dice = [d1, d1, d2, d2] if d1 == d2 else [d1, d2]
        p = self.player(pid)
        self.add_log(f"{p['name']} a dat {d1}-{d2}.")
        if d1 == d2:
            self.add_log("Dublu! Patru mutări.")
        self.turn_deadline = time.time() + self.opts["turn_seconds"]
        if not self.legal_moves(self.turn):
            self.add_log(f"{p['name']} nu are mutări — predă tura.")
            self._end_turn()
        self.bump()
        return {"ok": True}

    def _remove_die(self, d):
        if d in self.dice:
            self.dice.remove(d)
            return
        # zar mai mare folosit pentru scoatere exactă (teoretic nu ar trebui)
        if self.dice:
            self.dice.pop()

    def do_move(self, pid, frm, to):
        self._turn_player(pid)
        if not self.dice:
            raise TableError("Aruncă zarurile mai întâi.")
        try:
            if frm != "bar":
                frm = int(frm)
            if to != "off":
                to = int(to)
        except (TypeError, ValueError):
            raise TableError("Mutare invalidă.")
        candidates = [mv for mv in self.legal_moves(self.turn)
                      if str(mv["from"]) == str(frm) and str(mv["to"]) == str(to)]
        if not candidates:
            raise TableError("Mutare ilegală.")
        mv = candidates[0]
        steps_dice = mv.get("dice") or [mv["die"]]
        steps_path = mv.get("path") or [to]
        cur_from = frm
        for step_d, step_to in zip(steps_dice, steps_path):
            self._apply_move(self.turn, {"from": cur_from, "to": step_to, "die": step_d})
            self._remove_die(step_d)
            self.last_moves.append({"seat": self.turn, "from": cur_from, "to": step_to})
            cur_from = step_to
        p = self.player(pid)
        if len(self.last_moves) > 6:
            self.last_moves = self.last_moves[-6:]
        if to == "off":
            self.add_log(f"{p['name']} a scos o piesă ({self.off[self.turn]}/15).")
        # verificare câștig
        if self.off[self.turn] == 15:
            self._end_leg(self.turn)
            self.bump()
            return {"ok": True}
        # dacă nu mai există mutări, se încheie tura
        if not self.dice or not self.legal_moves(self.turn):
            self._end_turn()
        self.bump()
        return {"ok": True}

    def _apply_move(self, p, mv):
        frm, to = mv["from"], mv["to"]
        if frm == "bar":
            self.bar[p] -= 1
        else:
            c = self.board.get(frm)
            if not c or c[0] != p:
                raise TableError("Nu ai piesă acolo.")
            c[1] -= 1
            if c[1] == 0:
                del self.board[frm]
        if to == "off":
            self.off[p] += 1
            return
        c = self.board.get(to)
        if c and c[0] != p:
            # lovire
            if c[1] != 1:
                raise TableError("Nu poți lovi o grămadă.")
            self.bar[c[0]] += 1
            self.add_log(f"💥 {self.players[p]['name']} a lovit o piesă {COLOR_RO[c[0]]}.")
            self.board[to] = [p, 1]
        elif c:
            c[1] += 1
        else:
            self.board[to] = [p, 1]

    def _end_turn(self):
        self.dice = []
        self.dice_roll = []
        self.turn = 1 - self.turn
        self.turn_pid = self.players[self.turn]["id"]
        self.turn_deadline = time.time() + self.opts["turn_seconds"]

    def _end_leg(self, winner):
        loser = 1 - winner
        loser_off = self.off[loser]
        if loser_off == 0:
            home = self._home_points(winner)
            trapped = self._count_on(loser, home) > 0 or self.bar[loser] > 0
            pts = 3 if trapped else 2
            kind = "backgammon" if trapped else "gammon"
        else:
            pts = 1
            kind = "simplu"
        self.players[winner]["score"] += pts
        self.last_leg = {
            "leg": self.leg, "winner": self.players[winner]["id"],
            "winner_name": self.players[winner]["name"], "points": pts, "kind": kind,
            "off": [self.off[WHITE], self.off[BLACK]],
            "scores": [self.players[0]["score"], self.players[1]["score"]],
        }
        self.add_log(f"🏆 {self.players[winner]['name']} a câștigat legul ({kind}, {pts}p).")
        target = self.opts.get("target", 5)
        if self.players[winner]["score"] >= target:
            self.phase = "match_end"
            self.match_winner = self.players[winner]["id"]
            self.add_log(f"👑 {self.players[winner]['name']} a câștigat meciul {self.players[winner]['score']}-"
                         f"{self.players[loser]['score']}!")
        else:
            self.phase = "leg_end"
            self.next_leg_at = time.time() + LEG_END_DELAY
        self.dice = []
        self.dice_roll = []

    def do_next_leg(self, pid):
        if self.phase != "leg_end":
            return {"ok": True}
        self.start_leg()
        return {"ok": True}

    def do_new_match(self, pid):
        if self.phase not in ("match_end", "leg_end"):
            return {"ok": True}
        self.start_match()
        return {"ok": True}

    def do_update_opts(self, pid, opts):
        if self.phase != "lobby":
            raise TableError("Setările se schimbă doar în lobby.")
        if self.players and self.players[0]["id"] != pid:
            raise TableError("Doar gazda poate schimba setările.")
        if "target" in opts:
            self.opts["target"] = max(1, min(21, int(opts["target"])))
        if "turn_seconds" in opts:
            self.opts["turn_seconds"] = max(20, min(120, int(opts["turn_seconds"])))
        self.add_log("Setările mesei au fost actualizate.")
        self.bump()

    def remove_player(self, pid, reason="a părăsit jocul"):
        p = self.player(pid)
        if not p:
            return
        self.add_log(f"{p['name']} {reason}.")
        if self.phase == "playing":
            p["connected"] = False
        else:
            self.players = [x for x in self.players if x["id"] != pid]
            for i, x in enumerate(self.players):
                x["seat"] = i
        self.bump()

    # ------------------------------------------------------------- timp
    def handle_timeout(self):
        if self.phase != "playing":
            return
        p = self.player(self.turn_pid)
        if not p:
            return
        self.add_log(f"⏰ {p['name']} a depășit timpul — se joacă automat.")
        if not self.dice:
            try:
                self.do_roll(self.turn_pid)
            except TableError:
                pass
        guard = 0
        while self.dice and guard < 8:
            guard += 1
            moves = self.legal_moves(self.turn)
            if not moves:
                break
            mv = random.choice(moves)
            try:
                self._apply_move(self.turn, mv)
                self._remove_die(mv["die"])
            except TableError:
                break
            if self.off[self.turn] == 15:
                self._end_leg(self.turn)
                return
        if self.phase == "playing":
            self._end_turn()

    def tick(self, now):
        if self.phase == "playing":
            if now >= self.turn_deadline:
                self.handle_timeout()
                self.bump()
        elif self.phase == "leg_end":
            if self.next_leg_at and now >= self.next_leg_at and len(self.players) == 2:
                self.start_leg()

    # ------------------------------------------------------------- snapshot
    def snapshot(self, viewer_pid):
        me = self.player(viewer_pid)
        my_seat = me["seat"] if me else None
        now = time.time()
        board = []
        for pt in range(1, 25):
            c = self.board.get(pt)
            if c:
                board.append({"i": pt, "owner": c[0], "count": c[1]})
        players = []
        for p in self.players:
            players.append({
                "id": p["id"], "name": p["name"], "avatar": p.get("avatar", ""), "seat": p["seat"],
                "connected": p["connected"] and (time.time() - p.get("last_seen", time.time()) < 20),
                "ready": p["ready"], "score": p["score"],
                "off": self.off[p["seat"]], "bar": self.bar[p["seat"]],
                "isTurn": self.phase == "playing" and p["seat"] == self.turn,
            })
        moves = []
        if me and self.phase == "playing" and me["seat"] == self.turn:
            moves = self.legal_moves(self.turn)
        return {
            "v": self.version, "code": self.code, "game": "table", "phase": self.phase,
            "opts": self.opts, "round": self.leg, "leg": self.leg,
            "players": players,
            "turnPid": self.turn_pid,
            "turnSeat": self.turn,
            "turnLeft": int(max(0, self.turn_deadline - now)) if self.phase == "playing" else 0,
            "turnSeconds": self.opts["turn_seconds"],
            "board": board, "bar": self.bar, "off": self.off,
            "dice": list(self.dice), "diceRoll": list(self.dice_roll),
            "mySeat": my_seat,
            "myTurn": bool(me and self.phase == "playing" and me["seat"] == self.turn),
            "canRoll": bool(me and self.phase == "playing" and me["seat"] == self.turn and not self.dice),
            "legalMoves": moves,
            "lastLeg": self.last_leg,
            "matchWinner": self.match_winner,
            "nextLegIn": int(max(0, self.next_leg_at - now)) if self.phase == "leg_end" else 0,
            "log": self.log[-20:],
            "chat": self.chat[-30:],
            "hostPid": self.players[0]["id"] if self.players else None,
        }
