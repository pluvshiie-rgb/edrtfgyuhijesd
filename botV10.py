import discord
from discord.ext import commands, tasks
import json
import os
import asyncio
import random
import logging
import traceback
import time
from datetime import datetime, timedelta, timezone
import re
from collections import defaultdict
from io import BytesIO
import sys

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler()]
)
log = logging.getLogger("bot")

# ─────────────────────────────────────────
#  Configuration
# ─────────────────────────────────────────
PREFIX = "+"
TOKEN = os.getenv("DISCORD_TOKEN", "")

intents = discord.Intents.default()
intents.members = True
intents.message_content = True
intents.guilds = True
intents.presences = True   # OBLIGATOIRE pour que +stats connaisse le vrai statut (en ligne/hors ligne) des membres
intents.voice_states = True  # déjà inclus par default(), explicite ici pour la lisibilité (compte les membres en vocal)

bot = commands.Bot(command_prefix=PREFIX, intents=intents, help_command=None)

# ─────────────────────────────────────────
#  Persistance (fichiers JSON)
# ─────────────────────────────────────────
WARNS_FILE       = "warns.json"
CONFIG_FILE      = "config.json"
GIVEAWAY_FILE    = "giveaways.json"
TEMPBAN_FILE     = "tempbans.json"
MARRIAGES_FILE   = "marriages.json"
TEMPROLES_FILE   = "temproles.json"
TICKETS_FILE     = "tickets.json"
RREACTIONS_FILE  = "reaction_roles.json"
STATSVOC_FILE    = "statsvoc.json"
TEMPVOICE_FILE   = "tempvoice.json"
INVCOUNT_FILE    = "invite_counts.json"

def load_json(path):
    if not os.path.exists(path):
        return {}
    with open(path, "r", encoding="utf-8") as f:
        try:
            return json.load(f)
        except json.JSONDecodeError:
            return {}

def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

warns_db       = load_json(WARNS_FILE)
config_db      = load_json(CONFIG_FILE)
giveaway_db    = load_json(GIVEAWAY_FILE)
tempban_db     = load_json(TEMPBAN_FILE)
marriages_db   = load_json(MARRIAGES_FILE)
temproles_db   = load_json(TEMPROLES_FILE)
tickets_db     = load_json(TICKETS_FILE)
rreactions_db  = load_json(RREACTIONS_FILE)
statsvoc_db    = load_json(STATSVOC_FILE)
tempvoice_db   = load_json(TEMPVOICE_FILE)   # { channel_id(str): {"owner": id, "guild": id} }
invcount_db    = load_json(INVCOUNT_FILE)    # { guild_id(str): {inviter_id(str): count} }

def save_warns():       save_json(WARNS_FILE, warns_db)
def save_config():      save_json(CONFIG_FILE, config_db)
def save_giveaways():   save_json(GIVEAWAY_FILE, giveaway_db)
def save_tempbans():    save_json(TEMPBAN_FILE, tempban_db)
def save_marriages():   save_json(MARRIAGES_FILE, marriages_db)
def save_temproles():   save_json(TEMPROLES_FILE, temproles_db)
def save_tickets():     save_json(TICKETS_FILE, tickets_db)
def save_rreactions():  save_json(RREACTIONS_FILE, rreactions_db)
def save_statsvoc():    save_json(STATSVOC_FILE, statsvoc_db)
def save_tempvoice():   save_json(TEMPVOICE_FILE, tempvoice_db)
def save_invcount():    save_json(INVCOUNT_FILE, invcount_db)

def get_guild_cfg(guild_id: int) -> dict:
    key = str(guild_id)
    if key not in config_db:
        config_db[key] = {}
    return config_db[key]

def get_invcount_cfg(guild_id: int) -> dict:
    key = str(guild_id)
    if key not in invcount_db:
        invcount_db[key] = {}
    return invcount_db[key]

# ─────────────────────────────────────────
#  Mémoire en RAM
# ─────────────────────────────────────────
_spam_tracker: dict[int, dict[int, list]] = defaultdict(lambda: defaultdict(list))
_snipe_cache:  dict[int, dict[int, list]] = defaultdict(lambda: defaultdict(list))
_flood_cache:  dict[tuple, list]          = defaultdict(list)
_bot_stats = {
    "commands_used": 0,
    "automod_actions": 0,
    "messages_today": 0,
    "members_joined_week": 0,
}

# ── Suivi des stats membres (messages + temps vocal) ─────────────────────────
# Structure : { guild_id: { member_id: { "messages": int, "voice_seconds": float, "voice_joined": float|None } } }
_member_stats: dict[int, dict[int, dict]] = defaultdict(lambda: defaultdict(lambda: {"messages": 0, "voice_seconds": 0.0, "voice_joined": None}))
SNIPE_MAX_AGE     = timedelta(days=3)
SNIPE_MAX_PER_USER = 25
_start_time = datetime.now(timezone.utc)
_startup_tasks_launched = False  # évite de relancer resume_tempbans/check_temproles à chaque reconnexion

# ── Salons vocaux temporaires ("Rejoindre pour créer") ───────────────────────
# Structure : { channel_id(int): {"owner": member_id, "guild": guild_id} }
_temp_voice: dict[int, dict] = {}

# ── Cache des invitations (pour retrouver qui a invité qui) ──────────────────
# Structure : { guild_id(int): {invite_code(str): uses(int)} }
_invite_cache: dict[int, dict[str, int]] = {}
# Cache séparé pour l'invitation vanity (URL personnalisée), car elle n'apparaît
# pas dans guild.invites()
_vanity_cache: dict[int, int] = {}

# Recharger les salons vocaux temporaires connus depuis le disque (survit à un redémarrage)
for _cid, _rec in tempvoice_db.items():
    try:
        _temp_voice[int(_cid)] = {"owner": int(_rec["owner"]), "guild": int(_rec["guild"])}
    except (KeyError, ValueError, TypeError):
        pass

# ─────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────
def parse_duration(text: str):
    units = {"s": 1, "m": 60, "h": 3600, "d": 86400}
    m = re.fullmatch(r"(\d+)([smhd])", text.strip().lower())
    if not m:
        return None
    return timedelta(seconds=int(m.group(1)) * units[m.group(2)])

def format_duration(td: timedelta) -> str:
    total = int(td.total_seconds())
    if total >= 86400:
        return f"{total // 86400}j {(total % 86400) // 3600}h"
    elif total >= 3600:
        return f"{total // 3600}h {(total % 3600) // 60}m"
    elif total >= 60:
        return f"{total // 60}m {total % 60}s"
    return f"{total}s"

async def send_log(guild: discord.Guild, embed: discord.Embed):
    cfg = get_guild_cfg(guild.id)
    ch_id = cfg.get("log_channel")
    if ch_id:
        ch = guild.get_channel(int(ch_id))
        if ch:
            try:
                await ch.send(embed=embed)
            except discord.Forbidden:
                pass

async def send_invite_check(guild: discord.Guild, text: str):
    """Envoie une ligne de suivi d'invitations dans le salon configuré via +setinvitecheck
    (style 'Invite-Check' : qui a invité qui, invitations vanity, arrivées OAuth)."""
    cfg = get_guild_cfg(guild.id)
    ch_id = cfg.get("invite_log_channel")
    if not ch_id:
        return
    ch = guild.get_channel(int(ch_id))
    if not ch:
        return
    try:
        await ch.send(text)
    except (discord.Forbidden, discord.HTTPException):
        pass

def mod_embed(title, description, color=discord.Color.red()):
    return discord.Embed(
        title=title,
        description=description,
        color=color,
        timestamp=datetime.now(timezone.utc)
    )

def success_embed(title, description):
    return mod_embed(title, description, discord.Color.from_rgb(0, 0, 0))

def info_embed(title, description):
    return mod_embed(title, description, discord.Color.from_rgb(0, 0, 0))

def warning_embed(title, description):
    return mod_embed(title, description, discord.Color.yellow())

def check_hierarchy(ctx, member: discord.Member) -> bool:
    return ctx.author.top_role > member.top_role and ctx.guild.me.top_role > member.top_role

async def get_audit_executor(guild: discord.Guild, action: discord.AuditLogAction, target_id: int = None, within_seconds: int = 5) -> discord.Member | discord.User | None:
    """Récupère l'auteur d'une action via les logs d'audit Discord.
    Retourne None si les permissions manquent ou si aucune entrée récente ne correspond."""
    try:
        limit = 5
        async for entry in guild.audit_logs(limit=limit, action=action):
            age = (datetime.now(timezone.utc) - entry.created_at).total_seconds()
            if age > within_seconds:
                break
            if target_id is None:
                return entry.user
            target = entry.target
            # Le target peut être un objet Guild, User, Role, Channel, etc.
            target_eid = getattr(target, "id", None)
            if target_eid is None or target_eid == target_id:
                return entry.user
    except discord.Forbidden:
        pass
    except Exception:
        pass
    return None

async def refresh_invite_cache(guild: discord.Guild):
    """(Re)construit le cache local des invitations d'un serveur (codes -> nb d'utilisations).
    Nécessaire pour détecter quelle invitation a été utilisée lors d'une arrivée."""
    try:
        invites = await guild.invites()
    except (discord.Forbidden, discord.HTTPException):
        return
    _invite_cache[guild.id] = {inv.code: (inv.uses or 0) for inv in invites}
    try:
        if guild.features and "VANITY_URL" in guild.features:
            vanity = await guild.vanity_invite()
            if vanity:
                _vanity_cache[guild.id] = vanity.uses or 0
    except (discord.Forbidden, discord.HTTPException, discord.NotFound):
        pass

async def find_used_invite(guild: discord.Guild):
    """Compare le cache précédent au nouvel état pour trouver l'invitation utilisée.
    Retourne un tuple (invite_ou_None, est_vanity: bool)."""
    old_cache = _invite_cache.get(guild.id, {})
    old_vanity = _vanity_cache.get(guild.id)

    try:
        new_invites = await guild.invites()
    except (discord.Forbidden, discord.HTTPException):
        return None, False

    used_invite = None
    for inv in new_invites:
        old_uses = old_cache.get(inv.code, 0)
        if (inv.uses or 0) > old_uses:
            used_invite = inv
            break

    # Met à jour le cache tout de suite pour la prochaine arrivée
    _invite_cache[guild.id] = {inv.code: (inv.uses or 0) for inv in new_invites}

    if used_invite:
        return used_invite, False

    # Sinon, on vérifie l'invitation vanity (URL personnalisée du serveur)
    if guild.features and "VANITY_URL" in guild.features:
        try:
            vanity = await guild.vanity_invite()
        except (discord.Forbidden, discord.HTTPException, discord.NotFound):
            vanity = None
        if vanity:
            new_uses = vanity.uses or 0
            _vanity_cache[guild.id] = new_uses
            if old_vanity is not None and new_uses > old_vanity:
                return None, True

    return None, False

# ─────────────────────────────────────────
#  Automod — Configuration par défaut
# ─────────────────────────────────────────
AUTOMOD_DEFAULTS = {
    "enabled":           False,
    "anti_links":        False,
    "anti_invites":      False,
    "anti_spam":         False,
    "anti_caps":         False,
    "anti_mentions":     False,
    "anti_badwords":     False,
    "anti_zalgo":        False,
    "anti_flood":        False,
    "anti_scam":         False,   # détecte les liens de scam connus
    "anti_emoji":        False,   # NOUVEAU : trop d'emojis dans un même message
    "anti_attachments":  False,   # NOUVEAU : trop de pièces jointes dans un même message
    "anti_newlines":     False,   # NOUVEAU : trop de retours à la ligne (spam vertical)
    "spam_threshold":    5,
    "spam_interval":     5,
    "caps_percent":      70,
    "caps_min_length":   10,
    "max_mentions":      5,
    "max_emojis":        10,      # NOUVEAU : nb max d'emojis autorisés par message
    "max_attachments":   5,       # NOUVEAU : nb max de pièces jointes par message
    "max_newlines":      10,      # NOUVEAU : nb max de retours à la ligne par message
    "badwords":          [],
    "flood_count":       3,
    "action":            "delete",
    "mute_duration":     "10m",
    "exempt_roles":      [],
    "exempt_channels":   [],
    "log_automod":       True,
    "warn_threshold":    0,       # nb warns avant action auto (0 = désactivé)
    "warn_action":       "mute",  # action déclenchée au seuil
    "warn_action_dur":   "1h",    # durée si l'action est mute/tempban
    "whitelist_domains": [],      # domaines autorisés malgré anti_links
}

# Pattern de détection d'emojis (unicode + emojis custom Discord <:nom:id>)
EMOJI_PATTERN = re.compile(
    r"<a?:\w+:\d+>|[\U0001F300-\U0001FAFF\U00002600-\U000027BF\U0001F1E6-\U0001F1FF]"
)

# Patterns scam connus
SCAM_PATTERNS = [
    re.compile(r"free\s*(nitro|discord\s*nitro)", re.IGNORECASE),
    re.compile(r"claim\s*your\s*(free|gift)", re.IGNORECASE),
    re.compile(r"steam\s*gift", re.IGNORECASE),
]

def get_automod_cfg(guild_id: int) -> dict:
    cfg = get_guild_cfg(guild_id)
    if "automod" not in cfg:
        cfg["automod"] = dict(AUTOMOD_DEFAULTS)
    else:
        for k, v in AUTOMOD_DEFAULTS.items():
            if k not in cfg["automod"]:
                cfg["automod"][k] = v
    return cfg["automod"]

# Patterns de détection
# Anti-liens : exclut les GIFs tenor/giphy, les liens tenor.com et giphy.com, et les attachments Discord
URL_PATTERN     = re.compile(r"https?://\S+|www\.\S+|\S+\.\S{2,}/\S*", re.IGNORECASE)
GIF_WHITELIST   = re.compile(
    r"https?://(tenor\.com|giphy\.com|media\.tenor\.com|i\.giphy\.com|cdn\.discordapp\.com|media\.discordapp\.net)\S*",
    re.IGNORECASE
)
INVITE_PATTERN  = re.compile(r"discord\.gg/\S+|discord\.com/invite/\S+|discordapp\.com/invite/\S+", re.IGNORECASE)
ZALGO_PATTERN   = re.compile(r"[\u0300-\u036f\u0489\u1dc0-\u1dff\u20d0-\u20ff\ufe20-\ufe2f]{3,}")

def has_non_gif_link(content: str, whitelist_domains: list) -> bool:
    """Retourne True si le message contient un lien qui n'est PAS un GIF autorisé."""
    for match in URL_PATTERN.finditer(content):
        url = match.group(0)
        # Exempter les GIFs
        if GIF_WHITELIST.match(url):
            continue
        # Exempter les domaines whitelist configurés
        if any(domain.lower() in url.lower() for domain in whitelist_domains):
            continue
        return True
    return False

async def automod_action(message: discord.Message, reason: str, am_cfg: dict):
    """Effectue l'action configurée après détection d'une infraction."""
    global _bot_stats
    _bot_stats["automod_actions"] += 1

    guild  = message.guild
    member = message.author
    action = am_cfg.get("action", "delete")

    try:
        await message.delete()
    except (discord.Forbidden, discord.NotFound):
        pass

    try:
        await message.channel.send(
            embed=warning_embed("🤖 AutoMod", f"{member.mention} — {reason}"),
            delete_after=6
        )
    except discord.Forbidden:
        pass

    if action == "warn":
        gid, uid = str(guild.id), str(member.id)
        entry = {"reason": f"[AutoMod] {reason}", "date": datetime.now(timezone.utc).isoformat(), "mod": str(bot.user.id)}
        warns_db.setdefault(gid, {}).setdefault(uid, []).append(entry)
        save_warns()
        count = len(warns_db[gid][uid])
        # Paliers fixes : 3 warns = mute 1j, 5 warns = bl
        await apply_warn_milestones(guild, member, count)
        # Vérifier le seuil de warns configurable (optionnel, désactivé par défaut)
        await check_warn_threshold(guild, member, am_cfg)

    elif action == "mute":
        duration = am_cfg.get("mute_duration", "10m")
        delta    = parse_duration(duration) or timedelta(minutes=10)
        until    = datetime.now(timezone.utc) + delta
        try:
            await member.timeout(until, reason=f"[AutoMod] {reason}")
        except discord.Forbidden:
            pass

    elif action == "kick":
        try:
            await member.kick(reason=f"[AutoMod] {reason}")
        except discord.Forbidden:
            pass

    elif action == "ban":
        try:
            await member.ban(reason=f"[AutoMod] {reason}", delete_message_days=1)
        except discord.Forbidden:
            pass

    if am_cfg.get("log_automod", True):
        e = mod_embed(
            "🤖 AutoMod — Infraction",
            f"**Membre :** {member.mention} (`{member.id}`)\n"
            f"**Raison :** {reason}\n"
            f"**Action :** {action}\n"
            f"**Salon :** {message.channel.mention}\n"
            f"**Message :** ```{message.content[:300] or '[vide]'}```",
            discord.Color.orange()
        )
        await send_log(guild, e)

async def check_warn_threshold(guild: discord.Guild, member: discord.Member, am_cfg: dict):
    """Applique une action automatique si le membre dépasse le seuil de warns."""
    threshold = am_cfg.get("warn_threshold", 0)
    if threshold <= 0:
        return
    gid, uid = str(guild.id), str(member.id)
    count = len(warns_db.get(gid, {}).get(uid, []))
    if count < threshold:
        return

    action   = am_cfg.get("warn_action", "mute")
    dur_str  = am_cfg.get("warn_action_dur", "1h")
    delta    = parse_duration(dur_str) or timedelta(hours=1)

    reason = f"Seuil de {threshold} warns atteint ({count} warns)"

    if action == "mute":
        until = datetime.now(timezone.utc) + delta
        try:
            await member.timeout(until, reason=reason)
        except discord.Forbidden:
            pass
    elif action == "kick":
        try:
            await member.kick(reason=reason)
        except discord.Forbidden:
            pass
    elif action == "ban":
        try:
            await member.ban(reason=reason, delete_message_days=1)
        except discord.Forbidden:
            pass
    elif action == "tempban":
        until_ts = int((datetime.now(timezone.utc) + delta).timestamp())
        try:
            await member.ban(reason=reason, delete_message_days=1)
            gid_str = str(guild.id)
            tempban_db.setdefault(gid_str, {})[uid] = {
                "end_ts": until_ts, "reason": reason, "mod_id": str(bot.user.id)
            }
            save_tempbans()
        except discord.Forbidden:
            pass

    e = mod_embed(
        "⚠️ Seuil de warns atteint",
        f"**Membre :** {member.mention} (`{member.id}`)\n"
        f"**Warns :** {count}/{threshold}\n"
        f"**Action automatique :** {action}" +
        (f" ({dur_str})" if action in ("mute", "tempban") else ""),
        discord.Color.dark_orange()
    )
    await send_log(guild, e)

async def apply_warn_milestones(guild: discord.Guild, member: discord.Member, count: int):
    """Système de paliers de warns fixe :
    - 3 warns  -> mute (timeout) 1 jour
    - 5 warns  -> blacklist (ban) définitif
    """
    reason = f"Palier de {count} avertissement(s) atteint"

    if count == 5:
        try:
            await member.send(embed=mod_embed(
                "⛔ Tu as été blacklist (bl)",
                f"**Serveur :** {guild.name}\n**Raison :** {reason}"
            ))
        except Exception:
            pass
        try:
            await member.ban(reason=f"[AUTO-WARN] {reason}", delete_message_days=1)
        except discord.Forbidden:
            pass
        else:
            e = mod_embed(
                "⛔ Blacklist automatique (5 warns)",
                f"**Membre :** {member.mention} (`{member.id}`)\n"
                f"**Warns :** {count}\n"
                f"**Action :** Blacklist (bl) définitive",
                discord.Color.dark_red()
            )
            await send_log(guild, e)

    elif count == 3:
        delta = timedelta(days=1)
        until = datetime.now(timezone.utc) + delta
        try:
            await member.send(embed=mod_embed(
                "🔇 Tu as été mute",
                f"**Serveur :** {guild.name}\n**Durée :** 1 jour\n**Raison :** {reason}",
                discord.Color.orange()
            ))
        except Exception:
            pass
        try:
            await member.timeout(until, reason=f"[AUTO-WARN] {reason}")
        except discord.Forbidden:
            pass
        else:
            e = mod_embed(
                "🔇 Mute automatique (3 warns)",
                f"**Membre :** {member.mention} (`{member.id}`)\n"
                f"**Warns :** {count}\n"
                f"**Durée :** 1 jour\n"
                f"**Fin :** <t:{int(until.timestamp())}:R>",
                discord.Color.orange()
            )
            await send_log(guild, e)

def is_exempt(message: discord.Message, am_cfg: dict) -> bool:
    member = message.author
    if member.guild_permissions.administrator:
        return True
    exempt_roles    = [int(r) for r in am_cfg.get("exempt_roles", [])]
    exempt_channels = [int(c) for c in am_cfg.get("exempt_channels", [])]
    if message.channel.id in exempt_channels:
        return True
    for role in member.roles:
        if role.id in exempt_roles:
            return True
    return False

# ─────────────────────────────────────────
#  Événements
# ─────────────────────────────────────────
@bot.event
async def on_ready():
    global _startup_tasks_launched
    print(f"✅ Connecté en tant que {bot.user} (ID: {bot.user.id})")
    print(f"   Préfixe : {PREFIX}")
    if not check_giveaways.is_running():
        check_giveaways.start()
    # resume_tempbans et check_temproles sont des tâches "count=1" (une seule
    # exécution au démarrage). on_ready peut se déclencher plusieurs fois
    # (reconnexions gateway) : sans ce verrou, ces tâches seraient relancées
    # à chaque reconnexion et reprogrammeraient en double les unbans / retraits
    # de rôles temporaires déjà planifiés (bug corrigé).
    if not _startup_tasks_launched:
        _startup_tasks_launched = True
        if not resume_tempbans.is_running():
            resume_tempbans.start()
        if not check_temproles.is_running():
            check_temproles.start()
        # BUG CORRIGÉ : register_ticket_views() n'était jamais appelée. Sans ça,
        # les menus déroulants/boutons des panneaux de tickets cessaient de
        # répondre après chaque redémarrage du bot (vue non persistante ré-attachée).
        register_ticket_views()
        register_rolepanel_views()
    if not update_statsvoc_loop.is_running():
        update_statsvoc_loop.start()
    await bot.change_presence(activity=discord.Activity(
        type=discord.ActivityType.watching, name=f"{PREFIX}help · modération"))

    # ── Initialiser voice_joined pour les membres déjà en vocal au démarrage ──
    now_ts = time.time()
    for guild in bot.guilds:
        for vc in guild.voice_channels:
            for member in vc.members:
                if not member.bot:
                    _member_stats[guild.id][member.id]["voice_joined"] = now_ts

    # ── Construire le cache des invitations (Invite-Check) ────────────────
    for guild in bot.guilds:
        await refresh_invite_cache(guild)

@bot.event
async def on_command(ctx):
    _bot_stats["commands_used"] += 1

@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.MissingRequiredArgument):
        await ctx.reply(f"❌ Argument manquant. Tape `{PREFIX}help {ctx.command}` pour l'aide.")
    elif isinstance(error, commands.MissingPermissions):
        await ctx.reply("❌ Tu n'as pas la permission d'utiliser cette commande.")
    elif isinstance(error, commands.BotMissingPermissions):
        await ctx.reply("❌ Je n'ai pas les permissions nécessaires.")
    elif isinstance(error, commands.MemberNotFound):
        await ctx.reply("❌ Membre introuvable.")
    elif isinstance(error, commands.BadArgument):
        await ctx.reply("❌ Argument invalide.")
    elif isinstance(error, commands.CommandOnCooldown):
        await ctx.reply(f"⏳ Attends encore `{error.retry_after:.1f}s`.")
    elif isinstance(error, commands.CheckFailure):
        pass
    elif isinstance(error, commands.CommandNotFound):
        pass
    else:
        log.error(f"Erreur non gérée dans '{ctx.command}': {traceback.format_exc()}")
        try:
            await ctx.reply("❌ Une erreur interne est survenue. Réessaie plus tard.")
        except discord.Forbidden:
            pass

@bot.event
async def on_member_join(member):
    # ── Anti-bot : expulse tout bot ajouté sauf par le propriétaire du serveur ──
    if member.bot:
        guild = member.guild
        owner_id = guild.owner_id  # seul le propriétaire (couronne) est autorisé

        # Récupérer qui a ajouté le bot via les logs d'audit
        inviter_id = None
        try:
            async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.bot_add):
                if entry.target and entry.target.id == member.id:
                    inviter_id = entry.user.id if entry.user else None
                    break
        except discord.Forbidden:
            pass

        # Si le bot n'a pas été ajouté par le propriétaire → expulsion du bot + de l'inviteur
        if inviter_id != owner_id:
            # 1) Expulser le bot
            try:
                await member.kick(reason="[Anti-Bot] Seul le propriétaire du serveur peut ajouter des bots.")
            except discord.Forbidden:
                pass

            # 2) Expulser l'inviteur s'il est encore dans le serveur
            inviter_member = guild.get_member(inviter_id) if inviter_id else None
            inviter_kicked = False
            if inviter_member:
                try:
                    await inviter_member.kick(reason="[Anti-Bot] A ajouté un bot sans autorisation du propriétaire.")
                    inviter_kicked = True
                except discord.Forbidden:
                    pass

            # 3) Log de l'action
            inviter_info = f"<@{inviter_id}> (`{inviter_id}`)" if inviter_id else "Inconnu"
            kick_status  = "✅ Expulsé" if inviter_kicked else "❌ Non expulsé (permissions insuffisantes)"
            e = mod_embed(
                "🤖 Anti-Bot — Bot + Inviteur expulsés",
                f"**Bot expulsé :** {member} (`{member.id}`)\n"
                f"**Ajouté par :** {inviter_info}\n"
                f"**Inviteur expulsé :** {kick_status}\n"
                f"**Raison :** Seul le propriétaire du serveur peut ajouter des bots.",
                discord.Color.red()
            )
            await send_log(guild, e)
            return  # on arrête ici, pas de rôle auto ni de welcome pour un bot expulsé

        # ── Bot autorisé (ajouté par le propriétaire) : log Invite-Check "OAuth" ──
        await send_invite_check(guild, f"**{member}** joined using OAuth.")

    _bot_stats["members_joined_week"] += 1
    cfg = get_guild_cfg(member.guild.id)
    auto_role_id = cfg.get("auto_role")
    if auto_role_id:
        role = member.guild.get_role(int(auto_role_id))
        if role:
            try:
                await member.add_roles(role, reason="Auto-rôle à l'arrivée")
            except discord.Forbidden:
                pass

    # ── Invite-Check : détecter quelle invitation a été utilisée (membres humains) ──
    if not member.bot:
        used_invite, is_vanity = await find_used_invite(member.guild)
        if is_vanity:
            await send_invite_check(member.guild, f"{member.mention} joined using a vanity invite.")
        elif used_invite and used_invite.inviter:
            inv_cfg = get_invcount_cfg(member.guild.id)
            uid_key = str(used_invite.inviter.id)
            inv_cfg[uid_key] = inv_cfg.get(uid_key, 0) + 1
            save_invcount()
            count = inv_cfg[uid_key]
            await send_invite_check(
                member.guild,
                f"{member.mention} has been invited by **{used_invite.inviter}** and has now **{count}** invites."
            )
        else:
            await send_invite_check(member.guild, f"{member.mention} joined the server.")

    welcome_ch_id = cfg.get("welcome_channel")
    welcome_msg   = cfg.get("welcome_message", "Bienvenue {mention} sur **{server}** !")
    welcome_title = cfg.get("welcome_title", "Bienvenue sur le serveur !")
    welcome_image = cfg.get("welcome_image")
    if welcome_ch_id:
        ch = member.guild.get_channel(int(welcome_ch_id))
        if ch:
            def _fill(txt: str) -> str:
                return (txt.replace("{mention}", member.mention)
                           .replace("{server}", member.guild.name)
                           .replace("{name}", str(member))
                           .replace("{number}", str(member.guild.member_count)))
            e = discord.Embed(
                title=_fill(welcome_title) if welcome_title else None,
                description=_fill(welcome_msg),
                color=discord.Color.from_rgb(0, 0, 0),
                timestamp=datetime.now(timezone.utc)
            )
            if welcome_image:
                e.set_image(url=welcome_image)
            try:
                await ch.send(embed=e)
            except discord.Forbidden:
                pass

    # Log d'arrivée détaillé
    log_ch_id = cfg.get("log_channel")
    if log_ch_id:
        log_ch = member.guild.get_channel(int(log_ch_id))
        if log_ch:
            account_age = datetime.now(timezone.utc) - member.created_at
            days = account_age.days
            new_account_warning = "\n⚠️ **Compte récent (moins de 7 jours) !**" if days < 7 else ""
            e = success_embed(
                "👋 Nouveau membre",
                f"**Membre :** {member.mention} (`{member.id}`)\n"
                f"**Compte créé :** <t:{int(member.created_at.timestamp())}:R> ({days} jours)\n"
                f"**Membres total :** {member.guild.member_count}"
                + new_account_warning
            )
            e.set_thumbnail(url=member.display_avatar.url)
            try:
                await log_ch.send(embed=e)
            except discord.Forbidden:
                pass

@bot.event
async def on_member_remove(member):
    # Ne pas logger la suppression des bots (déjà géré par l'anti-bot)
    if member.bot:
        return
    cfg = get_guild_cfg(member.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = member.guild.get_channel(int(ch_id))
    if not ch:
        return
    roles = [r.mention for r in member.roles if r.name != "@everyone"]

    # Vérifier si c'est un kick via les logs d'audit
    kicker = await get_audit_executor(member.guild, discord.AuditLogAction.kick, member.id, within_seconds=5)
    if kicker:
        e = mod_embed(
            "👢 Membre expulsé (kick)",
            f"**Membre :** {member} (`{member.id}`)\n"
            f"**Expulsé par :** {kicker.mention} (`{kicker.id}`)\n"
            f"**Rejoint le :** {f'<t:{int(member.joined_at.timestamp())}:R>' if member.joined_at else 'Inconnu'}\n"
            f"**Rôles :** {', '.join(roles) if roles else 'Aucun'}",
            discord.Color.orange()
        )
    else:
        e = info_embed(
            "👋 Membre parti",
            f"**Membre :** {member} (`{member.id}`)\n"
            f"**Rejoint le :** {f'<t:{int(member.joined_at.timestamp())}:R>' if member.joined_at else 'Inconnu'}\n"
            f"**Rôles :** {', '.join(roles) if roles else 'Aucun'}"
        )
    e.set_thumbnail(url=member.display_avatar.url)
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_message_delete(message: discord.Message):
    if not message.guild or message.author.bot:
        return
    if not message.content and not message.attachments:
        return
    gid = message.guild.id
    uid = message.author.id
    data = {
        "content":     message.content[:1900],
        "channel_id":  message.channel.id,
        "author_id":   message.author.id,
        "created_at":  datetime.now(timezone.utc).isoformat(),
        "attachments": [a.url for a in message.attachments[:5]]
    }
    _snipe_cache[gid][uid].append(data)
    _snipe_cache[gid][uid] = _snipe_cache[gid][uid][-SNIPE_MAX_PER_USER:]
    now = datetime.now(timezone.utc)
    for user_id in list(_snipe_cache[gid].keys()):
        filtered = []
        for entry in _snipe_cache[gid][user_id]:
            try:
                ts = datetime.fromisoformat(entry["created_at"])
                if now - ts <= SNIPE_MAX_AGE:
                    filtered.append(entry)
            except Exception:
                pass
        if filtered:
            _snipe_cache[gid][user_id] = filtered
        else:
            _snipe_cache[gid].pop(user_id, None)

    # Log suppression dans le salon de logs
    cfg = get_guild_cfg(gid)
    ch_id = cfg.get("log_channel")
    if ch_id:
        ch = message.guild.get_channel(int(ch_id))
        if ch:
            # Tenter de trouver qui a supprimé le message via les logs d'audit
            deleter = await get_audit_executor(message.guild, discord.AuditLogAction.message_delete, message.author.id, within_seconds=5)
            deleter_str = f"\n**Supprimé par :** {deleter.mention} (`{deleter.id}`)" if deleter and deleter.id != message.author.id else ""
            desc = (
                f"**Auteur :** {message.author.mention} (`{message.author.id}`)\n"
                f"**Salon :** {message.channel.mention}"
                + deleter_str +
                f"\n**Contenu :** {message.content[:900] or '[vide]'}"
            )
            if message.attachments:
                desc += f"\n**Pièces jointes :** {', '.join(a.url for a in message.attachments[:3])}"
            e = mod_embed("🗑️ Message supprimé", desc, discord.Color.dark_red())
            try:
                await ch.send(embed=e)
            except discord.Forbidden:
                pass

@bot.event
async def on_message_edit(before: discord.Message, after: discord.Message):
    """Log les éditions de messages."""
    if not before.guild or before.author.bot:
        return
    if before.content == after.content:
        return
    cfg = get_guild_cfg(before.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = before.guild.get_channel(int(ch_id))
    if not ch:
        return
    e = info_embed(
        "✏️ Message édité",
        f"**Auteur :** {before.author.mention} (`{before.author.id}`)\n"
        f"**Salon :** {before.channel.mention}\n"
        f"**[Aller au message]({after.jump_url})**\n\n"
        f"**Avant :** {before.content[:450] or '[vide]'}\n"
        f"**Après :** {after.content[:450] or '[vide]'}"
    )
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

# ── Logs : Rôles d'un membre ──────────────────────────────────────────────────
@bot.event
async def on_member_update(before: discord.Member, after: discord.Member):
    cfg = get_guild_cfg(before.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = before.guild.get_channel(int(ch_id))
    if not ch:
        return

    # Changement de rôle
    added   = [r for r in after.roles  if r not in before.roles]
    removed = [r for r in before.roles if r not in after.roles]
    if added or removed:
        executor = await get_audit_executor(before.guild, discord.AuditLogAction.member_role_update, after.id, within_seconds=5)
        executor_str = f"\n**Modifié par :** {executor.mention} (`{executor.id}`)" if executor else ""
        desc = f"**Membre :** {after.mention} (`{after.id}`)\n"
        if added:
            desc += f"**Rôles ajoutés :** {', '.join(r.mention for r in added)}\n"
        if removed:
            desc += f"**Rôles retirés :** {', '.join(r.mention for r in removed)}"
        desc += executor_str
        e = info_embed("🎭 Rôles modifiés", desc)
        try:
            await ch.send(embed=e)
        except discord.Forbidden:
            pass
        return

    # Changement de pseudo
    if before.nick != after.nick:
        executor = await get_audit_executor(before.guild, discord.AuditLogAction.member_update, after.id, within_seconds=5)
        executor_str = f"\n**Modifié par :** {executor.mention} (`{executor.id}`)" if executor and executor.id != after.id else ""
        e = info_embed(
            "✏️ Pseudo modifié",
            f"**Membre :** {after.mention} (`{after.id}`)\n"
            f"**Avant :** {before.nick or before.name}\n"
            f"**Après :** {after.nick or after.name}"
            + executor_str
        )
        try:
            await ch.send(embed=e)
        except discord.Forbidden:
            pass

    # Timeout ajouté / retiré
    before_to = before.timed_out_until
    after_to  = after.timed_out_until
    now       = datetime.now(timezone.utc)
    if not before_to and after_to and after_to > now:
        executor = await get_audit_executor(before.guild, discord.AuditLogAction.member_update, after.id, within_seconds=5)
        executor_str = f"\n**Appliqué par :** {executor.mention} (`{executor.id}`)" if executor else ""
        e = mod_embed(
            "🔇 Membre mis en timeout",
            f"**Membre :** {after.mention} (`{after.id}`)\n"
            f"**Fin :** <t:{int(after_to.timestamp())}:R>\n"
            f"**Durée :** {format_duration(after_to - now)}"
            + executor_str
        )
        try:
            await ch.send(embed=e)
        except discord.Forbidden:
            pass
    elif before_to and (not after_to or after_to <= now):
        executor = await get_audit_executor(before.guild, discord.AuditLogAction.member_update, after.id, within_seconds=5)
        executor_str = f"\n**Retiré par :** {executor.mention} (`{executor.id}`)" if executor else ""
        e = success_embed(
            "🔊 Timeout retiré",
            f"**Membre :** {after.mention} (`{after.id}`)"
            + executor_str
        )
        try:
            await ch.send(embed=e)
        except discord.Forbidden:
            pass

# ── Logs : Bans / Unbans ─────────────────────────────────────────────────────
@bot.event
async def on_member_ban(guild: discord.Guild, user: discord.User):
    cfg = get_guild_cfg(guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = guild.get_channel(int(ch_id))
    if not ch:
        return
    executor = await get_audit_executor(guild, discord.AuditLogAction.ban, user.id, within_seconds=5)
    executor_str = f"\n**Banni par :** {executor.mention} (`{executor.id}`)" if executor else ""

    # Récupérer la raison depuis les logs d'audit
    reason_str = ""
    try:
        async for entry in guild.audit_logs(limit=3, action=discord.AuditLogAction.ban):
            if entry.target and entry.target.id == user.id:
                if entry.reason:
                    reason_str = f"\n**Raison :** {entry.reason}"
                break
    except discord.Forbidden:
        pass

    e = mod_embed(
        "🔨 Membre banni",
        f"**Utilisateur :** {user} (`{user.id}`)"
        + executor_str
        + reason_str,
        discord.Color.dark_red()
    )
    e.set_thumbnail(url=user.display_avatar.url)
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_member_unban(guild: discord.Guild, user: discord.User):
    cfg = get_guild_cfg(guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = guild.get_channel(int(ch_id))
    if not ch:
        return
    executor = await get_audit_executor(guild, discord.AuditLogAction.unban, user.id, within_seconds=5)
    executor_str = f"\n**Débanni par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = success_embed(
        "✅ Membre débanni",
        f"**Utilisateur :** {user} (`{user.id}`)"
        + executor_str
    )
    e.set_thumbnail(url=user.display_avatar.url)
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

# ── Logs : Salons créés / supprimés / renommés ────────────────────────────────
@bot.event
async def on_guild_channel_create(channel):
    cfg = get_guild_cfg(channel.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    log_ch = channel.guild.get_channel(int(ch_id))
    if not log_ch:
        return
    kind = "vocal" if isinstance(channel, discord.VoiceChannel) else "textuel" if isinstance(channel, discord.TextChannel) else "catégorie"
    executor = await get_audit_executor(channel.guild, discord.AuditLogAction.channel_create, channel.id, within_seconds=5)
    executor_str = f"\n**Créé par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = success_embed(
        "➕ Salon créé",
        f"**Nom :** {channel.mention if hasattr(channel, 'mention') else channel.name}\n"
        f"**Type :** {kind}\n"
        f"**ID :** `{channel.id}`"
        + executor_str
    )
    try:
        await log_ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_guild_channel_delete(channel):
    # Nettoyage : si un salon stat-vocale est supprimé manuellement, on retire sa config.
    svcfg = statsvoc_db.get(str(channel.guild.id))
    if svcfg and str(channel.id) in svcfg.get("channels", {}):
        svcfg["channels"].pop(str(channel.id), None)
        save_statsvoc()

    cfg = get_guild_cfg(channel.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    log_ch = channel.guild.get_channel(int(ch_id))
    if not log_ch:
        return
    executor = await get_audit_executor(channel.guild, discord.AuditLogAction.channel_delete, channel.id, within_seconds=5)
    executor_str = f"\n**Supprimé par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = mod_embed(
        "🗑️ Salon supprimé",
        f"**Nom :** #{channel.name}\n**ID :** `{channel.id}`"
        + executor_str,
        discord.Color.dark_red()
    )
    try:
        await log_ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_guild_channel_update(before, after):
    cfg = get_guild_cfg(before.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    log_ch = before.guild.get_channel(int(ch_id))
    if not log_ch:
        return
    changes = []
    if before.name != after.name:
        changes.append(f"**Nom :** `{before.name}` → `{after.name}`")
    if hasattr(before, "topic") and before.topic != after.topic:
        changes.append(f"**Description :** `{before.topic or 'vide'}` → `{after.topic or 'vide'}`")
    if hasattr(before, "slowmode_delay") and before.slowmode_delay != after.slowmode_delay:
        changes.append(f"**Slowmode :** `{before.slowmode_delay}s` → `{after.slowmode_delay}s`")
    if not changes:
        return
    executor = await get_audit_executor(before.guild, discord.AuditLogAction.channel_update, after.id, within_seconds=5)
    executor_str = f"\n**Modifié par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = info_embed(
        "🔧 Salon modifié",
        f"**Salon :** {after.mention if hasattr(after, 'mention') else after.name}\n" + "\n".join(changes) + executor_str
    )
    try:
        await log_ch.send(embed=e)
    except discord.Forbidden:
        pass

# ── Logs : Rôles créés / supprimés / modifiés ────────────────────────────────
@bot.event
async def on_guild_role_create(role: discord.Role):
    cfg = get_guild_cfg(role.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = role.guild.get_channel(int(ch_id))
    if not ch:
        return
    executor = await get_audit_executor(role.guild, discord.AuditLogAction.role_create, role.id, within_seconds=5)
    executor_str = f"\n**Créé par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = success_embed(
        "➕ Rôle créé",
        f"**Nom :** {role.mention}\n**ID :** `{role.id}`"
        + executor_str
    )
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_guild_role_delete(role: discord.Role):
    cfg = get_guild_cfg(role.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = role.guild.get_channel(int(ch_id))
    if not ch:
        return
    executor = await get_audit_executor(role.guild, discord.AuditLogAction.role_delete, role.id, within_seconds=5)
    executor_str = f"\n**Supprimé par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = mod_embed(
        "🗑️ Rôle supprimé",
        f"**Nom :** @{role.name}\n**ID :** `{role.id}`\n**Couleur :** `{role.color}`"
        + executor_str,
        discord.Color.dark_red()
    )
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_guild_role_update(before: discord.Role, after: discord.Role):
    cfg = get_guild_cfg(before.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = before.guild.get_channel(int(ch_id))
    if not ch:
        return
    changes = []
    if before.name != after.name:
        changes.append(f"**Nom :** `{before.name}` → `{after.name}`")
    if before.color != after.color:
        changes.append(f"**Couleur :** `{before.color}` → `{after.color}`")
    if before.permissions != after.permissions:
        changes.append("**Permissions modifiées**")
    if before.hoist != after.hoist:
        changes.append(f"**Affiché séparément :** `{before.hoist}` → `{after.hoist}`")
    if before.mentionable != after.mentionable:
        changes.append(f"**Mentionnable :** `{before.mentionable}` → `{after.mentionable}`")
    if not changes:
        return
    executor = await get_audit_executor(before.guild, discord.AuditLogAction.role_update, after.id, within_seconds=5)
    executor_str = f"\n**Modifié par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = info_embed(
        "🔧 Rôle modifié",
        f"**Rôle :** {after.mention}\n" + "\n".join(changes) + executor_str
    )
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

# ── Logs : Serveur modifié ────────────────────────────────────────────────────
@bot.event
async def on_guild_update(before: discord.Guild, after: discord.Guild):
    cfg = get_guild_cfg(before.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = after.get_channel(int(ch_id))
    if not ch:
        return
    changes = []
    if before.name != after.name:
        changes.append(f"**Nom :** `{before.name}` → `{after.name}`")
    if before.icon != after.icon:
        changes.append("**Icône du serveur modifiée**")
    if before.verification_level != after.verification_level:
        changes.append(f"**Niveau de vérif :** `{before.verification_level}` → `{after.verification_level}`")
    if not changes:
        return
    executor = await get_audit_executor(before, discord.AuditLogAction.guild_update, before.id, within_seconds=5)
    executor_str = f"\n**Modifié par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = info_embed("🏠 Serveur modifié", "\n".join(changes) + executor_str)
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

# ── Logs : Emojis ─────────────────────────────────────────────────────────────
@bot.event
async def on_guild_emojis_update(guild: discord.Guild, before, after):
    cfg = get_guild_cfg(guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = guild.get_channel(int(ch_id))
    if not ch:
        return
    added   = [e for e in after  if e not in before]
    removed = [e for e in before if e not in after]
    if added:
        executor = await get_audit_executor(guild, discord.AuditLogAction.emoji_create, added[0].id if added else None, within_seconds=5)
        executor_str = f"\n**Ajouté par :** {executor.mention} (`{executor.id}`)" if executor else ""
        e = success_embed("😀 Emoji(s) ajouté(s)", " ".join(str(em) for em in added) + f"\n**Noms :** {', '.join(f'`:{em.name}:`' for em in added)}" + executor_str)
        try:
            await ch.send(embed=e)
        except discord.Forbidden:
            pass
    if removed:
        executor = await get_audit_executor(guild, discord.AuditLogAction.emoji_delete, removed[0].id if removed else None, within_seconds=5)
        executor_str = f"\n**Supprimé par :** {executor.mention} (`{executor.id}`)" if executor else ""
        e = mod_embed("🗑️ Emoji(s) supprimé(s)", ", ".join(f"`:{em.name}:`" for em in removed) + executor_str, discord.Color.dark_red())
        try:
            await ch.send(embed=e)
        except discord.Forbidden:
            pass

# ── Logs : Invitations ────────────────────────────────────────────────────────
@bot.event
async def on_invite_create(invite: discord.Invite):
    if not invite.guild:
        return
    _invite_cache.setdefault(invite.guild.id, {})[invite.code] = invite.uses or 0
    cfg = get_guild_cfg(invite.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = invite.guild.get_channel(int(ch_id))
    if not ch:
        return
    expires = f"<t:{int(invite.expires_at.timestamp())}:R>" if invite.expires_at else "Jamais"
    e = info_embed(
        "🔗 Invitation créée",
        f"**Créateur :** {invite.inviter.mention if invite.inviter else 'Inconnu'}\n"
        f"**Lien :** discord.gg/{invite.code}\n"
        f"**Salon :** {invite.channel.mention if invite.channel else 'Inconnu'}\n"
        f"**Expiration :** {expires}\n"
        f"**Utilisations max :** {invite.max_uses or '∞'}"
    )
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_invite_delete(invite: discord.Invite):
    if not invite.guild:
        return
    _invite_cache.get(invite.guild.id, {}).pop(invite.code, None)
    cfg = get_guild_cfg(invite.guild.id)
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = invite.guild.get_channel(int(ch_id))
    if not ch:
        return
    executor = await get_audit_executor(invite.guild, discord.AuditLogAction.invite_delete, within_seconds=5)
    executor_str = f"\n**Supprimé par :** {executor.mention} (`{executor.id}`)" if executor else ""
    e = mod_embed(
        "🔗 Invitation supprimée",
        f"**Code :** discord.gg/{invite.code}\n"
        f"**Utilisations :** {invite.uses or 0}"
        + executor_str,
        discord.Color.dark_red()
    )
    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

# ─────────────────────────────────────────
#  SALONS VOCAUX TEMPORAIRES ("Rejoindre pour créer")
# ─────────────────────────────────────────
TEMP_VOICE_QUALITY_OPTIONS = [
    ("🔈 64 kbps", 64000),
    ("🔉 96 kbps", 96000),
    ("🔊 128 kbps", 128000),
    ("🎚️ 256 kbps (Boost Niv. 2)", 256000),
    ("🎛️ 384 kbps (Boost Niv. 3)", 384000),
]

def build_temp_voice_embed(channel: discord.VoiceChannel, record: dict) -> discord.Embed:
    owner = channel.guild.get_member(record["owner"]) if channel.guild else None
    e = discord.Embed(
        title="🔊 Salon vocal temporaire",
        description="Utilisez les boutons ci-dessous pour gérer votre salon vocal.",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    e.add_field(name="Propriétaire", value=owner.mention if owner else f"<@{record['owner']}>", inline=False)
    e.add_field(name="Membres", value=str(len(channel.members)), inline=True)
    e.add_field(name="Limite", value=str(channel.user_limit) if channel.user_limit else "Aucune", inline=True)
    e.add_field(name="Verrouillé", value="Oui" if record.get("locked") else "Non", inline=True)
    e.add_field(name="Caché", value="Oui" if record.get("hidden") else "Non", inline=True)
    e.set_footer(text="Le salon sera supprimé automatiquement quand il sera vide.")
    return e

class VoiceRenameModal(discord.ui.Modal, title="Renommer le salon"):
    def __init__(self, channel_id: int):
        super().__init__()
        self.channel_id = channel_id
        self.new_name = discord.ui.TextInput(label="Nouveau nom", max_length=100, placeholder="Mon super salon")
        self.add_item(self.new_name)

    async def on_submit(self, interaction: discord.Interaction):
        record = _temp_voice.get(self.channel_id)
        if not record or interaction.user.id != record["owner"]:
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        try:
            await channel.edit(name=str(self.new_name.value)[:100], reason=f"Renommé par {interaction.user}")
        except discord.HTTPException:
            return await interaction.response.send_message("❌ Impossible de renommer (limite Discord atteinte, réessaie dans quelques minutes).", ephemeral=True)
        await interaction.response.send_message(f"✅ Salon renommé en **{self.new_name.value}**.", ephemeral=True)

class VoiceLimitModal(discord.ui.Modal, title="Limite de membres"):
    def __init__(self, channel_id: int):
        super().__init__()
        self.channel_id = channel_id
        self.limit_input = discord.ui.TextInput(label="Limite (0 = aucune, max 99)", max_length=2, placeholder="0")
        self.add_item(self.limit_input)

    async def on_submit(self, interaction: discord.Interaction):
        record = _temp_voice.get(self.channel_id)
        if not record or interaction.user.id != record["owner"]:
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        raw = str(self.limit_input.value).strip()
        if not raw.isdigit() or not (0 <= int(raw) <= 99):
            return await interaction.response.send_message("❌ Limite invalide (0 à 99).", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        limit = int(raw)
        try:
            await channel.edit(user_limit=limit, reason=f"Limite modifiée par {interaction.user}")
        except discord.HTTPException:
            return await interaction.response.send_message("❌ Impossible de modifier la limite.", ephemeral=True)
        await interaction.response.send_message(f"✅ Limite fixée à **{limit if limit else 'aucune'}**.", ephemeral=True)

class VoiceMemberSelect(discord.ui.Select):
    """Menu déroulant listant les membres actuellement dans le salon (sauf le propriétaire),
    utilisé pour Expulser / Muter / Muter le casque / Transférer."""
    def __init__(self, channel_id: int, owner_id: int, action: str):
        self.channel_id = channel_id
        self.owner_id = owner_id
        self.action = action  # "kick" | "mute" | "deafen" | "transfer"
        channel = bot.get_channel(channel_id)
        options = []
        if channel:
            for m in channel.members:
                if m.id == owner_id:
                    continue
                options.append(discord.SelectOption(label=str(m.display_name)[:100], value=str(m.id), description=str(m)[:100]))
        if not options:
            options = [discord.SelectOption(label="Aucun membre disponible", value="__none__")]
        labels = {
            "kick": "Choisis qui expulser",
            "mute": "Choisis qui muter/démuter (micro)",
            "deafen": "Choisis qui muter/démuter (casque)",
            "transfer": "Choisis le nouveau propriétaire",
        }
        super().__init__(placeholder=labels.get(action, "Choisis un membre"), options=options[:25], min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if self.values[0] == "__none__":
            return await interaction.response.send_message("❌ Personne à sélectionner.", ephemeral=True)
        record = _temp_voice.get(self.channel_id)
        if not record or interaction.user.id != record["owner"]:
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        target = channel.guild.get_member(int(self.values[0]))
        if not target or not target.voice or target.voice.channel is None or target.voice.channel.id != channel.id:
            return await interaction.response.send_message("❌ Ce membre n'est plus dans le salon.", ephemeral=True)

        if self.action == "kick":
            try:
                await target.move_to(None, reason=f"Expulsé du salon par {interaction.user}")
            except discord.HTTPException:
                return await interaction.response.send_message("❌ Impossible d'expulser ce membre.", ephemeral=True)
            await interaction.response.send_message(f"✅ **{target.display_name}** a été expulsé du salon.", ephemeral=True)

        elif self.action == "mute":
            try:
                await target.edit(mute=not target.voice.mute, reason=f"Mute basculé par {interaction.user}")
            except discord.HTTPException:
                return await interaction.response.send_message("❌ Impossible de muter ce membre.", ephemeral=True)
            state = "muté 🔇" if target.voice.mute else "démuté 🔊"
            await interaction.response.send_message(f"✅ **{target.display_name}** est maintenant {state}.", ephemeral=True)

        elif self.action == "deafen":
            try:
                await target.edit(deafen=not target.voice.deaf, reason=f"Mute casque basculé par {interaction.user}")
            except discord.HTTPException:
                return await interaction.response.send_message("❌ Impossible de muter le casque de ce membre.", ephemeral=True)
            state = "sourd 🔕" if target.voice.deaf else "rétabli 🔔"
            await interaction.response.send_message(f"✅ **{target.display_name}** a maintenant le casque {state}.", ephemeral=True)

        elif self.action == "transfer":
            old_owner = channel.guild.get_member(record["owner"])
            try:
                overwrites = dict(channel.overwrites)
                if old_owner:
                    overwrites.pop(old_owner, None)
                overwrites[target] = discord.PermissionOverwrite(
                    connect=True, view_channel=True, speak=True, manage_channels=True,
                    mute_members=True, deafen_members=True, move_members=True, priority_speaker=True
                )
                await channel.edit(overwrites=overwrites, reason=f"Transfert de propriété par {interaction.user}")
            except discord.HTTPException:
                return await interaction.response.send_message("❌ Impossible de transférer la propriété.", ephemeral=True)
            record["owner"] = target.id
            tempvoice_db[str(channel.id)] = {"owner": target.id, "guild": channel.guild.id}
            save_tempvoice()
            await interaction.response.send_message(f"✅ **{target.display_name}** est désormais propriétaire du salon.", ephemeral=True)

class VoiceMemberSelectView(discord.ui.View):
    def __init__(self, channel_id: int, owner_id: int, action: str):
        super().__init__(timeout=60)
        self.add_item(VoiceMemberSelect(channel_id, owner_id, action))

class VoiceQualitySelect(discord.ui.Select):
    def __init__(self, channel_id: int, owner_id: int):
        self.channel_id = channel_id
        self.owner_id = owner_id
        channel = bot.get_channel(channel_id)
        max_bitrate = channel.guild.bitrate_limit if channel else 96000
        options = []
        for label, value in TEMP_VOICE_QUALITY_OPTIONS:
            if value <= max_bitrate:
                options.append(discord.SelectOption(label=label, value=str(value)))
        if not options:
            options = [discord.SelectOption(label="🔈 64 kbps", value="64000")]
        super().__init__(placeholder="Choisis la qualité audio", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        record = _temp_voice.get(self.channel_id)
        if not record or interaction.user.id != record["owner"]:
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        try:
            await channel.edit(bitrate=int(self.values[0]), reason=f"Qualité modifiée par {interaction.user}")
        except discord.HTTPException:
            return await interaction.response.send_message("❌ Impossible de modifier la qualité (limite du serveur).", ephemeral=True)
        await interaction.response.send_message(f"✅ Qualité audio réglée sur **{int(self.values[0]) // 1000} kbps**.", ephemeral=True)

class VoiceQualityView(discord.ui.View):
    def __init__(self, channel_id: int, owner_id: int):
        super().__init__(timeout=60)
        self.add_item(VoiceQualitySelect(channel_id, owner_id))

class VoiceControlView(discord.ui.View):
    """Panneau de gestion envoyé en MP au créateur d'un salon vocal temporaire."""
    def __init__(self, channel_id: int, owner_id: int):
        super().__init__(timeout=None)
        self.channel_id = channel_id
        self.owner_id = owner_id

    def _is_owner(self, interaction: discord.Interaction) -> bool:
        record = _temp_voice.get(self.channel_id)
        return record is not None and interaction.user.id == record["owner"]

    @discord.ui.button(label="Verrouiller", style=discord.ButtonStyle.danger, row=0)
    async def lock_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        record = _temp_voice.get(self.channel_id)
        if not record or interaction.user.id != record["owner"]:
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        record["locked"] = not record.get("locked", False)
        try:
            await channel.set_permissions(
                channel.guild.default_role, connect=not record["locked"],
                reason=f"Salon {'verrouillé' if record['locked'] else 'déverrouillé'} par {interaction.user}"
            )
        except discord.HTTPException:
            pass
        button.label = "Déverrouiller" if record["locked"] else "Verrouiller"
        button.style = discord.ButtonStyle.success if record["locked"] else discord.ButtonStyle.danger
        await interaction.response.edit_message(embed=build_temp_voice_embed(channel, record), view=self)

    @discord.ui.button(label="Cacher", style=discord.ButtonStyle.secondary, row=0)
    async def hide_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        record = _temp_voice.get(self.channel_id)
        if not record or interaction.user.id != record["owner"]:
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        record["hidden"] = not record.get("hidden", False)
        try:
            await channel.set_permissions(
                channel.guild.default_role, view_channel=not record["hidden"],
                reason=f"Salon {'caché' if record['hidden'] else 'affiché'} par {interaction.user}"
            )
        except discord.HTTPException:
            pass
        button.label = "Afficher" if record["hidden"] else "Cacher"
        await interaction.response.edit_message(embed=build_temp_voice_embed(channel, record), view=self)

    @discord.ui.button(label="Limite", style=discord.ButtonStyle.secondary, row=0)
    async def limit_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_modal(VoiceLimitModal(self.channel_id))

    @discord.ui.button(label="Renommer", style=discord.ButtonStyle.secondary, row=1)
    async def rename_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_modal(VoiceRenameModal(self.channel_id))

    @discord.ui.button(label="Qualité", style=discord.ButtonStyle.secondary, row=1)
    async def quality_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_message("Choisis la qualité audio :", view=VoiceQualityView(self.channel_id, self.owner_id), ephemeral=True)

    @discord.ui.button(label="Mute tout", style=discord.ButtonStyle.danger, row=2)
    async def muteall_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        for m in channel.members:
            if m.id != interaction.user.id:
                try:
                    await m.edit(mute=True, reason=f"Mute all par {interaction.user}")
                except discord.HTTPException:
                    pass
        await interaction.response.send_message("✅ Tout le monde a été muté (sauf toi).", ephemeral=True)

    @discord.ui.button(label="Unmute tout", style=discord.ButtonStyle.success, row=2)
    async def unmuteall_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        if not channel:
            return await interaction.response.send_message("❌ Ce salon n'existe plus.", ephemeral=True)
        for m in channel.members:
            try:
                await m.edit(mute=False, reason=f"Unmute all par {interaction.user}")
            except discord.HTTPException:
                pass
        await interaction.response.send_message("✅ Tout le monde a été démuté.", ephemeral=True)

    @discord.ui.button(label="Expulser", style=discord.ButtonStyle.danger, row=2)
    async def kick_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_message("Qui veux-tu expulser du salon ?", view=VoiceMemberSelectView(self.channel_id, self.owner_id, "kick"), ephemeral=True)

    @discord.ui.button(label="Mute quelqu'un", style=discord.ButtonStyle.secondary, row=3)
    async def mute_one_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_message("Qui veux-tu muter/démuter (micro) ?", view=VoiceMemberSelectView(self.channel_id, self.owner_id, "mute"), ephemeral=True)

    @discord.ui.button(label="Mute casque", style=discord.ButtonStyle.secondary, row=3)
    async def deafen_one_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_message("Qui veux-tu muter/démuter (casque) ?", view=VoiceMemberSelectView(self.channel_id, self.owner_id, "deafen"), ephemeral=True)

    @discord.ui.button(label="Transférer", style=discord.ButtonStyle.secondary, row=4)
    async def transfer_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        await interaction.response.send_message("À qui veux-tu transférer la propriété ?", view=VoiceMemberSelectView(self.channel_id, self.owner_id, "transfer"), ephemeral=True)

    @discord.ui.button(label="Supprimer", style=discord.ButtonStyle.danger, row=4)
    async def delete_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not self._is_owner(interaction):
            return await interaction.response.send_message("❌ Tu n'es pas le propriétaire de ce salon.", ephemeral=True)
        channel = bot.get_channel(self.channel_id)
        _temp_voice.pop(self.channel_id, None)
        tempvoice_db.pop(str(self.channel_id), None)
        save_tempvoice()
        if channel:
            try:
                await channel.delete(reason=f"Supprimé par {interaction.user}")
            except discord.HTTPException:
                pass
        for item in self.children:
            item.disabled = True
        try:
            await interaction.response.edit_message(content="🗑️ Salon supprimé.", embed=None, view=self)
        except discord.HTTPException:
            pass
        self.stop()

async def create_temp_voice_channel(member: discord.Member, hub_channel: discord.VoiceChannel):
    """Crée un salon vocal personnel pour `member` quand il rejoint le salon hub, puis
    lui envoie en MP le panneau de gestion (100% personnalisable)."""
    guild = member.guild
    overwrites = {
        guild.default_role: discord.PermissionOverwrite(connect=True, view_channel=True),
        member: discord.PermissionOverwrite(
            connect=True, view_channel=True, speak=True, manage_channels=True,
            mute_members=True, deafen_members=True, move_members=True, priority_speaker=True
        ),
        guild.me: discord.PermissionOverwrite(
            connect=True, view_channel=True, manage_channels=True,
            move_members=True, mute_members=True, deafen_members=True
        ),
    }
    try:
        new_channel = await guild.create_voice_channel(
            name=f"🔊 {member.display_name}"[:100],
            category=hub_channel.category,
            overwrites=overwrites,
            reason=f"Salon vocal temporaire créé par {member}"
        )
    except discord.Forbidden:
        return

    try:
        await member.move_to(new_channel, reason="Déplacement vers son salon vocal personnel")
    except discord.HTTPException:
        pass

    record = {"owner": member.id, "guild": guild.id, "locked": False, "hidden": False}
    _temp_voice[new_channel.id] = record
    tempvoice_db[str(new_channel.id)] = {"owner": member.id, "guild": guild.id}
    save_tempvoice()

    embed = build_temp_voice_embed(new_channel, record)
    view = VoiceControlView(new_channel.id, member.id)
    try:
        await member.send(embed=embed, view=view)
    except discord.Forbidden:
        # MP fermés : on tente de poster directement dans le salon vocal (texte intégré au salon vocal)
        try:
            await new_channel.send(content=f"{member.mention} (tes MP sont fermés, voici ton panneau ici)", embed=embed, view=view)
        except discord.HTTPException:
            pass

async def handle_jtc_voice_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    cfg = get_guild_cfg(member.guild.id)
    hub_id = cfg.get("jtc_channel")

    # ── Le membre rejoint le salon "➕ Créer un salon" → on lui crée son salon perso ──
    if hub_id and after.channel and after.channel.id == int(hub_id) and (not before.channel or before.channel.id != after.channel.id):
        await create_temp_voice_channel(member, after.channel)

    # ── Le membre quitte un salon temporaire → suppression automatique s'il est vide ──
    if before.channel and before.channel.id in _temp_voice:
        if (not after.channel or after.channel.id != before.channel.id):
            if len(before.channel.members) == 0:
                _temp_voice.pop(before.channel.id, None)
                tempvoice_db.pop(str(before.channel.id), None)
                save_tempvoice()
                try:
                    await before.channel.delete(reason="Salon vocal temporaire vide")
                except (discord.NotFound, discord.HTTPException):
                    pass

# ── Logs : Vocal join/leave/move ──────────────────────────────────────────────
@bot.event
async def on_voice_state_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    cfg = get_guild_cfg(member.guild.id)

    # ── Suivi temps vocal pour +statistic (indépendant du salon de logs) ──
    if not member.bot:
        stats = _member_stats[member.guild.id][member.id]
        now_ts = time.time()
        if not before.channel and after.channel:
            # Connexion vocal
            stats["voice_joined"] = now_ts
        elif before.channel and not after.channel:
            # Déconnexion vocal
            if stats["voice_joined"] is not None:
                stats["voice_seconds"] += now_ts - stats["voice_joined"]
                stats["voice_joined"] = None
        elif before.channel and after.channel and before.channel != after.channel:
            # Déplacement : on cumule le temps passé dans l'ancien salon
            if stats["voice_joined"] is not None:
                stats["voice_seconds"] += now_ts - stats["voice_joined"]
            stats["voice_joined"] = now_ts

    # ── Salons vocaux temporaires "Rejoindre pour créer" (indépendant du salon de logs) ──
    await handle_jtc_voice_update(member, before, after)

    # ── Logs de connexion/déconnexion/déplacement vocal (si configuré) ──
    ch_id = cfg.get("log_channel")
    if not ch_id:
        return
    ch = member.guild.get_channel(int(ch_id))
    if not ch:
        return

    if not before.channel and after.channel:
        e = success_embed(
            "🔊 Salon vocal — Connexion",
            f"**Membre :** {member.mention} (`{member.id}`)\n"
            f"**Salon :** {after.channel.mention}"
        )
    elif before.channel and not after.channel:
        e = mod_embed(
            "🔇 Salon vocal — Déconnexion",
            f"**Membre :** {member.mention} (`{member.id}`)\n"
            f"**Salon quitté :** {before.channel.mention}",
            discord.Color.dark_gray()
        )
    elif before.channel and after.channel and before.channel != after.channel:
        e = info_embed(
            "🔀 Salon vocal — Déplacement",
            f"**Membre :** {member.mention} (`{member.id}`)\n"
            f"**Avant :** {before.channel.mention} → **Après :** {after.channel.mention}"
        )
    else:
        return

    try:
        await ch.send(embed=e)
    except discord.Forbidden:
        pass

@bot.event
async def on_raw_reaction_add(payload: discord.RawReactionActionEvent):
    """Gestion des reaction roles."""
    if payload.member and payload.member.bot:
        return
    gid = str(payload.guild_id)
    mid = str(payload.message_id)
    emoji_str = str(payload.emoji)
    rr_data = rreactions_db.get(gid, {}).get(mid, {}).get(emoji_str)
    if not rr_data:
        return
    guild = bot.get_guild(payload.guild_id)
    if not guild:
        return
    member = payload.member or guild.get_member(payload.user_id)
    if not member:
        return
    role = guild.get_role(int(rr_data["role_id"]))
    if not role:
        return
    try:
        await member.add_roles(role, reason="Reaction Role")
    except discord.Forbidden:
        pass

@bot.event
async def on_raw_reaction_remove(payload: discord.RawReactionActionEvent):
    """Retire le rôle si la réaction est enlevée."""
    gid = str(payload.guild_id)
    mid = str(payload.message_id)
    emoji_str = str(payload.emoji)
    rr_data = rreactions_db.get(gid, {}).get(mid, {}).get(emoji_str)
    if not rr_data:
        return
    guild = bot.get_guild(payload.guild_id)
    if not guild:
        return
    member = guild.get_member(payload.user_id)
    if not member:
        return
    role = guild.get_role(int(rr_data["role_id"]))
    if not role:
        return
    try:
        await member.remove_roles(role, reason="Reaction Role retiré")
    except discord.Forbidden:
        pass

# ─────────────────────────────────────────
#  Automod — on_message
# ─────────────────────────────────────────
@bot.event
async def on_message(message: discord.Message):
    _bot_stats["messages_today"] += 1

    if message.author.bot or not message.guild:
        await bot.process_commands(message)
        return

    # ── Suivi messages pour +statistic ────────────────────────────────────
    _member_stats[message.guild.id][message.author.id]["messages"] += 1

    am_cfg = get_automod_cfg(message.guild.id)

    if not am_cfg.get("enabled", False) or is_exempt(message, am_cfg):
        await bot.process_commands(message)
        return

    content = message.content

    # ── Anti-invitations Discord ──────────────────────────────────────────
    if am_cfg.get("anti_invites") and INVITE_PATTERN.search(content):
        await automod_action(message, "Invitation Discord non autorisée.", am_cfg)
        return

    # ── Anti-liens externes (GIFs et domaines whitelist exemptés) ─────────
    if am_cfg.get("anti_links"):
        whitelist = am_cfg.get("whitelist_domains", [])
        if has_non_gif_link(content, whitelist):
            await automod_action(message, "Lien externe non autorisé.", am_cfg)
            return

    # ── Anti-scam ──────────────────────────────────────────────────────────
    if am_cfg.get("anti_scam"):
        for pattern in SCAM_PATTERNS:
            if pattern.search(content):
                await automod_action(message, "Message de type scam/phishing détecté.", am_cfg)
                return

    # ── Anti-mots interdits ───────────────────────────────────────────────
    if am_cfg.get("anti_badwords"):
        bad = am_cfg.get("badwords", [])
        low = content.lower()
        for word in bad:
            if word.lower() in low:
                await automod_action(message, "Mot interdit détecté.", am_cfg)
                return

    # ── Anti-majuscules ───────────────────────────────────────────────────
    if am_cfg.get("anti_caps"):
        min_len  = am_cfg.get("caps_min_length", 10)
        pct_cap  = am_cfg.get("caps_percent", 70)
        letters  = [c for c in content if c.isalpha()]
        if len(letters) >= min_len:
            caps_ratio = sum(1 for c in letters if c.isupper()) / len(letters) * 100
            if caps_ratio >= pct_cap:
                await automod_action(message, f"Trop de majuscules ({int(caps_ratio)}%).", am_cfg)
                return

    # ── Anti-mention flood ────────────────────────────────────────────────
    if am_cfg.get("anti_mentions"):
        max_m = am_cfg.get("max_mentions", 5)
        total_mentions = len(message.mentions) + len(message.role_mentions)
        if total_mentions >= max_m:
            await automod_action(message, f"Trop de mentions ({total_mentions}).", am_cfg)
            return

    # ── Anti-emoji flood ──────────────────────────────────────────────────
    if am_cfg.get("anti_emoji"):
        max_e = am_cfg.get("max_emojis", 10)
        emoji_count = len(EMOJI_PATTERN.findall(content))
        if emoji_count >= max_e:
            await automod_action(message, f"Trop d'emojis ({emoji_count}).", am_cfg)
            return

    # ── Anti-pièces jointes ───────────────────────────────────────────────
    if am_cfg.get("anti_attachments") and len(message.attachments) >= am_cfg.get("max_attachments", 5):
        await automod_action(message, f"Trop de pièces jointes ({len(message.attachments)}).", am_cfg)
        return

    # ── Anti-retours à la ligne (spam vertical) ─────────────────────────────
    if am_cfg.get("anti_newlines"):
        max_n = am_cfg.get("max_newlines", 10)
        newline_count = content.count("\n")
        if newline_count >= max_n:
            await automod_action(message, f"Trop de retours à la ligne ({newline_count}).", am_cfg)
            return

    # ── Anti-Zalgo ────────────────────────────────────────────────────────
    if am_cfg.get("anti_zalgo") and ZALGO_PATTERN.search(content):
        await automod_action(message, "Texte Zalgo/caractères spéciaux non autorisé.", am_cfg)
        return

    # ── Anti-flood (messages identiques) ─────────────────────────────────
    if am_cfg.get("anti_flood") and content.strip():
        flood_count = am_cfg.get("flood_count", 3)
        key = (message.guild.id, message.channel.id, message.author.id)
        _flood_cache[key].append(content.strip().lower())
        _flood_cache[key] = _flood_cache[key][-flood_count:]
        if (len(_flood_cache[key]) >= flood_count and
                len(set(_flood_cache[key])) == 1):
            _flood_cache[key].clear()
            await automod_action(message, "Flood de messages identiques détecté.", am_cfg)
            return

    # ── Anti-spam (vitesse d'envoi) ───────────────────────────────────────
    if am_cfg.get("anti_spam"):
        threshold = am_cfg.get("spam_threshold", 5)
        interval  = am_cfg.get("spam_interval", 5)
        now       = datetime.now(timezone.utc).timestamp()
        gid, uid  = message.guild.id, message.author.id
        timestamps = _spam_tracker[gid][uid]
        timestamps.append(now)
        _spam_tracker[gid][uid] = [t for t in timestamps if now - t <= interval]
        if len(_spam_tracker[gid][uid]) >= threshold:
            _spam_tracker[gid][uid].clear()
            await automod_action(message, f"Spam détecté ({threshold} messages en {interval}s).", am_cfg)
            return

    await bot.process_commands(message)

# ─────────────────────────────────────────
#  AIDE
# ─────────────────────────────────────────
# ─────────────────────────────────────────
#  AIDE — Menu déroulant (Select)
# ─────────────────────────────────────────
HELP_SECTIONS = {
    "sanctions": {
        "label": "🔨 Sanctions",
        "description": "Ban, kick, mute, warn, tempban…",
        "color": discord.Color.red(),
        "commands": [
            ("bl",         "<@membre|pseudo|id> [raison]",        "Bannir (blacklist), par mention/pseudo ou ID (même hors serveur)"),
            ("unbl",       "<user_id> [raison]",                 "Débannir un utilisateur par son ID"),
            ("blist",      "",                                    "Lister tous les membres bannis"),
            ("unbanall",   "",                                    "Débannir tout le monde (admin, confirmation)"),
            ("kick",       "<membre> [raison]",                  "Expulser un membre"),
            ("softbl",     "<membre> [raison]",                  "Ban + déban immédiat (efface les msgs)"),
            ("tembl",      "<membre> <durée> <raison>",          "Ban temporaire (ex : 1d, 2h)"),
            ("mute",       "<membre> <durée> [raison]",          "Timeout un membre"),
            ("unmute",     "<membre> [raison]",                  "Retirer le timeout"),
            ("warn",       "<membre> <raison>",                  "Ajouter un avertissement (3=mute 1j, 5=bl)"),
            ("unwarn",     "<membre> <id>",                      "Supprimer un warn spécifique"),
            ("clearwarns", "<membre>",                           "Effacer tous les warns d'un membre"),
            ("warns",      "[membre]",                           "Consulter les warns"),
        ],
    },
    "nettoyage": {
        "label": "🧹 Nettoyage",
        "description": "Supprimer des messages",
        "color": discord.Color.teal(),
        "commands": [
            ("clear",  "<nombre|all>",       "Supprimer N messages ou tous dans le salon"),
            ("purge",  "<membre> [nombre]",  "Supprimer les messages d'un membre"),
            ("snipe",  "[@membre]",          "Voir les messages supprimés récents"),
        ],
    },
    "salons": {
        "label": "🔒 Salons",
        "description": "Gérer les salons du serveur",
        "color": discord.Color.dark_blue(),
        "commands": [
            ("lock",        "[salon]",                   "Verrouiller un salon"),
            ("unlock",      "[salon]",                   "Déverrouiller un salon"),
            ("slowmode",    "<sec> [salon]",             "Définir le slowmode"),
            ("nuke",        "[salon]",                   "Recréer un salon (efface tout)"),
            ("createtext",  "<nom> [catégorie]",         "Créer un salon textuel"),
            ("createvoice", "<nom> [catégorie]",         "Créer un salon vocal"),
            ("createcat",   "<nom>",                     "Créer une catégorie"),
            ("deletechan",  "<salon>",                   "Supprimer un salon"),
            ("renamechan",  "<salon> <nom>",             "Renommer un salon"),
        ],
    },
    "giveaways": {
        "label": "🎉 Giveaways",
        "description": "Lancer et gérer des giveaways",
        "color": discord.Color.gold(),
        "commands": [
            ("gcreate", "<durée> <gagnants> <prix>", "Lancer un giveaway"),
            ("gend",    "<message_id>",              "Terminer un giveaway immédiatement"),
            ("greroll", "<message_id>",              "Retirer un nouveau gagnant"),
            ("glist",   "",                          "Lister les giveaways actifs"),
        ],
    },
    "tickets": {
        "label": "🎫 Tickets",
        "description": "Système de support par ticket (boutons)",
        "color": discord.Color.purple(),
        "commands": [
            ("ticketadd",       "<nom>",                      "Créer un type de ticket (= un bouton)"),
            ("ticketremove",    "<type>",                     "Supprimer un type de ticket"),
            ("ticketedit",      "<type> <champ> <valeur>",     "Modifier label/emoji/style/catégorie/message"),
            ("ticketrole",      "<type> add/remove <@rôle>",   "Gérer les rôles staff d'un type"),
            ("ticketquestion",  "<type> add/remove/list",      "Gérer le formulaire d'ouverture"),
            ("tickettypes",     "",                            "Lister les types configurés"),
            ("ticketpanel",     "<salon> [Titre | Description | image: <url>]","Envoyer le panneau (+ image/gif jointe en pièce jointe)"),
            ("ticketpanelimage","<id_message> <url|none>",     "Changer/retirer l'image d'un panneau déjà envoyé"),
            ("ticketsettings",  "[option] [valeur]",           "Réglages globaux (max, logs, naming…)"),
            ("closeticket",     "",                            "Fermer le ticket (dans le salon ticket)"),
        ],
    },
    "fun": {
        "label": "🎭 Fun & Social",
        "description": "Commandes fun et sociales",
        "color": discord.Color.magenta(),
        "commands": [
            ("marry",    "@membre",      "Demander en mariage"),
            ("divorce",  "",             "Divorcer"),
            ("couples",  "",             "Voir les couples du serveur"),
            ("coinflip", "",             "Pile ou Face"),
            ("roll",     "[NdN]",        "Lancer des dés (ex : 2d6)"),
            ("8ball",    "<question>",   "Réponse de la boule magique"),
        ],
    },
    "utilitaires": {
        "label": "📢 Utilitaires",
        "description": "Infos, sondages, rappels…",
        "color": discord.Color.blurple(),
        "commands": [
            ("stats",    "",                             "Statistiques du serveur"),
            ("statvoc",  "create/format/remove/list",   "Salons vocaux stats auto (membres/en ligne/vocal/boosts)"),
            ("botinfo",  "",                             "Infos et stats du bot"),
            ("ping",     "",                             "Latence du bot"),
            ("uptime",   "",                             "Temps de fonctionnement"),
            ("poll",     "<question> | <opt1> | …",     "Créer un sondage"),
            ("remind",   "<durée> <message>",           "Créer un rappel"),
            ("embed",    "<titre> | <description>",     "Envoyer un embed personnalisé"),
            ("announce", "<message>",                   "Envoyer une annonce"),
            ("calc",     "<expression>",                "Calculatrice"),
            ("say",      "<message>",                   "Faire parler le bot"),
            ("create",   "<emoji>",                     "Voler/cloner un emoji"),
        ],
    },
    "membres": {
        "label": "👤 Membres & Rôles",
        "description": "Rôles, profils, accueil…",
        "color": discord.Color.green(),
        "commands": [
            ("invites",             "[@membre]",                    "Voir les invitations d'un membre"),
            ("statistic",           "[@membre]",                    "Stats messages & temps vocal d'un membre"),
            ("leaderboard",         "",                             "Top 3 messages & Top 3 temps vocal + ton classement"),
            ("autorole",            "<rôle>",                    "Auto-rôle à l'arrivée"),
            ("setwelcome",          "<salon> <message>",         "Message de bienvenue (variables : {mention} {name} {server} {number})"),
            ("setwelcometitle",     "<titre>",                   "Titre de l'embed de bienvenue"),
            ("setwelcomeimage",     "<url> (ou joins une image/gif)", "Image/gif affiché dans le message de bienvenue"),
            ("removewelcomeimage",  "",                          "Retirer l'image du message de bienvenue"),
            ("addrole",             "<membre> <rôle>",           "Donner un rôle"),
            ("removerole",          "<membre> <rôle>",           "Retirer un rôle"),
            ("temprole",            "<membre> <rôle> <durée>",   "Rôle temporaire"),
            ("reactionrole",        "<msg_id> <emoji> <rôle>",   "Ajouter un reaction role"),
            ("removereactionrole",  "<msg_id> <emoji>",          "Supprimer un reaction role"),
            ("avatar",              "[membre]",                  "Afficher l'avatar"),
            ("userinfo",            "[membre]",                  "Infos sur un membre"),
            ("serverinfo",          "",                          "Infos sur le serveur"),
            ("roleinfo",            "<rôle>",                    "Infos sur un rôle"),
        ],
    },
    "config": {
        "label": "⚙️ Configuration",
        "description": "Logs, rôles, paramètres",
        "color": discord.Color.greyple(),
        "commands": [
            ("setlog",      "<salon>",  "Définir le salon de logs"),
            ("setmuterole", "<rôle>",   "Définir le rôle muet (legacy)"),
            ("setjtc",      "create | <#salon>",  "Salon 'Rejoindre pour créer' (salons vocaux persos)"),
            ("removejtc",   "",         "Désactiver les salons vocaux temporaires"),
            ("setinvitecheck",    "<#salon>",  "Salon de suivi des invitations (qui a invité qui)"),
            ("removeinvitecheck", "",           "Désactiver le suivi des invitations"),
        ],
    },
    "automod": {
        "label": "🛡️ AutoMod",
        "description": "Modération automatique",
        "color": discord.Color.orange(),
        "commands": [
            ("automod status",                              "",  "Voir la configuration AutoMod"),
            ("automod enable / disable",                    "",  "Activer / désactiver l'AutoMod"),
            ("automod set <règle> on/off",                  "",  "Activer/désactiver une règle"),
            ("automod action <delete|warn|mute|kick|ban>",  "",  "Choisir l'action automatique"),
            ("automod mute_duration <durée>",               "",  "Durée du mute automatique"),
            ("automod max_mentions <nb>",                   "",  "Nb max de mentions par message"),
            ("automod max_emojis <nb>",                      "",  "Nb max d'emojis par message"),
            ("automod max_attachments <nb>",                "",  "Nb max de pièces jointes par message"),
            ("automod max_newlines <nb>",                   "",  "Nb max de retours à la ligne par message"),
            ("automod warn_threshold <nb>",                 "",  "Nombre de warns avant action"),
            ("automod warn_action <action>",                "",  "Action au seuil de warns"),
            ("automod whitelist_domain add/remove <dom>",   "",  "Domaine autorisé malgré anti_links"),
            ("automod badword add/remove/list <mot>",       "",  "Gérer les mots interdits"),
            ("automod exempt_role @rôle add/remove",        "",  "Exempter un rôle de l'AutoMod"),
            ("automod exempt_channel #salon add/remove",    "",  "Exempter un salon de l'AutoMod"),
        ],
    },
}

HELP_PAGE_SIZE = 6  # commandes max par page

def build_home_embed(author: discord.User) -> discord.Embed:
    e = discord.Embed(
        title="🤖 Aide — Menu principal",
        description=(
            f"Préfixe : **`{PREFIX}`**\n\n"
            "Sélectionne une catégorie dans le menu ci-dessous pour voir les commandes.\n"
            "Tu peux aussi taper `+help <commande>` directement.\n\n"
            + "\n".join(
                f"{data['label']} — *{data['description']}*"
                for data in HELP_SECTIONS.values()
            )
        ),
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    e.set_footer(text=f"Demandé par {author}", icon_url=author.display_avatar.url)
    return e

def build_section_pages(key: str) -> list[list[str]]:
    """Découpe les commandes d'une section en pages de HELP_PAGE_SIZE lignes."""
    data = HELP_SECTIONS[key]
    lines = []
    for name, args, desc in data["commands"]:
        if args:
            lines.append(f"`{PREFIX}{name}` `{args}`\n┗ {desc}")
        else:
            lines.append(f"`{PREFIX}{name}`\n┗ {desc}")
    # Découper en pages
    pages = [lines[i:i + HELP_PAGE_SIZE] for i in range(0, len(lines), HELP_PAGE_SIZE)]
    return pages if pages else [[]]

def build_section_embed(key: str, author: discord.User, page: int = 0) -> discord.Embed:
    data  = HELP_SECTIONS[key]
    pages = build_section_pages(key)
    total = len(pages)
    page  = max(0, min(page, total - 1))
    e = discord.Embed(
        title=data["label"],
        description="\n".join(pages[page]),
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    footer_page = f"Page {page + 1}/{total} • {len(HELP_SECTIONS[key]['commands'])} commande(s)"
    e.set_footer(
        text=f"Demandé par {author} • {footer_page} • {PREFIX}help <commande> pour plus de détails",
        icon_url=author.display_avatar.url
    )
    return e

class HelpSelect(discord.ui.Select):
    def __init__(self, author: discord.User, view_ref):
        self.author   = author
        self.view_ref = view_ref
        options = [
            discord.SelectOption(label="🏠 Accueil", value="home", description="Retourner au menu principal")
        ] + [
            discord.SelectOption(
                label=data["label"],
                value=key,
                description=data["description"]
            )
            for key, data in HELP_SECTIONS.items()
        ]
        super().__init__(placeholder="📂 Choisir une catégorie…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author.id:
            return await interaction.response.send_message("❌ Ce menu ne t'appartient pas.", ephemeral=True)
        selected = self.values[0]
        self.view_ref.current_section = selected
        self.view_ref.current_page    = 0
        self.view_ref.update_buttons()
        if selected == "home":
            embed = build_home_embed(self.author)
        else:
            embed = build_section_embed(selected, self.author, 0)
        await interaction.response.edit_message(embed=embed, view=self.view_ref)

class HelpView(discord.ui.View):
    def __init__(self, author: discord.User):
        super().__init__(timeout=180)
        self.author          = author
        self.current_section = "home"
        self.current_page    = 0
        self.message         = None

        self.select = HelpSelect(author, self)
        self.add_item(self.select)

        # Bouton page précédente
        self.prev_btn = discord.ui.Button(emoji="◀", style=discord.ButtonStyle.primary, row=1, disabled=True)
        self.prev_btn.callback = self.go_prev
        self.add_item(self.prev_btn)

        # Label de page (bouton désactivé, juste pour l'affichage)
        self.page_label = discord.ui.Button(label="1/1", style=discord.ButtonStyle.secondary, row=1, disabled=True)
        self.add_item(self.page_label)

        # Bouton page suivante
        self.next_btn = discord.ui.Button(emoji="▶", style=discord.ButtonStyle.primary, row=1, disabled=True)
        self.next_btn.callback = self.go_next
        self.add_item(self.next_btn)

        self.update_buttons()

    def _total_pages(self) -> int:
        if self.current_section == "home":
            return 1
        return len(build_section_pages(self.current_section))

    def _rebuild_pagination(self):
        """Ajoute ou retire les boutons de pagination selon le nombre de pages."""
        total = self._total_pages()
        has_pagination = any(item is self.prev_btn for item in self.children)

        if total > 1 and not has_pagination:
            self.add_item(self.prev_btn)
            self.add_item(self.page_label)
            self.add_item(self.next_btn)
        elif total <= 1 and has_pagination:
            self.remove_item(self.prev_btn)
            self.remove_item(self.page_label)
            self.remove_item(self.next_btn)

    def update_buttons(self):
        total = self._total_pages()
        self._rebuild_pagination()
        if total > 1:
            self.prev_btn.disabled  = (self.current_page <= 0)
            self.next_btn.disabled  = (self.current_page >= total - 1)
            self.page_label.label   = f"{self.current_page + 1}/{total}"
            self.page_label.disabled = True

    async def go_prev(self, interaction: discord.Interaction):
        if interaction.user.id != self.author.id:
            return await interaction.response.send_message("❌ Ce menu ne t'appartient pas.", ephemeral=True)
        self.current_page = max(0, self.current_page - 1)
        self.update_buttons()
        embed = build_section_embed(self.current_section, self.author, self.current_page)
        await interaction.response.edit_message(embed=embed, view=self)

    async def go_next(self, interaction: discord.Interaction):
        if interaction.user.id != self.author.id:
            return await interaction.response.send_message("❌ Ce menu ne t'appartient pas.", ephemeral=True)
        self.current_page = min(self._total_pages() - 1, self.current_page + 1)
        self.update_buttons()
        embed = build_section_embed(self.current_section, self.author, self.current_page)
        await interaction.response.edit_message(embed=embed, view=self)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        try:
            if self.message:
                await self.message.edit(view=self)
        except Exception:
            pass

@bot.command(name="help")
async def help_cmd(ctx, commande: str = None):
    """Affiche l'aide avec un menu déroulant par catégorie."""
    if commande:
        cmd = bot.get_command(commande)
        if cmd:
            e = info_embed(f"{PREFIX}{cmd.name}", cmd.help or "Pas de description disponible.")
            return await ctx.send(embed=e)
        return await ctx.reply(f"❌ Commande `{commande}` inconnue.")

    view = HelpView(ctx.author)
    embed = build_home_embed(ctx.author)
    view.message = await ctx.send(embed=embed, view=view)

# ─────────────────────────────────────────
#  SANCTIONS
# ─────────────────────────────────────────
@bot.command(name="unbl")
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def unban(ctx, user_id: int, *, reason: str = "Aucune raison fournie"):
    """Débannir un utilisateur via son ID."""
    try:
        user = await bot.fetch_user(user_id)
        await ctx.guild.unban(user, reason=f"{ctx.author} : {reason}")
        e = success_embed("✅ Membre débanni", f"**Cible :** {user} (`{user_id}`)\n**Modérateur :** {ctx.author.mention}\n**Raison :** {reason}")
        await ctx.send(embed=e)
        await send_log(ctx.guild, e)
    except discord.NotFound:
        await ctx.reply("❌ Cet utilisateur n'est pas banni.")

@bot.command(name="bl")
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def banid(ctx, cible: str, *, reason: str = "Aucune raison fournie"):
    """Bannir (blacklist) un utilisateur : par ID (même hors du serveur), par mention ou par pseudo
    s'il est déjà membre du serveur. Usage : +bl <@membre|pseudo|id> [raison]"""
    user = None

    # 1) Membre déjà dans le serveur : mention, "pseudo#1234", pseudo seul, ou ID
    try:
        member = await commands.MemberConverter().convert(ctx, cible)
        user = member
    except commands.BadArgument:
        pass

    # 2) Sinon on tente un ID brut (utilisateur potentiellement hors serveur)
    if user is None:
        raw_id = cible.strip("<@!>")
        if raw_id.isdigit():
            try:
                user = await bot.fetch_user(int(raw_id))
            except discord.NotFound:
                return await ctx.reply("❌ Aucun utilisateur trouvé avec cet ID.")
            except discord.HTTPException:
                return await ctx.reply("❌ Impossible de récupérer cet utilisateur.")
        else:
            return await ctx.reply("❌ Utilisateur introuvable. Utilise une mention, un pseudo (s'il est dans le serveur) ou un ID.")

    if isinstance(user, discord.Member) and not check_hierarchy(ctx, user):
        return await ctx.reply("❌ Tu ne peux pas bannir ce membre (hiérarchie).")

    # Vérifier s'il est déjà banni
    try:
        await ctx.guild.fetch_ban(user)
        return await ctx.reply(f"❌ {user} (`{user.id}`) est déjà banni.")
    except discord.NotFound:
        pass

    try:
        await ctx.guild.ban(user, reason=f"{ctx.author} : {reason}", delete_message_days=1)
    except discord.Forbidden:
        return await ctx.reply("❌ Je n'ai pas la permission de bannir cet utilisateur.")

    e = mod_embed(
        "🔨 Utilisateur banni (blacklist)",
        f"**Cible :** {user} (`{user.id}`)\n"
        f"**Modérateur :** {ctx.author.mention}\n"
        f"**Raison :** {reason}"
    )
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)


@bot.command(name="blist")
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def banlist(ctx):
    """Afficher la liste des membres bannis du serveur."""
    bans = []
    async for ban_entry in ctx.guild.bans():
        bans.append(ban_entry)

    if not bans:
        return await ctx.send(embed=info_embed("📋 Liste des bans", "Aucun utilisateur banni sur ce serveur."))

    # Paginer par blocs de 20
    page_size = 20
    pages = [bans[i:i + page_size] for i in range(0, len(bans), page_size)]
    total = len(bans)

    for i, page in enumerate(pages):
        lines = []
        for entry in page:
            raison = (entry.reason[:40] + "…") if entry.reason and len(entry.reason) > 40 else (entry.reason or "Aucune raison")
            lines.append(f"`{entry.user.id}` — **{entry.user}** — _{raison}_")
        desc = "\n".join(lines)
        title = f"🔨 Bannis ({total} au total)" if len(pages) == 1 else f"🔨 Bannis — Page {i+1}/{len(pages)} ({total} au total)"
        e = mod_embed(title, desc, discord.Color.dark_red())
        await ctx.send(embed=e)


@bot.command(name="unbanall")
@commands.has_permissions(administrator=True)
@commands.bot_has_permissions(ban_members=True)
async def unbanall(ctx):
    """Débannir tous les utilisateurs du serveur (confirmation requise)."""
    bans = []
    async for ban_entry in ctx.guild.bans():
        bans.append(ban_entry)

    if not bans:
        return await ctx.send(embed=info_embed("✅ Unban all", "Aucun utilisateur banni à débannir."))

    confirm_msg = await ctx.send(embed=warning_embed(
        "⚠️ Confirmation requise",
        f"Tu es sur le point de débannir **{len(bans)} utilisateur(s)**.\n"
        f"Réagis avec ✅ pour confirmer ou ❌ pour annuler.\n"
        f"*(Tu as 30 secondes)*"
    ))
    await confirm_msg.add_reaction("✅")
    await confirm_msg.add_reaction("❌")

    def check(reaction, user):
        return (
            user == ctx.author
            and str(reaction.emoji) in ("✅", "❌")
            and reaction.message.id == confirm_msg.id
        )

    try:
        reaction, _ = await bot.wait_for("reaction_add", timeout=30.0, check=check)
    except asyncio.TimeoutError:
        await confirm_msg.edit(embed=warning_embed("⏰ Délai expiré", "Opération annulée (aucune confirmation reçue)."))
        return

    if str(reaction.emoji) == "❌":
        await confirm_msg.edit(embed=info_embed("❌ Annulé", "Opération annulée."))
        return

    # Lancer le débannissement
    progress = await ctx.send(embed=info_embed("⏳ En cours…", f"Débannissement de **{len(bans)}** utilisateur(s)…"))
    success_count = 0
    fail_count = 0
    for entry in bans:
        try:
            await ctx.guild.unban(entry.user, reason=f"[unbanall] Demandé par {ctx.author}")
            success_count += 1
        except Exception:
            fail_count += 1

    e = success_embed(
        "✅ Unban all terminé",
        f"**Débannis :** {success_count}\n"
        f"**Échecs :** {fail_count}\n"
        f"**Modérateur :** {ctx.author.mention}"
    )
    await progress.edit(embed=e)
    await send_log(ctx.guild, e)


@bot.command()
@commands.has_permissions(kick_members=True)
@commands.bot_has_permissions(kick_members=True)
async def kick(ctx, member: discord.Member, *, reason: str = "Aucune raison fournie"):
    """Expulser un membre du serveur."""
    if not check_hierarchy(ctx, member):
        return await ctx.reply("❌ Tu ne peux pas expulser ce membre (hiérarchie).")
    try:
        await member.send(embed=mod_embed("👢 Tu as été expulsé", f"**Serveur :** {ctx.guild.name}\n**Raison :** {reason}", discord.Color.orange()))
    except Exception:
        pass
    await member.kick(reason=f"{ctx.author} : {reason}")
    e = mod_embed("👢 Membre expulsé", f"**Cible :** {member.mention} (`{member.id}`)\n**Modérateur :** {ctx.author.mention}\n**Raison :** {reason}", discord.Color.orange())
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(moderate_members=True)
@commands.bot_has_permissions(moderate_members=True)
async def mute(ctx, member: discord.Member, duration: str, *, reason: str = "Aucune raison fournie"):
    """Rendre muet un membre. Durée : 10m, 2h, 1d (max 28j)."""
    if not check_hierarchy(ctx, member):
        return await ctx.reply("❌ Tu ne peux pas mute ce membre (hiérarchie).")
    delta = parse_duration(duration)
    if not delta:
        return await ctx.reply("❌ Durée invalide. Exemples : `10m`, `2h`, `1d`.")
    if delta > timedelta(days=28):
        return await ctx.reply("❌ Durée maximum : 28 jours.")
    until = datetime.now(timezone.utc) + delta
    await member.timeout(until, reason=f"{ctx.author} : {reason}")
    e = mod_embed(
        "🔇 Membre muet",
        f"**Cible :** {member.mention} (`{member.id}`)\n**Durée :** {duration}\n**Fin :** <t:{int(until.timestamp())}:R>\n**Modérateur :** {ctx.author.mention}\n**Raison :** {reason}",
        discord.Color.orange()
    )
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(moderate_members=True)
@commands.bot_has_permissions(moderate_members=True)
async def unmute(ctx, member: discord.Member, *, reason: str = "Aucune raison fournie"):
    """Retirer le mute d'un membre."""
    await member.timeout(None, reason=f"{ctx.author} : {reason}")
    e = success_embed("🔊 Mute retiré", f"**Cible :** {member.mention}\n**Modérateur :** {ctx.author.mention}\n**Raison :** {reason}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(kick_members=True)
async def warn(ctx, member: discord.Member, *, reason: str):
    """Avertir un membre et enregistrer l'avertissement. (3 warns = mute 1j, 5 warns = bl)"""
    if not check_hierarchy(ctx, member):
        return await ctx.reply("❌ Tu ne peux pas avertir ce membre (hiérarchie).")
    gid, uid = str(ctx.guild.id), str(member.id)
    warns_db.setdefault(gid, {}).setdefault(uid, [])
    entry = {"reason": reason, "date": datetime.now(timezone.utc).isoformat(), "mod": str(ctx.author.id)}
    warns_db[gid][uid].append(entry)
    save_warns()
    count = len(warns_db[gid][uid])
    e = warning_embed("⚠️ Avertissement", f"**Cible :** {member.mention} (`{member.id}`)\n**Raison :** {reason}\n**Total warns :** {count}\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)
    try:
        await member.send(embed=warning_embed("⚠️ Tu as reçu un avertissement", f"**Serveur :** {ctx.guild.name}\n**Raison :** {reason}\n**Total :** {count} warn(s)"))
    except Exception:
        pass
    # Paliers fixes : 3 warns = mute 1j, 5 warns = bl
    await apply_warn_milestones(ctx.guild, member, count)
    # Vérifier le seuil de warns configurable (optionnel, désactivé par défaut)
    am_cfg = get_automod_cfg(ctx.guild.id)
    await check_warn_threshold(ctx.guild, member, am_cfg)

@bot.command()
@commands.has_permissions(kick_members=True)
async def unwarn(ctx, member: discord.Member, warn_id: int):
    """Supprimer un avertissement par son numéro (commence à 1)."""
    gid, uid = str(ctx.guild.id), str(member.id)
    w_list = warns_db.get(gid, {}).get(uid, [])
    if not w_list or warn_id < 1 or warn_id > len(w_list):
        return await ctx.reply(f"❌ Warn #{warn_id} introuvable.")
    removed = w_list.pop(warn_id - 1)
    save_warns()
    e = success_embed("🗑️ Warn supprimé", f"**Cible :** {member.mention}\n**Warn supprimé :** {removed['reason']}\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)

@bot.command()
@commands.has_permissions(kick_members=True)
async def clearwarns(ctx, member: discord.Member):
    """Effacer tous les avertissements d'un membre."""
    gid, uid = str(ctx.guild.id), str(member.id)
    count = len(warns_db.get(gid, {}).get(uid, []))
    if count == 0:
        return await ctx.reply(f"✅ {member.mention} n'a aucun avertissement.")
    warns_db.setdefault(gid, {})[uid] = []
    save_warns()
    e = success_embed("🧹 Warns effacés", f"**{count}** avertissement(s) supprimé(s) pour {member.mention}\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)

@bot.command()
async def warns(ctx, member: discord.Member = None):
    """Afficher les avertissements d'un membre."""
    member = member or ctx.author
    gid, uid = str(ctx.guild.id), str(member.id)
    w_list = warns_db.get(gid, {}).get(uid, [])
    if not w_list:
        return await ctx.reply(f"✅ {member.mention} n'a aucun avertissement.")
    e = warning_embed(f"⚠️ Warns de {member}", "")
    for i, w in enumerate(w_list, 1):
        ts     = w.get("date", "?")[:10]
        mod_id = w.get("mod")
        mod_str= f"<@{mod_id}>" if mod_id else "?"
        e.add_field(name=f"#{i} — {ts}", value=f"**Raison :** {w['reason']}\n**Mod :** {mod_str}", inline=False)
    await ctx.send(embed=e)

@bot.command(name="softbl")
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def softban(ctx, member: discord.Member, *, reason: str = "Aucune raison fournie"):
    """Bannir puis débannir immédiatement (supprime les messages récents)."""
    if not check_hierarchy(ctx, member):
        return await ctx.reply("❌ Tu ne peux pas softbl ce membre.")
    await member.ban(reason=f"[SOFTBAN] {ctx.author} : {reason}", delete_message_days=7)
    await ctx.guild.unban(member, reason="Softban — déban automatique")
    e = mod_embed("🪃 Softban", f"**Cible :** {member.mention}\n**Modérateur :** {ctx.author.mention}\n**Raison :** {reason}", discord.Color.orange())
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command(name="tembl")
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def tempban(ctx, member: discord.Member, duration: str, *, reason: str = "Aucune raison fournie"):
    """Bannir temporairement un membre. Durée : 10m, 2h, 1d."""
    if not check_hierarchy(ctx, member):
        return await ctx.reply("❌ Tu ne peux pas tembl ce membre.")
    delta = parse_duration(duration)
    if not delta:
        return await ctx.reply("❌ Durée invalide. Exemples : `10m`, `2h`, `1d`.")
    until = datetime.now(timezone.utc) + delta
    until_ts = int(until.timestamp())
    try:
        await member.send(embed=mod_embed("⏳ Ban temporaire", f"**Serveur :** {ctx.guild.name}\n**Durée :** {duration}\n**Raison :** {reason}"))
    except Exception:
        pass
    try:
        await member.ban(reason=f"[TEMPBAN {duration}] {ctx.author} : {reason}", delete_message_days=1)
    except discord.Forbidden:
        return await ctx.reply("❌ Je n'ai pas la permission de bannir ce membre.")
    except discord.HTTPException as exc:
        return await ctx.reply(f"❌ Erreur lors du ban : {exc}")
    gid = str(ctx.guild.id)
    tempban_db.setdefault(gid, {})[str(member.id)] = {
        "end_ts": until_ts, "reason": reason, "mod_id": str(ctx.author.id),
    }
    save_tempbans()
    e = mod_embed(
        "⏳ Ban temporaire",
        f"**Cible :** {member.mention} (`{member.id}`)\n**Durée :** {duration}\n**Fin :** <t:{until_ts}:R>\n**Modérateur :** {ctx.author.mention}\n**Raison :** {reason}"
    )
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

    async def unban_later():
        await asyncio.sleep(delta.total_seconds())
        try:
            user = await bot.fetch_user(member.id)
            await ctx.guild.unban(user, reason="Tempban expiré")
            tempban_db.get(gid, {}).pop(str(member.id), None)
            save_tempbans()
            ue = success_embed("✅ Tempban expiré", f"**Cible :** {user} (`{user.id}`) a été débanni automatiquement.")
            await send_log(ctx.guild, ue)
        except Exception:
            pass
    asyncio.ensure_future(unban_later())

@tasks.loop(count=1)
async def resume_tempbans():
    await bot.wait_until_ready()
    now = datetime.now(timezone.utc).timestamp()
    for gid, bans in list(tempban_db.items()):
        guild = bot.get_guild(int(gid))
        if not guild:
            continue
        for uid, bdata in list(bans.items()):
            end_ts = bdata["end_ts"]
            remaining = end_ts - now
            if remaining <= 0:
                try:
                    user = await bot.fetch_user(int(uid))
                    await guild.unban(user, reason="Tempban expiré (reprise)")
                except Exception:
                    pass
                tempban_db[gid].pop(uid, None)
            else:
                async def _unban(g=guild, u_id=uid, delay=remaining, g_id=gid):
                    await asyncio.sleep(delay)
                    try:
                        user = await bot.fetch_user(int(u_id))
                        await g.unban(user, reason="Tempban expiré")
                        tempban_db.get(g_id, {}).pop(u_id, None)
                        save_tempbans()
                        ue = success_embed("✅ Tempban expiré", f"**Cible :** {user} (`{u_id}`) débanni automatiquement.")
                        await send_log(g, ue)
                    except Exception:
                        pass
                asyncio.ensure_future(_unban())
        save_tempbans()

# ─────────────────────────────────────────
#  NETTOYAGE
# ─────────────────────────────────────────
@bot.command()
@commands.has_permissions(manage_messages=True)
@commands.bot_has_permissions(manage_messages=True)
async def clear(ctx, amount: str):
    """Supprimer les N derniers messages du salon. Usage : +clear <nombre|all>"""
    await ctx.message.delete()
    is_all = amount.lower() == "all"
    if not is_all:
        try:
            amount_int = int(amount)
        except ValueError:
            return await ctx.send("❌ Utilise un nombre ou `all`.", delete_after=5)
        if amount_int < 1 or amount_int > 500:
            return await ctx.send("❌ Nombre entre 1 et 500.", delete_after=5)
    after_limit = datetime.now(timezone.utc) - timedelta(days=14)
    if is_all:
        deleted = await ctx.channel.purge(limit=None, after=after_limit)
    else:
        deleted = await ctx.channel.purge(limit=amount_int)
    e = success_embed("🧹 Nettoyage", f"**{len(deleted)}** message(s) supprimé(s).\n**Modérateur :** {ctx.author.mention}")
    msg = await ctx.send(embed=e)
    await asyncio.sleep(5)
    await msg.delete()
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_messages=True)
@commands.bot_has_permissions(manage_messages=True)
async def purge(ctx, member: discord.Member, amount: int = 100):
    """Supprimer les messages d'un membre spécifique. Usage : +purge @membre [nombre]"""
    if amount < 1 or amount > 500:
        return await ctx.reply("❌ Nombre entre 1 et 500.")
    await ctx.message.delete()
    after_limit = datetime.now(timezone.utc) - timedelta(days=14)
    deleted_count = 0
    # On scanne jusqu'à amount*5 messages max pour trouver 'amount' messages de ce membre
    async def check(m): return m.author == member
    # discord.py purge ne supporte pas un check async, on utilise une lambda
    deleted = await ctx.channel.purge(limit=min(amount * 5, 1000), check=lambda m: m.author == member, after=after_limit, bulk=True)
    # Supprimer seulement les 'amount' premiers trouvés si on en a trop
    if len(deleted) > amount:
        # On ne peut pas "remettre" les extras, mais c'est rare — la limite * 5 évite le sur-suppression
        pass
    e = success_embed("🧹 Purge", f"**{len(deleted)}** message(s) de {member.mention} supprimé(s).\n**Modérateur :** {ctx.author.mention}")
    msg = await ctx.send(embed=e)
    await asyncio.sleep(5)
    await msg.delete()
    await send_log(ctx.guild, e)

# ─────────────────────────────────────────
#  GESTION DES CANAUX
# ─────────────────────────────────────────
@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def lock(ctx, channel: discord.TextChannel = None):
    """Verrouiller un salon."""
    channel = channel or ctx.channel
    overwrite = channel.overwrites_for(ctx.guild.default_role)
    overwrite.send_messages = False
    await channel.set_permissions(ctx.guild.default_role, overwrite=overwrite)
    e = mod_embed("🔒 Salon verrouillé", f"{channel.mention} a été verrouillé.\n**Modérateur :** {ctx.author.mention}", discord.Color.orange())
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def unlock(ctx, channel: discord.TextChannel = None):
    """Déverrouiller un salon."""
    channel = channel or ctx.channel
    overwrite = channel.overwrites_for(ctx.guild.default_role)
    overwrite.send_messages = None
    await channel.set_permissions(ctx.guild.default_role, overwrite=overwrite)
    e = success_embed("🔓 Salon déverrouillé", f"{channel.mention} est maintenant ouvert.\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def slowmode(ctx, seconds: int, channel: discord.TextChannel = None):
    """Définir le slowmode. Usage : +slowmode <secondes> [#salon]"""
    channel = channel or ctx.channel
    if seconds < 0 or seconds > 21600:
        return await ctx.reply("❌ Entre 0 et 21600 secondes.")
    await channel.edit(slowmode_delay=seconds)
    if seconds == 0:
        e = success_embed("⏱️ Slowmode désactivé", f"{channel.mention} — Slowmode retiré.")
    else:
        e = info_embed("⏱️ Slowmode activé", f"{channel.mention} — **{seconds}s** entre chaque message.")
    await ctx.send(embed=e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def nuke(ctx, channel: discord.TextChannel = None):
    """Recréer un salon vierge."""
    channel = channel or ctx.channel
    confirm_msg = await ctx.send(embed=warning_embed("💥 Confirmation Nuke", f"Recréer **{channel.name}** ? Tape `CONFIRMER` dans les 15 secondes."))
    def check(m): return m.author == ctx.author and m.channel == ctx.channel and m.content == "CONFIRMER"
    try:
        await bot.wait_for("message", check=check, timeout=15)
    except asyncio.TimeoutError:
        await confirm_msg.delete()
        return await ctx.reply("❌ Nuke annulé.")
    pos = channel.position
    new_ch = await channel.clone(reason=f"Nuke par {ctx.author}")
    await channel.delete(reason=f"Nuke par {ctx.author}")
    await new_ch.edit(position=pos)
    e = mod_embed("💥 Salon nuke", f"{new_ch.mention} a été recréé.\n**Modérateur :** {ctx.author.mention}")
    await new_ch.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def createtext(ctx, nom: str, *, categorie: str = None):
    """Créer un salon textuel."""
    category = None
    if categorie:
        category = discord.utils.get(ctx.guild.categories, name=categorie)
        if not category:
            return await ctx.reply(f"❌ Catégorie `{categorie}` introuvable.")
    channel = await ctx.guild.create_text_channel(nom, category=category, reason=f"Créé par {ctx.author}")
    e = success_embed("✅ Salon textuel créé", f"**Nom :** {channel.mention}\n**Catégorie :** {category.name if category else 'Aucune'}\n**Créé par :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def createvoice(ctx, nom: str, *, categorie: str = None):
    """Créer un salon vocal."""
    category = None
    if categorie:
        category = discord.utils.get(ctx.guild.categories, name=categorie)
        if not category:
            return await ctx.reply(f"❌ Catégorie `{categorie}` introuvable.")
    channel = await ctx.guild.create_voice_channel(nom, category=category, reason=f"Créé par {ctx.author}")
    e = success_embed("✅ Salon vocal créé", f"**Nom :** {channel.name}\n**Catégorie :** {category.name if category else 'Aucune'}\n**Créé par :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def createcat(ctx, *, nom: str):
    """Créer une catégorie."""
    category = await ctx.guild.create_category(nom, reason=f"Créé par {ctx.author}")
    e = success_embed("✅ Catégorie créée", f"**Nom :** {category.name}\n**Créé par :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def deletechan(ctx, channel: discord.abc.GuildChannel):
    """Supprimer un salon."""
    nom = channel.name
    await channel.delete(reason=f"Supprimé par {ctx.author}")
    e = mod_embed("🗑️ Salon supprimé", f"**Nom :** `{nom}`\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def renamechan(ctx, channel: discord.abc.GuildChannel, *, nouveau_nom: str):
    """Renommer un salon."""
    ancien = channel.name
    await channel.edit(name=nouveau_nom, reason=f"Renommé par {ctx.author}")
    e = info_embed("✏️ Salon renommé", f"**Ancien :** `{ancien}`\n**Nouveau :** `{nouveau_nom}`\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

# ─────────────────────────────────────────
#  GIVEAWAYS
# ─────────────────────────────────────────
GIVEAWAY_EMOJI = "🎉"

def giveaway_embed(prize, winners, end_ts, host, ended=False, winner_mentions=None):
    color  = discord.Color.from_rgb(0, 0, 0)
    status = "🎉 **GIVEAWAY**" if not ended else "🏁 **GIVEAWAY TERMINÉ**"
    desc   = f"**Prix :** {prize}\n**Gagnants :** {winners}\n**Organisé par :** {host.mention}\n"
    if not ended:
        desc += f"**Se termine :** <t:{end_ts}:R>\n\nRéagis avec {GIVEAWAY_EMOJI} pour participer !"
    else:
        desc += f"**Gagnant(s) :** {', '.join(winner_mentions)}" if winner_mentions else "**Aucun participant valide.**"
    return discord.Embed(title=status, description=desc, color=color, timestamp=datetime.now(timezone.utc))

async def end_giveaway(guild, channel_id, message_id):
    gid = str(guild.id)
    mid = str(message_id)
    gdata = giveaway_db.get(gid, {}).get(mid)
    if not gdata or gdata.get("ended"):
        return
    channel = guild.get_channel(channel_id)
    if not channel:
        return
    try:
        message = await channel.fetch_message(message_id)
    except Exception:
        return
    reaction = discord.utils.get(message.reactions, emoji=GIVEAWAY_EMOJI)
    participants = []
    if reaction:
        async for user in reaction.users():
            if not user.bot:
                participants.append(user)
    nb_winners = min(gdata["winners"], len(participants))
    winners = random.sample(participants, nb_winners) if participants else []
    winner_mentions = [w.mention for w in winners]
    host = guild.get_member(gdata["host_id"]) or await bot.fetch_user(gdata["host_id"])
    await message.edit(embed=giveaway_embed(gdata["prize"], gdata["winners"], gdata["end_ts"], host, ended=True, winner_mentions=winner_mentions))
    if winners:
        await channel.send(f"🎉 Félicitations {', '.join(winner_mentions)} ! Vous avez gagné **{gdata['prize']}** !")
    else:
        await channel.send("😢 Personne n'a participé au giveaway.")
    giveaway_db[gid][mid]["ended"]     = True
    giveaway_db[gid][mid]["winner_ids"] = [w.id for w in winners]
    save_giveaways()

@tasks.loop(seconds=15)
async def check_giveaways():
    now = datetime.now(timezone.utc).timestamp()
    for gid, giveaways in list(giveaway_db.items()):
        guild = bot.get_guild(int(gid))
        if not guild:
            continue
        for mid, gdata in list(giveaways.items()):
            if not gdata.get("ended") and gdata.get("end_ts", 0) <= now:
                await end_giveaway(guild, gdata["channel_id"], int(mid))

@bot.command()
@commands.has_permissions(manage_guild=True)
async def gcreate(ctx, duration: str, winners: int, *, prize: str):
    """Lancer un giveaway. Usage : +gcreate <durée> <gagnants> <prix>"""
    delta = parse_duration(duration)
    if not delta:
        return await ctx.reply("❌ Durée invalide.")
    if not 1 <= winners <= 20:
        return await ctx.reply("❌ Entre 1 et 20 gagnants.")
    end_ts = int((datetime.now(timezone.utc) + delta).timestamp())
    msg = await ctx.send(embed=giveaway_embed(prize, winners, end_ts, ctx.author))
    await msg.add_reaction(GIVEAWAY_EMOJI)
    gid = str(ctx.guild.id)
    giveaway_db.setdefault(gid, {})[str(msg.id)] = {
        "channel_id": ctx.channel.id, "end_ts": end_ts, "winners": winners,
        "prize": prize, "host_id": ctx.author.id, "ended": False,
    }
    save_giveaways()

@bot.command()
@commands.has_permissions(manage_guild=True)
async def gend(ctx, message_id: int):
    """Terminer un giveaway immédiatement."""
    gid = str(ctx.guild.id)
    gdata = giveaway_db.get(gid, {}).get(str(message_id))
    if not gdata:
        return await ctx.reply("❌ Giveaway introuvable.")
    if gdata.get("ended"):
        return await ctx.reply("❌ Ce giveaway est déjà terminé.")
    await end_giveaway(ctx.guild, gdata["channel_id"], message_id)
    await ctx.reply("✅ Giveaway terminé.")

@bot.command()
@commands.has_permissions(manage_guild=True)
async def greroll(ctx, message_id: int):
    """Tirer un nouveau gagnant."""
    gid = str(ctx.guild.id)
    gdata = giveaway_db.get(gid, {}).get(str(message_id))
    if not gdata or not gdata.get("ended"):
        return await ctx.reply("❌ Giveaway introuvable ou pas encore terminé.")
    channel = ctx.guild.get_channel(gdata["channel_id"])
    if not channel:
        return await ctx.reply("❌ Salon introuvable.")
    try:
        message = await channel.fetch_message(message_id)
    except Exception:
        return await ctx.reply("❌ Message introuvable.")
    reaction = discord.utils.get(message.reactions, emoji=GIVEAWAY_EMOJI)
    participants = []
    if reaction:
        async for user in reaction.users():
            if not user.bot:
                participants.append(user)
    if not participants:
        return await ctx.reply("😢 Aucun participant valide.")
    winner = random.choice(participants)
    await ctx.send(f"🎉 Nouveau gagnant : {winner.mention} ! Félicitations pour **{gdata['prize']}** !")

@bot.command()
@commands.has_permissions(manage_guild=True)
async def glist(ctx):
    """Lister les giveaways actifs."""
    gid = str(ctx.guild.id)
    actifs = {mid: g for mid, g in giveaway_db.get(gid, {}).items() if not g.get("ended")}
    if not actifs:
        return await ctx.reply("ℹ️ Aucun giveaway actif.")
    e = success_embed("🎉 Giveaways actifs", "")
    for mid, g in actifs.items():
        ch = ctx.guild.get_channel(g["channel_id"])
        e.add_field(name=f"🎁 {g['prize']}", value=f"ID : `{mid}`\nSalon : {ch.mention if ch else '?'}\nFin : <t:{g['end_ts']}:R>\nGagnants : {g['winners']}", inline=False)
    await ctx.send(embed=e)

# ─────────────────────────────────────────
#  REACTION ROLES
# ─────────────────────────────────────────
@bot.command()
@commands.has_permissions(manage_roles=True)
async def reactionrole(ctx, message_id: int, emoji: str, role: discord.Role):
    """Créer un reaction role. Usage : +reactionrole <message_id> <emoji> <@rôle>"""
    try:
        msg = await ctx.channel.fetch_message(message_id)
    except discord.NotFound:
        return await ctx.reply("❌ Message introuvable dans ce salon.")
    gid = str(ctx.guild.id)
    mid = str(message_id)
    rreactions_db.setdefault(gid, {}).setdefault(mid, {})[emoji] = {
        "role_id":    str(role.id),
        "channel_id": str(ctx.channel.id),
    }
    save_rreactions()
    try:
        await msg.add_reaction(emoji)
    except discord.HTTPException:
        return await ctx.reply("❌ Emoji invalide ou impossible à ajouter.")
    e = success_embed("✅ Reaction Role créé", f"**Message :** `{message_id}`\n**Emoji :** {emoji}\n**Rôle :** {role.mention}\n\nLes membres obtiennent ce rôle en réagissant avec {emoji}.")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_roles=True)
async def removereactionrole(ctx, message_id: int, emoji: str):
    """Supprimer un reaction role. Usage : +removereactionrole <message_id> <emoji>"""
    gid = str(ctx.guild.id)
    mid = str(message_id)
    if gid not in rreactions_db or mid not in rreactions_db[gid] or emoji not in rreactions_db[gid][mid]:
        return await ctx.reply("❌ Aucun reaction role trouvé pour cet emoji sur ce message.")
    del rreactions_db[gid][mid][emoji]
    if not rreactions_db[gid][mid]:
        del rreactions_db[gid][mid]
    save_rreactions()
    await ctx.reply(embed=success_embed("✅ Reaction Role supprimé", f"L'emoji {emoji} sur le message `{message_id}` ne donne plus de rôle."))

# ─────────────────────────────────────────
#  ROLE PANEL (dropdown self-role)
# ─────────────────────────────────────────
# Fichier de persistance
ROLEPANEL_FILE = "rolepanels.json"
rolepanel_db   = load_json(ROLEPANEL_FILE)

def save_rolepanels():
    save_json(ROLEPANEL_FILE, rolepanel_db)

async def is_valid_emoji(ctx, raw_emoji: str):
    """Vérifie qu'un emoji (unicode ou custom) est valide pour Discord, en testant
    une vraie réaction sur le message de commande — c'est exactement la même
    validation que celle utilisée côté API pour les menus déroulants."""
    raw_emoji = raw_emoji.strip()
    m = re.match(r"^<a?:\w+:(\d+)>$", raw_emoji)
    if m:
        emoji_obj = bot.get_emoji(int(m.group(1)))
        if emoji_obj is None:
            return False, "Emoji personnalisé inaccessible (mauvais serveur ?)."
        return True, ""
    try:
        await ctx.message.add_reaction(raw_emoji)
        await ctx.message.remove_reaction(raw_emoji, ctx.guild.me)
        return True, ""
    except discord.HTTPException:
        return False, "Discord ne reconnaît pas ce caractère comme un emoji valide."
    except discord.Forbidden:
        return True, ""  # pas de perm pour tester → on n'empêche pas l'ajout

async def check_panel_emojis(ctx, panel: dict):
    """Teste tous les emojis d'un panel et retourne la liste des erreurs (rôle + raison)."""
    errors = []
    for opt in panel.get("options", []):
        emoji = opt.get("emoji")
        if not emoji:
            continue
        valid, reason = await is_valid_emoji(ctx, emoji)
        if not valid:
            role = ctx.guild.get_role(int(opt["role_id"]))
            role_str = role.mention if role else f"`{opt['role_id']}`"
            errors.append(f"❌ {role_str} — emoji `{emoji}` : {reason}")
    return errors

# ── Vue Select persistante ────────────────────────────────────────────────────
class RolePanelSelect(discord.ui.Select):
    """Dropdown qui attribue / retire les rôles selon le panel."""

    def __init__(self, panel_id: str, options_data: list):
        options = []
        for item in options_data:
            # Parser l'emoji de façon ultra-défensive
            parsed_emoji = None
            try:
                raw_emoji = item.get("emoji") or None
                if raw_emoji:
                    raw_emoji = raw_emoji.strip()
                    m = re.match(r"<(a?):([\w]+):(\d+)>", raw_emoji)
                    if m:
                        animated = bool(m.group(1))
                        ename    = m.group(2)
                        eid      = int(m.group(3))
                        parsed_emoji = discord.PartialEmoji(name=ename, id=eid, animated=animated)
                    else:
                        parsed_emoji = raw_emoji
            except Exception:
                parsed_emoji = None  # emoji invalide → on l'ignore

            # Créer l'option de façon défensive aussi
            try:
                label = str(item.get("label", "Rôle"))[:100]
                desc  = item.get("description") or None
                if desc:
                    desc = str(desc)[:100]
                opt = discord.SelectOption(
                    label=label,
                    value=str(item["role_id"]),
                    emoji=parsed_emoji,
                    description=desc,
                )
                options.append(opt)
            except Exception:
                # Si l'option est invalide (emoji rejeté, etc.), on réessaie sans emoji
                try:
                    opt = discord.SelectOption(
                        label=str(item.get("label", "Rôle"))[:100],
                        value=str(item["role_id"]),
                        emoji=None,
                        description=None,
                    )
                    options.append(opt)
                except Exception:
                    pass  # Option complètement invalide, on la skip

        if not options:
            options = [discord.SelectOption(label="Aucun rôle disponible", value="__none__")]

        options = options[:25]
        super().__init__(
            placeholder="Fais un choix",
            min_values=0,
            max_values=len(options),
            options=options,
            custom_id=f"rolepanel:{panel_id}",
        )
        self.panel_id = panel_id

    async def callback(self, interaction: discord.Interaction):
        guild  = interaction.guild
        member = interaction.user

        # Récupérer le panel
        gid   = str(guild.id)
        panel = rolepanel_db.get(gid, {}).get(self.panel_id)
        if not panel:
            return await interaction.response.send_message(
                "❌ Ce panel n'existe plus.", ephemeral=True
            )

        # Ensemble des role_id disponibles dans ce panel
        all_role_ids = {str(o["role_id"]) for o in panel["options"]}
        # Rôles choisis par l'utilisateur
        chosen_ids   = set(self.values)

        added   = []
        removed = []
        errors  = []

        for role_id_str in all_role_ids:
            role = guild.get_role(int(role_id_str))
            if not role:
                continue
            has_role = role in member.roles
            if role_id_str in chosen_ids and not has_role:
                try:
                    await member.add_roles(role, reason="Role Panel")
                    added.append(role.mention)
                except discord.Forbidden:
                    errors.append(role.name)
            elif role_id_str not in chosen_ids and has_role:
                try:
                    await member.remove_roles(role, reason="Role Panel")
                    removed.append(role.mention)
                except discord.Forbidden:
                    errors.append(role.name)

        lines = []
        if added:
            lines.append(f"✅ **Ajouté(s) :** {', '.join(added)}")
        if removed:
            lines.append(f"➖ **Retiré(s) :** {', '.join(removed)}")
        if errors:
            lines.append(f"❌ **Erreur (hiérarchie) :** {', '.join(errors)}")
        if not lines:
            lines.append("Aucun changement.")

        await interaction.response.send_message(
            embed=success_embed("🏷️ Rôles mis à jour", "\n".join(lines)),
            ephemeral=True,
        )

class RolePanelView(discord.ui.View):
    """Vue persistante contenant le Select d'un panel."""

    def __init__(self, panel_id: str, options_data: list):
        super().__init__(timeout=None)
        self.add_item(RolePanelSelect(panel_id, options_data))

# ── Helpers ───────────────────────────────────────────────────────────────────
def build_rolepanel_view(gid: str, panel_id: str) -> RolePanelView | None:
    panel = rolepanel_db.get(gid, {}).get(panel_id)
    if not panel or not panel.get("options"):
        return None
    return RolePanelView(panel_id, panel["options"])

def register_rolepanel_views():
    """Ré-enregistre toutes les vues persistantes au démarrage."""
    for gid, panels in rolepanel_db.items():
        for panel_id, panel in panels.items():
            if not panel.get("options"):
                continue
            view = RolePanelView(panel_id, panel["options"])
            msg_id = panel.get("message_id")
            try:
                if msg_id:
                    bot.add_view(view, message_id=int(msg_id))
                else:
                    bot.add_view(view)
            except Exception:
                pass

def build_rolepanel_embed(panel: dict) -> discord.Embed:
    """Construit l'embed d'un panel."""
    title = panel.get("title", "🏷️ Rôles")
    desc  = panel.get("description", "Sélectionne les rôles que tu souhaites recevoir.")
    color_hex = panel.get("color", "000000")
    try:
        color = discord.Color(int(color_hex.lstrip("#"), 16))
    except Exception:
        color = discord.Color.from_rgb(0, 0, 0)

    e = discord.Embed(title=title, description=desc, color=color)
    # Lister les options
    lines = []
    for opt in panel.get("options", []):
        emoji = opt.get("emoji") or "•"
        label = opt["label"]
        role_id = opt["role_id"]
        desc_opt = opt.get("description", "")
        line = f"{emoji} <@&{role_id}>"
        if desc_opt:
            line += f" — *{desc_opt}*"
        lines.append(line)
    if lines:
        e.add_field(name="\u200b", value="\n".join(lines), inline=False)
    thumbnail = panel.get("thumbnail")
    if thumbnail:
        e.set_thumbnail(url=thumbnail)
    footer = panel.get("footer")
    if footer:
        e.set_footer(text=footer)
    return e

# ── Commandes ─────────────────────────────────────────────────────────────────
@bot.command(name="rolepanel")
@commands.has_permissions(manage_roles=True)
async def rolepanel_cmd(ctx, *, args: str = ""):
    """Système de panneau de rôles (dropdown). Usage : +rolepanel <sous-commande>

    Sous-commandes :
      create <id>                          — créer un nouveau panel
      title  <id> <texte>                  — définir le titre de l'embed
      desc   <id> <texte>                  — définir la description
      color  <id> <#hexcode>               — couleur de l'embed (ex: #7289DA)
      thumbnail <id> <url>                 — miniature de l'embed
      footer <id> <texte>                  — footer de l'embed
      add    <id> @rôle [emoji] [desc]     — ajouter une option
      remove <id> @rôle                    — retirer une option
      send   <id>                          — envoyer le panel dans ce salon
      delete <id>                          — supprimer un panel
      list                                 — lister les panels du serveur
      preview <id>                         — prévisualiser sans envoyer
    """
    gid    = str(ctx.guild.id)
    parts  = args.split()

    if not parts:
        return await ctx.reply(embed=info_embed(
            "🏷️ Role Panel — Aide",
            "**+rolepanel create <id>** — créer un panel\n"
            "**+rolepanel title <id> <texte>** — titre de l'embed\n"
            "**+rolepanel desc <id> <texte>** — description\n"
            "**+rolepanel color <id> #hexcode** — couleur\n"
            "**+rolepanel thumbnail <id> <url>** — image\n"
            "**+rolepanel footer <id> <texte>** — footer\n"
            "**+rolepanel add <id> @rôle [emoji] [desc]** — ajouter un rôle\n"
            "**+rolepanel remove <id> @rôle** — retirer un rôle\n"
            "**+rolepanel send <id>** — envoyer ici\n"
            "**+rolepanel delete <id>** — supprimer\n"
            "**+rolepanel list** — lister\n"
            "**+rolepanel preview <id>** — prévisualiser"
        ))

    sub = parts[0].lower()

    # ── list ──────────────────────────────────────────────────────────────────
    if sub == "list":
        panels = rolepanel_db.get(gid, {})
        if not panels:
            return await ctx.reply("❌ Aucun panel sur ce serveur.")
        lines = []
        for pid, panel in panels.items():
            n_opts = len(panel.get("options", []))
            sent   = "✅ envoyé" if panel.get("message_id") else "⏳ non envoyé"
            lines.append(f"• **{pid}** — *{panel.get('title','Sans titre')}* — {n_opts} rôle(s) — {sent}")
        return await ctx.reply(embed=info_embed("🏷️ Role Panels", "\n".join(lines)))

    # ── Sous-commandes nécessitant un <id> ───────────────────────────────────
    if len(parts) < 2:
        return await ctx.reply("❌ Précise l'ID du panel. Ex : `+rolepanel create monpanel`")
    panel_id = parts[1].lower()
    rolepanel_db.setdefault(gid, {})

    # ── create ────────────────────────────────────────────────────────────────
    if sub == "create":
        if panel_id in rolepanel_db[gid]:
            return await ctx.reply(f"❌ Un panel avec l'ID `{panel_id}` existe déjà.")
        rolepanel_db[gid][panel_id] = {
            "title":       "🏷️ Rôles Notifications",
            "description": "Sélectionne les rôles que tu souhaites recevoir.",
            "color":       "000000",
            "thumbnail":   None,
            "footer":      None,
            "options":     [],
            "message_id":  None,
            "channel_id":  None,
        }
        save_rolepanels()
        return await ctx.reply(embed=success_embed(
            "✅ Panel créé",
            f"Panel `{panel_id}` créé.\n"
            f"Ajoute des rôles avec `+rolepanel add {panel_id} @rôle [emoji] [desc]`\n"
            f"Puis envoie-le avec `+rolepanel send {panel_id}`"
        ))

    # ── Vérifier existence pour les autres sous-commandes ─────────────────────
    if sub not in ("create",) and panel_id not in rolepanel_db.get(gid, {}):
        return await ctx.reply(f"❌ Panel `{panel_id}` introuvable. Crée-le avec `+rolepanel create {panel_id}`.")

    panel = rolepanel_db[gid][panel_id]

    # ── title ─────────────────────────────────────────────────────────────────
    if sub == "title":
        text = " ".join(parts[2:])
        if not text:
            return await ctx.reply("❌ Précise le titre.")
        panel["title"] = text
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Titre mis à jour", f"**{text}**"))

    # ── desc ──────────────────────────────────────────────────────────────────
    elif sub == "desc":
        text = " ".join(parts[2:])
        if not text:
            return await ctx.reply("❌ Précise la description.")
        panel["description"] = text
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Description mise à jour", text))

    # ── color ─────────────────────────────────────────────────────────────────
    elif sub == "color":
        if len(parts) < 3:
            return await ctx.reply("❌ Précise un code hex. Ex : `#7289DA`")
        hex_code = parts[2].lstrip("#")
        try:
            int(hex_code, 16)
            assert len(hex_code) == 6
        except Exception:
            return await ctx.reply("❌ Code hex invalide. Exemple : `#7289DA`")
        panel["color"] = hex_code
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Couleur mise à jour", f"#{hex_code}"))

    # ── thumbnail ─────────────────────────────────────────────────────────────
    elif sub == "thumbnail":
        if len(parts) < 3:
            return await ctx.reply("❌ Précise une URL d'image.")
        panel["thumbnail"] = parts[2]
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Thumbnail mis à jour", parts[2]))

    # ── footer ────────────────────────────────────────────────────────────────
    elif sub == "footer":
        text = " ".join(parts[2:])
        if not text:
            return await ctx.reply("❌ Précise le texte du footer.")
        panel["footer"] = text
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Footer mis à jour", text))

    # ── add ───────────────────────────────────────────────────────────────────
    elif sub == "add":
        # +rolepanel add <id> @rôle [emoji] [description...]
        if len(parts) < 3:
            return await ctx.reply("❌ Précise un rôle. Ex : `+rolepanel add monpanel @Informations 🔔`")
        # Extraire le rôle (mention ou ID)
        role = None
        try:
            role = await commands.RoleConverter().convert(ctx, parts[2])
        except Exception:
            return await ctx.reply("❌ Rôle introuvable.")
        if role >= ctx.guild.me.top_role:
            return await ctx.reply("❌ Je ne peux pas gérer ce rôle (hiérarchie).")
        if len(panel["options"]) >= 25:
            return await ctx.reply("❌ Maximum 25 options par panel (limite Discord).")
        # Déjà présent ?
        for opt in panel["options"]:
            if opt["role_id"] == role.id:
                return await ctx.reply(f"❌ {role.mention} est déjà dans ce panel.")
        emoji = parts[3] if len(parts) > 3 else None
        desc  = " ".join(parts[4:]) if len(parts) > 4 else None
        if emoji:
            valid, reason = await is_valid_emoji(ctx, emoji)
            if not valid:
                return await ctx.reply(
                    f"❌ Emoji invalide pour {role.mention} : `{emoji}`. {reason}\n"
                    f"Réessaie avec un emoji copié directement depuis le picker Discord, ou laisse ce champ vide."
                )
        panel["options"].append({
            "label":       role.name,
            "role_id":     role.id,
            "emoji":       emoji,
            "description": desc,
        })
        save_rolepanels()
        return await ctx.reply(embed=success_embed(
            "✅ Option ajoutée",
            f"{emoji or ''} {role.mention}" + (f"\n*{desc}*" if desc else "")
        ))

    # ── remove ────────────────────────────────────────────────────────────────
    elif sub == "remove":
        if len(parts) < 3:
            return await ctx.reply("❌ Précise un rôle.")
        try:
            role = await commands.RoleConverter().convert(ctx, parts[2])
        except Exception:
            return await ctx.reply("❌ Rôle introuvable.")
        before = len(panel["options"])
        panel["options"] = [o for o in panel["options"] if o["role_id"] != role.id]
        if len(panel["options"]) == before:
            return await ctx.reply(f"❌ {role.mention} n'est pas dans ce panel.")
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Option retirée", role.mention))

    # ── preview ───────────────────────────────────────────────────────────────
    elif sub == "preview":
        if not panel["options"]:
            return await ctx.reply("❌ Aucune option dans ce panel. Ajoute des rôles avec `+rolepanel add`.")
        bad = await check_panel_emojis(ctx, panel)
        if bad:
            return await ctx.reply(embed=warning_embed(
                "⚠️ Emoji(s) invalide(s) détecté(s)",
                "\n".join(bad) +
                f"\n\nCorrige avec `{PREFIX}rolepanel remove {panel_id} @rôle` "
                f"puis `{PREFIX}rolepanel add {panel_id} @rôle <nouvel_emoji>`."
            ))
        embed = build_rolepanel_embed(panel)
        view  = RolePanelView(panel_id, panel["options"])
        return await ctx.send(
            content="👁️ **Prévisualisation** (non sauvegardée)",
            embed=embed,
            view=view
        )

    # ── send ──────────────────────────────────────────────────────────────────
    elif sub == "send":
        if not panel["options"]:
            return await ctx.reply("❌ Aucune option dans ce panel. Ajoute des rôles avec `+rolepanel add`.")
        bad = await check_panel_emojis(ctx, panel)
        if bad:
            return await ctx.reply(embed=warning_embed(
                "⚠️ Emoji(s) invalide(s) détecté(s)",
                "\n".join(bad) +
                f"\n\nCorrige avec `{PREFIX}rolepanel remove {panel_id} @rôle` "
                f"puis `{PREFIX}rolepanel add {panel_id} @rôle <nouvel_emoji>`."
            ))
        try:
            embed = build_rolepanel_embed(panel)
            view  = RolePanelView(panel_id, panel["options"])
        except Exception as e:
            import traceback as _tb
            log.error(f"[rolepanel send] Erreur construction view/embed : {_tb.format_exc()}")
            return await ctx.reply(f"❌ Erreur lors de la construction du panel : `{e}`")
        # Supprimer le message précédent si on renvoie
        if panel.get("message_id") and panel.get("channel_id"):
            try:
                old_ch = ctx.guild.get_channel(int(panel["channel_id"]))
                if old_ch:
                    old_msg = await old_ch.fetch_message(int(panel["message_id"]))
                    await old_msg.delete()
            except Exception:
                pass
        try:
            msg = await ctx.send(embed=embed, view=view)
        except Exception as e:
            import traceback as _tb
            log.error(f"[rolepanel send] Erreur ctx.send : {_tb.format_exc()}")
            return await ctx.reply(f"❌ Erreur lors de l'envoi : `{e}`")
        bot.add_view(view, message_id=msg.id)
        panel["message_id"] = str(msg.id)
        panel["channel_id"] = str(ctx.channel.id)
        save_rolepanels()
        # Supprimer le message de commande
        try:
            await ctx.message.delete()
        except Exception:
            pass

    # ── delete ────────────────────────────────────────────────────────────────
    elif sub == "delete":
        # Supprimer le message Discord si présent
        if panel.get("message_id") and panel.get("channel_id"):
            try:
                ch = ctx.guild.get_channel(int(panel["channel_id"]))
                if ch:
                    msg = await ch.fetch_message(int(panel["message_id"]))
                    await msg.delete()
            except Exception:
                pass
        del rolepanel_db[gid][panel_id]
        save_rolepanels()
        return await ctx.reply(embed=success_embed("✅ Panel supprimé", f"Le panel `{panel_id}` a été supprimé."))

    else:
        await ctx.reply(f"❌ Sous-commande inconnue : `{sub}`. Tape `+rolepanel` pour l'aide.")

# ─────────────────────────────────────────
#  RÔLES TEMPORAIRES
# ─────────────────────────────────────────
@bot.command()
@commands.has_permissions(manage_roles=True)
@commands.bot_has_permissions(manage_roles=True)
async def temprole(ctx, member: discord.Member, role: discord.Role, duration: str):
    """Donner un rôle temporairement. Usage : +temprole @membre @rôle <durée>"""
    delta = parse_duration(duration)
    if not delta:
        return await ctx.reply("❌ Durée invalide. Exemples : `10m`, `2h`, `1d`.")
    if role >= ctx.guild.me.top_role:
        return await ctx.reply("❌ Je ne peux pas gérer ce rôle (hiérarchie).")
    await member.add_roles(role, reason=f"Rôle temp par {ctx.author} ({duration})")
    end_ts = int((datetime.now(timezone.utc) + delta).timestamp())
    gid = str(ctx.guild.id)
    key = f"{member.id}_{role.id}"
    temproles_db.setdefault(gid, {})[key] = {
        "member_id":  str(member.id),
        "role_id":    str(role.id),
        "end_ts":     end_ts,
        "guild_id":   str(ctx.guild.id),
    }
    save_temproles()
    e = success_embed(
        "⏳ Rôle temporaire attribué",
        f"**Membre :** {member.mention}\n**Rôle :** {role.mention}\n**Durée :** {duration}\n**Expiration :** <t:{end_ts}:R>\n**Modérateur :** {ctx.author.mention}"
    )
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

    async def remove_later():
        await asyncio.sleep(delta.total_seconds())
        try:
            await member.remove_roles(role, reason="Rôle temporaire expiré")
            temproles_db.get(gid, {}).pop(key, None)
            save_temproles()
            re_e = info_embed("⏰ Rôle temporaire expiré", f"**Membre :** {member.mention}\n**Rôle :** {role.mention} retiré automatiquement.")
            await send_log(ctx.guild, re_e)
        except Exception:
            pass
    asyncio.ensure_future(remove_later())

@tasks.loop(count=1)
async def check_temproles():
    """Reprend les temproles persistés au redémarrage."""
    await bot.wait_until_ready()
    now = datetime.now(timezone.utc).timestamp()
    for gid, roles in list(temproles_db.items()):
        guild = bot.get_guild(int(gid))
        if not guild:
            continue
        for key, rdata in list(roles.items()):
            remaining = rdata["end_ts"] - now
            member = guild.get_member(int(rdata["member_id"]))
            role   = guild.get_role(int(rdata["role_id"]))
            if not member or not role:
                temproles_db[gid].pop(key, None)
                continue
            if remaining <= 0:
                try:
                    await member.remove_roles(role, reason="Rôle temporaire expiré (reprise)")
                except Exception:
                    pass
                temproles_db[gid].pop(key, None)
            else:
                async def _remove(m=member, r=role, g=guild, g_id=gid, k=key, delay=remaining):
                    await asyncio.sleep(delay)
                    try:
                        await m.remove_roles(r, reason="Rôle temporaire expiré")
                        temproles_db.get(g_id, {}).pop(k, None)
                        save_temproles()
                        re_e = info_embed("⏰ Rôle temporaire expiré", f"**Membre :** {m.mention}\n**Rôle :** {r.mention} retiré automatiquement.")
                        await send_log(g, re_e)
                    except Exception:
                        pass
                asyncio.ensure_future(_remove())
        save_temproles()

# ─────────────────────────────────────────
#  SYSTÈME DE TICKETS — par boutons, personnalisable
# ─────────────────────────────────────────
TICKET_SETTINGS_DEFAULTS = {
    "max_per_user":  1,                 # nb de tickets ouverts simultanément autorisés / membre
    "confirm_close": True,              # demander confirmation avant fermeture
    "ping_staff":    True,              # ping le(s) rôle(s) staff à l'ouverture
    "naming":        "ticket-{user}",   # motif du nom de salon : {user} {type} {number}
    "log_channel":   None,              # salon où sont envoyés les transcripts (sinon fallback +setlog)
    "next_number":   0,                 # compteur auto-incrémenté pour {number}
}

BUTTON_STYLES = {
    "primary":   discord.ButtonStyle.primary,
    "secondary": discord.ButtonStyle.secondary,
    "success":   discord.ButtonStyle.success,
    "danger":    discord.ButtonStyle.danger,
}

def get_ticket_cfg(guild_id) -> dict:
    """Retourne (et initialise si besoin) la config tickets d'un serveur, avec migration
    automatique depuis l'ancien système (+setticket / +setstaffrole)."""
    gid = str(guild_id)
    tcfg = tickets_db.setdefault(gid, {})
    tcfg.setdefault("settings", {})
    tcfg.setdefault("types", {})
    tcfg.setdefault("panels", {})
    tcfg.setdefault("open", {})
    for k, v in TICKET_SETTINGS_DEFAULTS.items():
        tcfg["settings"].setdefault(k, v)

    if not tcfg.get("_migrated"):
        old_cfg = config_db.get(gid, {})
        old_cat  = old_cfg.get("ticket_category")
        old_role = old_cfg.get("ticket_staff_role")
        if (old_cat or old_role) and not tcfg["types"]:
            tcfg["types"]["support"] = {
                "label":           "Support",
                "emoji":           "🎫",
                "style":           "primary",
                "category_id":     str(old_cat) if old_cat else None,
                "staff_roles":     [str(old_role)] if old_role else [],
                "welcome_message": None,
                "questions":       [],
            }
        tcfg["_migrated"] = True
        save_tickets()
    return tcfg

def slugify(text: str) -> str:
    text = text.strip().lower()
    text = re.sub(r"[^a-z0-9\-_]+", "-", text)
    text = re.sub(r"-{2,}", "-", text).strip("-")
    return text[:40]

def sanitize_channel_name(name: str) -> str:
    name = name.lower()
    name = re.sub(r"[^a-z0-9\-_]+", "-", name)
    name = re.sub(r"-{2,}", "-", name).strip("-")
    return name[:90] or "ticket"

def is_ticket_staff(member: discord.Member, ttype: dict) -> bool:
    """Un membre est considéré staff d'un type de ticket s'il a manage_guild/manage_channels/admin,
    ou s'il possède l'un des rôles staff définis sur ce type."""
    perms = member.guild_permissions
    if perms.administrator or perms.manage_channels or perms.manage_guild:
        return True
    member_role_ids = {str(r.id) for r in member.roles}
    return bool(member_role_ids & set(ttype.get("staff_roles", [])))

def get_open_ticket(guild_id, channel_id):
    """Retourne (tdata, ttype) si le salon donné est un ticket actif, sinon (None, None)."""
    tcfg = get_ticket_cfg(guild_id)
    tdata = tcfg["open"].get(str(channel_id))
    if not tdata:
        return None, None
    ttype = tcfg["types"].get(tdata.get("type_id"), {})
    return tdata, ttype

def build_panel_view(gid: str, type_ids: list) -> discord.ui.View:
    """Construit la vue (menu déroulant d'ouverture) à partir des types de tickets actuels."""
    view = discord.ui.View(timeout=None)
    view.add_item(TicketOpenSelect(gid, type_ids))
    return view

async def refresh_panels(guild: discord.Guild):
    """Met à jour tous les panneaux existants d'un serveur (boutons supprimés/édités) et nettoie
    les panneaux dont le salon/message n'existe plus."""
    gid = str(guild.id)
    tcfg = get_ticket_cfg(gid)
    changed = False
    for msg_id, panel in list(tcfg["panels"].items()):
        channel = guild.get_channel(int(panel["channel_id"]))
        if not channel:
            tcfg["panels"].pop(msg_id, None)
            changed = True
            continue
        try:
            message = await channel.fetch_message(int(msg_id))
        except (discord.NotFound, discord.Forbidden, discord.HTTPException):
            tcfg["panels"].pop(msg_id, None)
            changed = True
            continue
        type_ids = [tid for tid in panel.get("type_ids", []) if tid in tcfg["types"]]
        if type_ids != panel.get("type_ids"):
            panel["type_ids"] = type_ids
            changed = True
        view = build_panel_view(gid, type_ids)
        try:
            await message.edit(view=view)
            bot.add_view(view, message_id=message.id)
        except Exception:
            pass
    if changed:
        save_tickets()

def register_ticket_views():
    """Réenregistre toutes les vues persistantes (boutons) au démarrage du bot, pour qu'elles
    fonctionnent même après un redémarrage."""
    try:
        bot.add_view(TicketManageView())
    except Exception:
        pass
    for gid, tcfg in tickets_db.items():
        for msg_id, panel in tcfg.get("panels", {}).items():
            type_ids = [t for t in panel.get("type_ids", []) if t in tcfg.get("types", {})]
            if not type_ids:
                continue
            try:
                view = build_panel_view(gid, type_ids)
                bot.add_view(view, message_id=int(msg_id))
            except Exception:
                pass

async def close_ticket_channel(channel: discord.TextChannel, closer: discord.abc.User):
    """Logique partagée de fermeture : transcript, log, suppression du salon."""
    guild = channel.guild
    gid = str(guild.id)
    tcfg = get_ticket_cfg(gid)
    tdata = tcfg["open"].pop(str(channel.id), None)
    save_tickets()
    if tdata is None:
        return

    ttype = tcfg["types"].get(tdata.get("type_id"), {})
    owner = guild.get_member(int(tdata["owner_id"])) if tdata.get("owner_id") else None

    transcript_lines = []
    try:
        async for msg in channel.history(limit=500, oldest_first=True):
            ts = msg.created_at.strftime("%Y-%m-%d %H:%M")
            content = msg.content or "[sans texte]"
            if msg.attachments:
                content += " " + " ".join(a.url for a in msg.attachments)
            transcript_lines.append(f"[{ts}] {msg.author} : {content}")
    except Exception:
        pass
    transcript_bytes = "\n".join(transcript_lines).encode("utf-8")

    log_ch_id = tcfg["settings"].get("log_channel") or get_guild_cfg(guild.id).get("log_channel")
    if log_ch_id:
        log_ch = guild.get_channel(int(log_ch_id))
        if log_ch:
            claimer = guild.get_member(int(tdata["claimed_by"])) if tdata.get("claimed_by") else None
            e = info_embed(
                "🎫 Ticket fermé",
                f"**Salon :** {channel.name}\n"
                f"**Type :** {ttype.get('label', '?')}\n"
                f"**Propriétaire :** {owner.mention if owner else tdata.get('owner_id', '?')}\n"
                f"**Fermé par :** {closer.mention}\n"
                f"**Réclamé par :** {claimer.mention if claimer else 'Personne'}"
            )
            try:
                await log_ch.send(
                    embed=e,
                    file=discord.File(BytesIO(transcript_bytes), filename=f"transcript-{channel.name}.txt")
                )
            except (discord.Forbidden, discord.HTTPException):
                pass

    try:
        await channel.send(embed=info_embed("🎫 Ticket fermé", f"Fermé par {closer.mention}. Ce salon sera supprimé dans 5 secondes."))
    except Exception:
        pass
    await asyncio.sleep(5)
    try:
        await channel.delete(reason=f"Ticket fermé par {closer}")
    except discord.Forbidden:
        pass

# ── Composants UI ─────────────────────────────────────────────────────────

class TicketOpenSelect(discord.ui.Select):
    """Menu déroulant utilisé sur le panneau de tickets : chaque option correspond à un type de
    ticket configuré. Remplace l'ancien système par boutons pour un rendu plus propre, surtout
    quand il y a beaucoup de catégories (jusqu'à 25 options vs 25 boutons qui prennent 5 lignes)."""
    def __init__(self, gid: str, type_ids: list):
        tcfg = get_ticket_cfg(gid)
        options = []
        for tid in type_ids:
            t = tcfg["types"].get(tid)
            if not t:
                continue
            emoji = t.get("emoji") or None
            try:
                options.append(discord.SelectOption(
                    label=t.get("label", tid)[:100],
                    value=tid,
                    description=(t.get("description") or "Ouvrir un ticket dans cette catégorie")[:100],
                    emoji=emoji,
                ))
            except Exception:
                # emoji invalide : on retente sans emoji plutôt que de casser tout le panneau
                options.append(discord.SelectOption(
                    label=t.get("label", tid)[:100],
                    value=tid,
                    description=(t.get("description") or "Ouvrir un ticket dans cette catégorie")[:100],
                ))
        if not options:
            options = [discord.SelectOption(label="Aucune catégorie disponible", value="__none__")]
        super().__init__(
            placeholder="🎫 Choisissez une catégorie…",
            min_values=1,
            max_values=1,
            options=options,
            custom_id="ticket_open_select",
        )

    async def callback(self, interaction: discord.Interaction):
        type_id = self.values[0]
        if type_id == "__none__":
            return await interaction.response.send_message("❌ Aucune catégorie de ticket n'est configurée.", ephemeral=True)
        await handle_ticket_button(interaction, type_id)

class TicketOpenModal(discord.ui.Modal):
    def __init__(self, type_id: str, questions: list):
        ttype_label = "Nouveau ticket"
        super().__init__(title=ttype_label[:45])
        self.type_id = type_id
        self.answer_inputs = []
        for q in questions[:5]:
            ti = discord.ui.TextInput(
                label=q["label"][:45],
                style=discord.TextStyle.paragraph if q.get("style") == "long" else discord.TextStyle.short,
                required=q.get("required", True),
                max_length=1000 if q.get("style") == "long" else 200,
            )
            self.add_item(ti)
            self.answer_inputs.append((q["label"], ti))

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True, thinking=True)
        answers = [(label, ti.value) for label, ti in self.answer_inputs]
        await create_ticket_channel(interaction, self.type_id, answers)

    async def on_error(self, interaction: discord.Interaction, error: Exception):
        log.error(f"Erreur dans TicketOpenModal : {error}")
        try:
            await interaction.response.send_message("❌ Une erreur est survenue lors de la création du ticket.", ephemeral=True)
        except discord.InteractionResponded:
            await interaction.followup.send("❌ Une erreur est survenue lors de la création du ticket.", ephemeral=True)

class TicketMemberModal(discord.ui.Modal):
    def __init__(self, action: str):
        super().__init__(title="Ajouter un membre" if action == "add" else "Retirer un membre")
        self.action = action
        self.member_input = discord.ui.TextInput(
            label="ID ou nom du membre",
            placeholder="Ex : 123456789012345678 ou Pseudo",
            required=True,
            max_length=100,
        )
        self.add_item(self.member_input)

    async def on_submit(self, interaction: discord.Interaction):
        raw = self.member_input.value.strip().strip("<@!>")
        member = None
        if raw.isdigit():
            member = interaction.guild.get_member(int(raw))
        if not member:
            member = discord.utils.find(
                lambda m: m.name.lower() == raw.lower() or (m.nick or "").lower() == raw.lower() or str(m.display_name).lower() == raw.lower(),
                interaction.guild.members
            )
        if not member:
            return await interaction.response.send_message("❌ Membre introuvable. Utilise un ID valide ou un nom exact.", ephemeral=True)

        tdata, _ = get_open_ticket(interaction.guild.id, interaction.channel.id)
        if tdata is None:
            return await interaction.response.send_message("❌ Ce salon n'est plus un ticket actif.", ephemeral=True)

        try:
            if self.action == "add":
                await interaction.channel.set_permissions(member, view_channel=True, send_messages=True, read_message_history=True, attach_files=True)
                added = tdata.setdefault("added_members", [])
                if str(member.id) not in added:
                    added.append(str(member.id))
                save_tickets()
                await interaction.response.send_message(embed=success_embed("➕ Membre ajouté", f"{member.mention} a été ajouté à ce ticket par {interaction.user.mention}."))
            else:
                await interaction.channel.set_permissions(member, overwrite=None)
                added = tdata.get("added_members", [])
                if str(member.id) in added:
                    added.remove(str(member.id))
                save_tickets()
                await interaction.response.send_message(embed=success_embed("➖ Membre retiré", f"{member.mention} a été retiré de ce ticket par {interaction.user.mention}."))
        except discord.Forbidden:
            await interaction.response.send_message("❌ Permissions insuffisantes pour modifier ce salon.", ephemeral=True)

class TicketCloseConfirmView(discord.ui.View):
    def __init__(self, requester: discord.abc.User):
        super().__init__(timeout=60)
        self.requester = requester

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True

    @discord.ui.button(label="Confirmer", style=discord.ButtonStyle.danger, emoji="✅")
    async def confirm(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.requester.id:
            return await interaction.response.send_message("❌ Seule la personne ayant initié la fermeture peut confirmer.", ephemeral=True)
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content="🔒 Fermeture en cours...", view=self)
        await close_ticket_channel(interaction.channel, interaction.user)

    @discord.ui.button(label="Annuler", style=discord.ButtonStyle.secondary, emoji="✖️")
    async def cancel(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.requester.id:
            return await interaction.response.send_message("❌ Seule la personne ayant initié la fermeture peut annuler.", ephemeral=True)
        await interaction.response.edit_message(content="❌ Fermeture annulée.", view=None)

class TicketManageView(discord.ui.View):
    """Vue persistante envoyée dans chaque salon de ticket (Réclamer / Ajouter / Retirer / Fermer)."""
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="Réclamer", emoji="🙋", style=discord.ButtonStyle.secondary, custom_id="ticket_claim")
    async def claim_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        tdata, ttype = get_open_ticket(interaction.guild.id, interaction.channel.id)
        if tdata is None:
            return await interaction.response.send_message("❌ Ce salon n'est pas un ticket actif.", ephemeral=True)
        if not is_ticket_staff(interaction.user, ttype):
            return await interaction.response.send_message("❌ Tu n'as pas la permission de réclamer ce ticket.", ephemeral=True)
        if tdata.get("claimed_by"):
            claimer = interaction.guild.get_member(int(tdata["claimed_by"]))
            return await interaction.response.send_message(f"❌ Déjà réclamé par {claimer.mention if claimer else 'un membre du staff'}.", ephemeral=True)
        tdata["claimed_by"] = str(interaction.user.id)
        save_tickets()
        await interaction.response.send_message(embed=success_embed("🙋 Ticket réclamé", f"{interaction.user.mention} prend en charge ce ticket."))

    @discord.ui.button(label="Ajouter", emoji="➕", style=discord.ButtonStyle.secondary, custom_id="ticket_add_member")
    async def add_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        tdata, ttype = get_open_ticket(interaction.guild.id, interaction.channel.id)
        if tdata is None:
            return await interaction.response.send_message("❌ Ce salon n'est pas un ticket actif.", ephemeral=True)
        if not is_ticket_staff(interaction.user, ttype):
            return await interaction.response.send_message("❌ Tu n'as pas la permission d'ajouter un membre.", ephemeral=True)
        await interaction.response.send_modal(TicketMemberModal("add"))

    @discord.ui.button(label="Retirer", emoji="➖", style=discord.ButtonStyle.secondary, custom_id="ticket_remove_member")
    async def remove_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        tdata, ttype = get_open_ticket(interaction.guild.id, interaction.channel.id)
        if tdata is None:
            return await interaction.response.send_message("❌ Ce salon n'est pas un ticket actif.", ephemeral=True)
        if not is_ticket_staff(interaction.user, ttype):
            return await interaction.response.send_message("❌ Tu n'as pas la permission de retirer un membre.", ephemeral=True)
        await interaction.response.send_modal(TicketMemberModal("remove"))

    @discord.ui.button(label="Fermer", emoji="🔒", style=discord.ButtonStyle.danger, custom_id="ticket_close")
    async def close_btn(self, interaction: discord.Interaction, button: discord.ui.Button):
        tdata, ttype = get_open_ticket(interaction.guild.id, interaction.channel.id)
        if tdata is None:
            return await interaction.response.send_message("❌ Ce salon n'est pas un ticket actif.", ephemeral=True)
        is_owner = str(interaction.user.id) == tdata.get("owner_id")
        if not (is_owner or is_ticket_staff(interaction.user, ttype)):
            return await interaction.response.send_message("❌ Tu n'es pas autorisé à fermer ce ticket.", ephemeral=True)

        tcfg = get_ticket_cfg(interaction.guild.id)
        if not tcfg["settings"].get("confirm_close", True):
            await interaction.response.send_message("🔒 Fermeture du ticket en cours...", ephemeral=True)
            return await close_ticket_channel(interaction.channel, interaction.user)

        view = TicketCloseConfirmView(interaction.user)
        await interaction.response.send_message("⚠️ Confirmer la fermeture de ce ticket ?", view=view, ephemeral=True)

# ── Ouverture d'un ticket ───────────────────────────────────────────────────

async def handle_ticket_button(interaction: discord.Interaction, type_id: str):
    gid = str(interaction.guild.id)
    tcfg = get_ticket_cfg(gid)
    ttype = tcfg["types"].get(type_id)
    if not ttype:
        return await interaction.response.send_message("❌ Ce type de ticket n'est plus disponible. Préviens un administrateur.", ephemeral=True)

    uid = str(interaction.user.id)
    settings = tcfg["settings"]
    max_per_user = settings.get("max_per_user", 1)
    open_count = sum(1 for t in tcfg["open"].values() if t.get("owner_id") == uid)
    if open_count >= max_per_user:
        word = "un ticket" if max_per_user == 1 else f"{max_per_user} tickets"
        return await interaction.response.send_message(f"❌ Tu as déjà {word} ouvert(s). Ferme-le avant d'en ouvrir un nouveau.", ephemeral=True)

    questions = ttype.get("questions", [])
    if questions:
        return await interaction.response.send_modal(TicketOpenModal(type_id, questions))

    await interaction.response.defer(ephemeral=True, thinking=True)
    await create_ticket_channel(interaction, type_id, answers=None)

async def create_ticket_channel(interaction: discord.Interaction, type_id: str, answers=None):
    """Crée réellement le salon de ticket. Suppose que l'interaction a déjà reçu une réponse
    (defer) et utilise donc interaction.followup pour les messages de retour."""
    guild = interaction.guild
    member = interaction.user
    gid = str(guild.id)
    tcfg = get_ticket_cfg(gid)
    ttype = tcfg["types"].get(type_id)
    if not ttype:
        return await interaction.followup.send("❌ Ce type de ticket n'est plus disponible.", ephemeral=True)

    settings = tcfg["settings"]
    uid = str(member.id)

    # Double vérification de la limite (entre l'ouverture du modal et sa soumission, la situation peut changer)
    max_per_user = settings.get("max_per_user", 1)
    open_count = sum(1 for t in tcfg["open"].values() if t.get("owner_id") == uid)
    if open_count >= max_per_user:
        word = "un ticket" if max_per_user == 1 else f"{max_per_user} tickets"
        return await interaction.followup.send(f"❌ Tu as déjà {word} ouvert(s).", ephemeral=True)

    category = guild.get_channel(int(ttype["category_id"])) if ttype.get("category_id") else None
    if category and not isinstance(category, discord.CategoryChannel):
        category = None

    overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        member: discord.PermissionOverwrite(view_channel=True, send_messages=True, attach_files=True, read_message_history=True),
        guild.me: discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_channels=True, manage_permissions=True),
    }
    role_mentions = []
    for rid in ttype.get("staff_roles", []):
        role = guild.get_role(int(rid))
        if role:
            overwrites[role] = discord.PermissionOverwrite(view_channel=True, send_messages=True, read_message_history=True)
            role_mentions.append(role.mention)

    settings["next_number"] = settings.get("next_number", 0) + 1
    number = settings["next_number"]

    naming = settings.get("naming", "ticket-{user}")
    base_name = naming.replace("{user}", member.name).replace("{type}", ttype.get("label", type_id)).replace("{number}", str(number))
    base_name = sanitize_channel_name(base_name)

    try:
        channel = await guild.create_text_channel(
            base_name,
            category=category,
            overwrites=overwrites,
            reason=f"Ticket ({ttype.get('label', type_id)}) ouvert par {member}"
        )
    except discord.Forbidden:
        save_tickets()
        return await interaction.followup.send("❌ Je n'ai pas la permission de créer un salon. Préviens un administrateur.", ephemeral=True)

    tcfg["open"][str(channel.id)] = {
        "owner_id":       uid,
        "type_id":        type_id,
        "opened_at":      datetime.now(timezone.utc).isoformat(),
        "claimed_by":      None,
        "added_members":  [],
        "number":         number,
    }
    save_tickets()

    welcome = ttype.get("welcome_message") or "Décris ta demande ci-dessous, le staff va te répondre rapidement."
    welcome = welcome.replace("{user}", member.mention).replace("{type}", ttype.get("label", type_id))

    e = discord.Embed(
        title=f"{ttype.get('emoji', '🎫')} {ttype.get('label', type_id)} — Ticket #{number}",
        description=welcome,
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    if answers:
        for label, value in answers:
            if value:
                e.add_field(name=label[:256], value=value[:1024], inline=False)
    e.set_footer(text=f"Ouvert par {member}", icon_url=member.display_avatar.url)

    content = " ".join(role_mentions) if (role_mentions and settings.get("ping_staff", True)) else None
    try:
        await channel.send(content=content, embed=e, view=TicketManageView())
    except Exception:
        pass

    await interaction.followup.send(f"✅ Ton ticket a été créé : {channel.mention}", ephemeral=True)

# ── Commandes d'administration ──────────────────────────────────────────────

@bot.command(name="ticketadd")
@commands.has_permissions(manage_guild=True)
async def ticketadd(ctx, *, nom: str):
    """Créer un nouveau type de ticket (= une option du menu déroulant). Usage : +ticketadd <nom>"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    type_id = slugify(nom)
    if not type_id:
        return await ctx.reply("❌ Nom invalide.")
    if type_id in tcfg["types"]:
        return await ctx.reply(f"❌ Un type `{type_id}` existe déjà.")
    if len(tcfg["types"]) >= 25:
        return await ctx.reply("❌ Limite de 25 types de tickets atteinte (max 25 options par menu déroulant).")

    tcfg["types"][type_id] = {
        "label":           nom[:80],
        "emoji":           "🎫",
        "style":           "primary",
        "description":     None,
        "category_id":     None,
        "staff_roles":     [],
        "welcome_message": None,
        "questions":       [],
    }
    save_tickets()
    await ctx.reply(embed=success_embed(
        "🎫 Type de ticket créé",
        f"Identifiant : `{type_id}`\n\n"
        f"Configure-le avec :\n"
        f"`{PREFIX}ticketedit {type_id} category <catégorie>`\n"
        f"`{PREFIX}ticketrole {type_id} add @rôle`\n"
        f"`{PREFIX}ticketedit {type_id} emoji <emoji>`\n"
        f"`{PREFIX}ticketedit {type_id} description <texte affiché sous l'option>`\n"
        f"Puis envoie le panneau avec `{PREFIX}ticketpanel #salon Titre | Description`."
    ))
    await refresh_panels(ctx.guild)


@bot.command(name="ticketremove")
@commands.has_permissions(manage_guild=True)
async def ticketremove(ctx, type_id: str):
    """Supprimer un type de ticket. Usage : +ticketremove <type>"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    type_id = type_id.lower()
    if type_id not in tcfg["types"]:
        return await ctx.reply(f"❌ Type `{type_id}` introuvable. Utilise `{PREFIX}tickettypes`.")
    label = tcfg["types"][type_id]["label"]
    del tcfg["types"][type_id]
    save_tickets()
    await ctx.reply(embed=success_embed("🗑️ Type supprimé", f"Le type **{label}** (`{type_id}`) a été supprimé. Les panneaux existants sont mis à jour."))
    await refresh_panels(ctx.guild)

@bot.command(name="ticketedit")
@commands.has_permissions(manage_guild=True)
async def ticketedit(ctx, type_id: str, champ: str, *, valeur: str = None):
    """Modifier un type de ticket. Usage : +ticketedit <type> <label|emoji|style|category|message> <valeur>"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    type_id = type_id.lower()
    ttype = tcfg["types"].get(type_id)
    if not ttype:
        return await ctx.reply(f"❌ Type `{type_id}` introuvable. Utilise `{PREFIX}tickettypes`.")
    champ = champ.lower()

    if champ == "label":
        if not valeur:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketedit {type_id} label <texte>`")
        ttype["label"] = valeur[:80]
        msg = f"Label mis à jour : **{valeur[:80]}**."
    elif champ == "emoji":
        if not valeur:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketedit {type_id} emoji <emoji>`")
        valeur = valeur.strip()
        valid, reason = await is_valid_emoji(ctx, valeur)
        if not valid:
            return await ctx.reply(f"❌ Emoji invalide : `{valeur}`. {reason}")
        ttype["emoji"] = valeur[:50]
        msg = f"Emoji mis à jour : {valeur}"
    elif champ == "style":
        if not valeur or valeur.lower() not in BUTTON_STYLES:
            return await ctx.reply(f"❌ Style invalide. Choix possibles : {', '.join(BUTTON_STYLES)}")
        ttype["style"] = valeur.lower()
        msg = f"Style mis à jour : **{valeur.lower()}**."
    elif champ == "category":
        if not valeur:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketedit {type_id} category <nom catégorie>`")
        cat = discord.utils.get(ctx.guild.categories, name=valeur)
        if not cat:
            return await ctx.reply(f"❌ Catégorie `{valeur}` introuvable.")
        ttype["category_id"] = str(cat.id)
        msg = f"Catégorie mise à jour : **{cat.name}**."
    elif champ == "message":
        if not valeur:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketedit {type_id} message <texte>` (variables : {{user}}, {{type}})")
        ttype["welcome_message"] = valeur[:1500]
        msg = "Message d'accueil mis à jour."
    else:
        return await ctx.reply("❌ Champ invalide. Choix : `label`, `emoji`, `style`, `category`, `message`.")

    save_tickets()
    await ctx.reply(embed=success_embed("🎫 Type modifié", msg))
    await refresh_panels(ctx.guild)

@bot.command(name="ticketrole")
@commands.has_permissions(manage_guild=True)
async def ticketrole(ctx, type_id: str, action: str, role: discord.Role):
    """Gérer les rôles staff d'un type. Usage : +ticketrole <type> add/remove <@rôle>"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    type_id = type_id.lower()
    ttype = tcfg["types"].get(type_id)
    if not ttype:
        return await ctx.reply(f"❌ Type `{type_id}` introuvable. Utilise `{PREFIX}tickettypes`.")
    roles = ttype.setdefault("staff_roles", [])
    rid = str(role.id)
    action = action.lower()
    if action == "add":
        if rid in roles:
            return await ctx.reply(f"❌ {role.mention} est déjà rôle staff de ce type.")
        roles.append(rid)
        save_tickets()
        await ctx.reply(embed=success_embed("🎫 Rôle ajouté", f"{role.mention} peut maintenant voir/gérer les tickets **{ttype['label']}**."))
    elif action == "remove":
        if rid not in roles:
            return await ctx.reply(f"❌ {role.mention} n'est pas rôle staff de ce type.")
        roles.remove(rid)
        save_tickets()
        await ctx.reply(embed=success_embed("🎫 Rôle retiré", f"{role.mention} retiré des rôles staff de **{ttype['label']}**."))
    else:
        await ctx.reply("❌ Action invalide. Utilise `add` ou `remove`.")

@bot.command(name="ticketquestion")
@commands.has_permissions(manage_guild=True)
async def ticketquestion(ctx, type_id: str, action: str, *, valeur: str = None):
    """Gérer les questions du formulaire (modal) d'un type.
    Usage : +ticketquestion <type> add/addlong/remove/list [intitulé|numéro]"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    type_id = type_id.lower()
    ttype = tcfg["types"].get(type_id)
    if not ttype:
        return await ctx.reply(f"❌ Type `{type_id}` introuvable. Utilise `{PREFIX}tickettypes`.")
    questions = ttype.setdefault("questions", [])
    action = action.lower()

    if action in ("add", "addlong"):
        if not valeur:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketquestion {type_id} {action} <intitulé de la question>`")
        if len(questions) >= 5:
            return await ctx.reply("❌ Limite de 5 questions par type (limite Discord pour un formulaire).")
        questions.append({"label": valeur[:45], "style": "long" if action == "addlong" else "short", "required": True})
        save_tickets()
        await ctx.reply(embed=success_embed("🎫 Question ajoutée", f"« {valeur[:45]} » ajoutée au formulaire de **{ttype['label']}**."))
    elif action == "remove":
        if not valeur or not valeur.isdigit():
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketquestion {type_id} remove <numéro>` (voir `list`)")
        idx = int(valeur) - 1
        if not (0 <= idx < len(questions)):
            return await ctx.reply("❌ Numéro invalide.")
        removed = questions.pop(idx)
        save_tickets()
        await ctx.reply(embed=success_embed("🎫 Question supprimée", f"« {removed['label']} » supprimée."))
    elif action == "list":
        if not questions:
            return await ctx.reply("ℹ️ Aucune question configurée pour ce type.")
        lines = [f"**{i + 1}.** {q['label']} *({'long' if q['style'] == 'long' else 'court'})*" for i, q in enumerate(questions)]
        return await ctx.send(embed=info_embed(f"🎫 Questions — {ttype['label']}", "\n".join(lines)))
    else:
        return await ctx.reply("❌ Action invalide. Utilise `add`, `addlong`, `remove` ou `list`.")

@bot.command(name="tickettypes")
@commands.has_permissions(manage_guild=True)
async def tickettypes(ctx):
    """Lister les types de tickets configurés."""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    if not tcfg["types"]:
        return await ctx.reply(f"ℹ️ Aucun type de ticket configuré. Crée-en un avec `{PREFIX}ticketadd <nom>`.")
    e = discord.Embed(title="🎫 Types de tickets configurés", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    for tid, t in tcfg["types"].items():
        cat = ctx.guild.get_channel(int(t["category_id"])) if t.get("category_id") else None
        roles = [ctx.guild.get_role(int(r)) for r in t.get("staff_roles", [])]
        roles = [r.mention for r in roles if r]
        e.add_field(
            name=f"{t.get('emoji', '🎫')} {t['label']}  (`{tid}`)",
            value=(
                f"Style : `{t.get('style', 'primary')}`\n"
                f"Catégorie : {cat.mention if cat else '*non définie*'}\n"
                f"Rôles staff : {', '.join(roles) if roles else '*aucun*'}\n"
                f"Questions formulaire : {len(t.get('questions', []))}"
            ),
            inline=False
        )
    await ctx.send(embed=e)

def _extract_image_url(contenu: str | None, attachments: list) -> tuple:
    """Extrait une URL d'image/gif depuis le contenu (segment 'image:' ou 'image|')
    ou depuis une pièce jointe du message. Retourne (contenu_nettoyé, image_url)."""
    image_url = None
    if attachments:
        for att in attachments:
            ct = (att.content_type or "").lower()
            if ct.startswith("image/") or att.filename.lower().endswith((".gif", ".png", ".jpg", ".jpeg", ".webp")):
                image_url = att.url
                break
    if contenu:
        match = re.search(r"(?:^|\|)\s*image\s*[:|]\s*(\S+)", contenu, re.IGNORECASE)
        if match:
            candidate = match.group(1).strip()
            if candidate.startswith("http"):
                if not image_url:
                    image_url = candidate
                contenu = (contenu[:match.start()] + contenu[match.end():]).strip()
                contenu = contenu.rstrip("|").strip()
    return contenu, image_url

@bot.command(name="ticketpanel")
@commands.has_permissions(manage_guild=True)
async def ticketpanel(ctx, channel: discord.TextChannel, *, contenu: str = None):
    """Envoyer le panneau de tickets (boutons).
    Usage : +ticketpanel #salon Titre | Description | image: <url>
    Tu peux aussi attacher directement une image/gif à ton message au lieu de mettre une URL."""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    if not tcfg["types"]:
        return await ctx.reply(f"❌ Aucun type de ticket configuré. Crée-en un avec `{PREFIX}ticketadd <nom>` avant d'envoyer un panneau.")

    contenu, image_url = _extract_image_url(contenu, ctx.message.attachments)

    if contenu:
        parts = contenu.split("|", 1)
        titre = parts[0].strip() or "🎫 Support"
        description = parts[1].strip() if len(parts) > 1 else "Clique sur un bouton ci-dessous pour ouvrir un ticket."
    else:
        titre = "🎫 Support"
        description = "Clique sur un bouton ci-dessous pour ouvrir un ticket."

    type_ids = list(tcfg["types"].keys())[:25]
    e = discord.Embed(title=titre, description=description, color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    e.set_footer(text=f"Panneau créé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    if image_url:
        e.set_image(url=image_url)

    view = build_panel_view(gid, type_ids)
    try:
        msg = await channel.send(embed=e, view=view)
    except discord.Forbidden:
        return await ctx.reply(f"❌ Je n'ai pas la permission d'envoyer de message dans {channel.mention}.")

    tcfg["panels"][str(msg.id)] = {
        "channel_id": str(channel.id),
        "title":      titre,
        "description": description,
        "image_url":  image_url,
        "type_ids":   type_ids,
    }
    save_tickets()
    bot.add_view(view, message_id=msg.id)

    await ctx.reply(embed=success_embed("🎫 Panneau envoyé", f"Le panneau de tickets a été envoyé dans {channel.mention} avec {len(type_ids)} bouton(s)." + (" et une image." if image_url else "")))

@bot.command(name="ticketpanelimage")
@commands.has_permissions(manage_guild=True)
async def ticketpanelimage(ctx, message_id: str, url: str = None):
    """Ajouter/changer/retirer l'image d'un panneau déjà envoyé.
    Usage : +ticketpanelimage <id_message> <url|none> (ou attache une image au message)"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    panel = tcfg["panels"].get(message_id)
    if not panel:
        return await ctx.reply("❌ Panneau introuvable. Vérifie l'ID du message du panneau (`+tickettypes`/historique du salon).")

    image_url = None
    if ctx.message.attachments:
        for att in ctx.message.attachments:
            ct = (att.content_type or "").lower()
            if ct.startswith("image/") or att.filename.lower().endswith((".gif", ".png", ".jpg", ".jpeg", ".webp")):
                image_url = att.url
                break
    elif url and url.lower() != "none" and url.startswith("http"):
        image_url = url

    channel = ctx.guild.get_channel(int(panel["channel_id"]))
    if not channel:
        return await ctx.reply("❌ Le salon de ce panneau n'existe plus.")
    try:
        message = await channel.fetch_message(int(message_id))
    except (discord.NotFound, discord.Forbidden, discord.HTTPException):
        return await ctx.reply("❌ Message du panneau introuvable.")

    e = discord.Embed(title=panel["title"], description=panel["description"], color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    e.set_footer(text=f"Panneau créé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    if image_url:
        e.set_image(url=image_url)

    try:
        await message.edit(embed=e)
    except discord.HTTPException as ex:
        return await ctx.reply(f"❌ Impossible de modifier le panneau : {ex}")

    panel["image_url"] = image_url
    save_tickets()
    await ctx.reply(embed=success_embed("🎫 Image mise à jour", "L'image a été retirée." if not image_url else "L'image du panneau a été mise à jour."))

@bot.command(name="ticketsettings")
@commands.has_permissions(manage_guild=True)
async def ticketsettings(ctx, option: str = None, *, valeur: str = None):
    """Voir/modifier les réglages globaux des tickets.
    Usage : +ticketsettings [max|logsalon|naming|confirmation|ping] [valeur]"""
    gid = str(ctx.guild.id)
    tcfg = get_ticket_cfg(gid)
    settings = tcfg["settings"]

    if not option:
        log_ch = ctx.guild.get_channel(int(settings["log_channel"])) if settings.get("log_channel") else None
        e = discord.Embed(title="🎫 Paramètres des tickets", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
        e.add_field(name="Max tickets / membre", value=f"`{settings.get('max_per_user', 1)}`", inline=True)
        e.add_field(name="Confirmation fermeture", value="🟢 ON" if settings.get("confirm_close", True) else "🔴 OFF", inline=True)
        e.add_field(name="Ping staff à l'ouverture", value="🟢 ON" if settings.get("ping_staff", True) else "🔴 OFF", inline=True)
        e.add_field(name="Salon de logs/transcripts", value=log_ch.mention if log_ch else "*celui défini par `+setlog`, sinon aucun*", inline=False)
        e.add_field(name="Format des noms de salon", value=f"`{settings.get('naming', 'ticket-{user}')}`", inline=False)
        e.set_footer(text=f"{PREFIX}ticketsettings <option> <valeur> pour modifier")
        return await ctx.send(embed=e)

    option = option.lower()
    if option == "max":
        if not valeur or not valeur.isdigit() or not (1 <= int(valeur) <= 10):
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketsettings max <1-10>`")
        settings["max_per_user"] = int(valeur)
        msg = f"Limite fixée à **{valeur}** ticket(s) par membre."
    elif option == "logsalon":
        match = re.search(r"\d{15,20}", valeur or "")
        channel = ctx.guild.get_channel(int(match.group())) if match else None
        if not channel:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketsettings logsalon #salon`")
        settings["log_channel"] = str(channel.id)
        msg = f"Salon de logs des tickets : {channel.mention}."
    elif option == "naming":
        if not valeur:
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketsettings naming <motif>` (variables : {{user}}, {{type}}, {{number}})")
        settings["naming"] = valeur[:90]
        msg = f"Motif de nom de salon : `{valeur[:90]}`."
    elif option == "confirmation":
        if not valeur or valeur.lower() not in ("on", "off"):
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketsettings confirmation on/off`")
        settings["confirm_close"] = (valeur.lower() == "on")
        msg = f"Confirmation de fermeture : **{valeur.lower()}**."
    elif option == "ping":
        if not valeur or valeur.lower() not in ("on", "off"):
            return await ctx.reply(f"❌ Usage : `{PREFIX}ticketsettings ping on/off`")
        settings["ping_staff"] = (valeur.lower() == "on")
        msg = f"Ping du staff à l'ouverture : **{valeur.lower()}**."
    else:
        return await ctx.reply("❌ Option invalide. Choix : `max`, `logsalon`, `naming`, `confirmation`, `ping`.")

    save_tickets()
    await ctx.reply(embed=success_embed("🎫 Paramètres", msg))

@bot.command()
@commands.has_permissions(manage_channels=True)
async def closeticket(ctx):
    """Fermer le ticket courant (alternative textuelle aux boutons)."""
    tdata, _ = get_open_ticket(ctx.guild.id, ctx.channel.id)
    if tdata is None:
        return await ctx.reply("❌ Ce salon n'est pas un ticket actif.")
    await close_ticket_channel(ctx.channel, ctx.author)
    
# ─────────────────────────────────────────
#  SYSTÈME DE MARIAGE
# ─────────────────────────────────────────
@bot.command()
async def marry(ctx, member: discord.Member):
    """Demander quelqu'un en mariage. Usage : +marry @membre"""
    if member == ctx.author:
        return await ctx.reply("❌ Tu ne peux pas te marier avec toi-même.")
    if member.bot:
        return await ctx.reply("❌ Tu ne peux pas te marier avec un bot.")
    gid = str(ctx.guild.id)
    uid1, uid2 = str(ctx.author.id), str(member.id)

    # Vérifier si l'un des deux est déjà marié
    marriages = marriages_db.get(gid, {})
    if uid1 in marriages:
        partner = ctx.guild.get_member(int(marriages[uid1]))
        return await ctx.reply(f"❌ Tu es déjà marié(e) avec {partner.mention if partner else marriages[uid1]}.")
    if uid2 in marriages:
        partner = ctx.guild.get_member(int(marriages[uid2]))
        return await ctx.reply(f"❌ {member.mention} est déjà marié(e).")

    e = discord.Embed(
        title="💍 Demande en mariage",
        description=f"{ctx.author.mention} demande {member.mention} en mariage !\n\n{member.mention}, acceptes-tu ? Réponds `oui` ou `non` dans les 30 secondes.",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    await ctx.send(embed=e)

    def check(m): return m.author == member and m.channel == ctx.channel and m.content.lower() in ("oui", "non")
    try:
        response = await bot.wait_for("message", check=check, timeout=30)
    except asyncio.TimeoutError:
        return await ctx.send(f"💔 {member.mention} n'a pas répondu à temps. La demande expire.")

    if response.content.lower() == "non":
        return await ctx.send(f"💔 {member.mention} a refusé la demande de mariage.")

    marriages_db.setdefault(gid, {})[uid1] = uid2
    marriages_db[gid][uid2] = uid1
    save_marriages()

    e = discord.Embed(
        title="💒 Mariage célébré !",
        description=f"🎊 {ctx.author.mention} et {member.mention} sont maintenant mariés !\nFélicitations ! 💕",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    await ctx.send(embed=e)

@bot.command()
async def divorce(ctx):
    """Divorcer de ton partenaire actuel."""
    gid = str(ctx.guild.id)
    uid = str(ctx.author.id)
    marriages = marriages_db.get(gid, {})
    if uid not in marriages:
        return await ctx.reply("❌ Tu n'es pas marié(e).")
    partner_id = marriages[uid]
    partner = ctx.guild.get_member(int(partner_id))
    marriages.pop(uid, None)
    marriages.pop(partner_id, None)
    save_marriages()
    e = mod_embed("💔 Divorce", f"{ctx.author.mention} a divorcé de {partner.mention if partner else partner_id}.", discord.Color.dark_red())
    await ctx.send(embed=e)

@bot.command()
async def couples(ctx):
    """Voir tous les couples mariés sur ce serveur."""
    gid = str(ctx.guild.id)
    marriages = marriages_db.get(gid, {})
    if not marriages:
        return await ctx.reply("💔 Aucun couple sur ce serveur.")
    seen = set()
    lines = []
    for uid1, uid2 in marriages.items():
        pair = tuple(sorted([uid1, uid2]))
        if pair in seen:
            continue
        seen.add(pair)
        m1 = ctx.guild.get_member(int(uid1))
        m2 = ctx.guild.get_member(int(uid2))
        n1 = m1.display_name if m1 else f"<@{uid1}>"
        n2 = m2.display_name if m2 else f"<@{uid2}>"
        lines.append(f"💕 **{n1}** & **{n2}**")
    e = discord.Embed(title="💒 Couples du serveur", description="\n".join(lines) or "Aucun couple.", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    await ctx.send(embed=e)

# ─────────────────────────────────────────
#  Système de salons "stats vocales" (compteurs personnalisables)
# ─────────────────────────────────────────
STATSVOC_TYPES = {
    "membres":  {"label": "Nombre de membres",        "default_format": "👥 Membres : {count}"},
    "enligne":  {"label": "Membres en ligne",          "default_format": "🟢 En ligne : {count}"},
    "vocal":    {"label": "Membres en vocal",          "default_format": "🔊 En vocal : {count}"},
    "boosts":   {"label": "Boosts du serveur",         "default_format": "💎 Boosts : {count}"},
}

def get_statsvoc_cfg(guild_id) -> dict:
    gid = str(guild_id)
    cfg = statsvoc_db.setdefault(gid, {})
    cfg.setdefault("channels", {})  # channel_id -> {"type": str, "format": str}
    return cfg

def compute_statsvoc_value(guild: discord.Guild, stat_type: str) -> int:
    if stat_type == "membres":
        return guild.member_count or len(guild.members)
    if stat_type == "enligne":
        return sum(
            1 for m in guild.members
            if not m.bot and m.status not in (discord.Status.offline, None)
        )
    if stat_type == "vocal":
        return sum(1 for vc in guild.voice_channels for m in vc.members if not m.bot)
    if stat_type == "boosts":
        return guild.premium_subscription_count or 0
    return 0

async def update_statsvoc_guild(guild: discord.Guild):
    """Met à jour (renomme) tous les salons stats-vocales d'un serveur."""
    gid = str(guild.id)
    cfg = statsvoc_db.get(gid)
    if not cfg or not cfg.get("channels"):
        return
    if guild.chunked is False:
        try:
            await guild.chunk(cache=True)
        except Exception:
            pass
    changed = False
    for chan_id, data in list(cfg["channels"].items()):
        channel = guild.get_channel(int(chan_id))
        if not channel:
            cfg["channels"].pop(chan_id, None)
            changed = True
            continue
        stat_type = data.get("type")
        fmt = data.get("format") or STATSVOC_TYPES.get(stat_type, {}).get("default_format", "{count}")
        count = compute_statsvoc_value(guild, stat_type)
        new_name = fmt.replace("{count}", str(count))[:100]
        if channel.name != new_name:
            try:
                await channel.edit(name=new_name, reason="Mise à jour stat vocale")
            except discord.HTTPException:
                pass
            except Exception:
                pass
    if changed:
        save_statsvoc()

@tasks.loop(minutes=5)
async def update_statsvoc_loop():
    for guild in bot.guilds:
        try:
            await update_statsvoc_guild(guild)
        except Exception:
            log.error(f"Erreur update_statsvoc_guild ({guild.id}): {traceback.format_exc()}")
        await asyncio.sleep(1)  # éviter de spammer l'API d'un coup sur plusieurs serveurs

@update_statsvoc_loop.before_loop
async def before_update_statsvoc_loop():
    await bot.wait_until_ready()

@bot.command(name="statvoc")
@commands.has_permissions(manage_guild=True)
async def statvoc(ctx, action: str = None, *, args: str = None):
    """Salons vocaux "stats" personnalisables, mis à jour automatiquement toutes les 5 minutes.
    Usage :
      +statvoc create <membres|enligne|vocal|boosts> [format avec {count}]
      +statvoc format <id_salon> <format avec {count}>
      +statvoc remove <id_salon>
      +statvoc list
    Le format par défaut utilise {count} comme variable, ex : "👥 Membres : {count}"."""
    gid = str(ctx.guild.id)
    cfg = get_statsvoc_cfg(gid)

    if not action:
        types_help = ", ".join(f"`{t}`" for t in STATSVOC_TYPES)
        return await ctx.reply(
            f"❌ Usage : `{PREFIX}statvoc create <type> [format]` (types : {types_help})\n"
            f"`{PREFIX}statvoc format <id_salon> <format>` · `{PREFIX}statvoc remove <id_salon>` · `{PREFIX}statvoc list`"
        )
    action = action.lower()

    if action == "create":
        if not args:
            types_help = ", ".join(f"`{t}`" for t in STATSVOC_TYPES)
            return await ctx.reply(f"❌ Usage : `{PREFIX}statvoc create <type> [format]` (types : {types_help})")
        parts = args.split(None, 1)
        stat_type = parts[0].lower()
        custom_format = parts[1].strip() if len(parts) > 1 else None
        if stat_type not in STATSVOC_TYPES:
            types_help = ", ".join(f"`{t}`" for t in STATSVOC_TYPES)
            return await ctx.reply(f"❌ Type invalide. Choix : {types_help}")
        if custom_format and "{count}" not in custom_format:
            return await ctx.reply("❌ Le format doit contenir la variable `{count}`.")

        fmt = custom_format or STATSVOC_TYPES[stat_type]["default_format"]
        count = compute_statsvoc_value(ctx.guild, stat_type)
        chan_name = fmt.replace("{count}", str(count))[:100]

        try:
            channel = await ctx.guild.create_voice_channel(
                chan_name,
                overwrites={
                    ctx.guild.default_role: discord.PermissionOverwrite(connect=False, view_channel=True),
                    ctx.guild.me: discord.PermissionOverwrite(connect=True, view_channel=True, manage_channels=True),
                },
                reason=f"Salon stat vocale ({stat_type}) créé par {ctx.author}"
            )
        except discord.Forbidden:
            return await ctx.reply("❌ Je n'ai pas la permission de créer un salon vocal.")

        cfg["channels"][str(channel.id)] = {"type": stat_type, "format": fmt}
        save_statsvoc()
        await ctx.reply(embed=success_embed(
            "📊 Salon stat créé",
            f"{channel.mention} affichera désormais **{STATSVOC_TYPES[stat_type]['label'].lower()}**, "
            f"actualisé toutes les 5 minutes.\nFormat : `{fmt}`"
        ))

    elif action == "format":
        if not args:
            return await ctx.reply(f"❌ Usage : `{PREFIX}statvoc format <id_salon> <format avec {{count}}>`")
        parts = args.split(None, 1)
        if len(parts) < 2 or not parts[0].isdigit():
            return await ctx.reply(f"❌ Usage : `{PREFIX}statvoc format <id_salon> <format avec {{count}}>`")
        chan_id, new_fmt = parts[0], parts[1].strip()
        if "{count}" not in new_fmt:
            return await ctx.reply("❌ Le format doit contenir la variable `{count}`.")
        data = cfg["channels"].get(chan_id)
        if not data:
            return await ctx.reply("❌ Ce salon n'est pas un salon stat configuré (`+statvoc list`).")
        data["format"] = new_fmt
        save_statsvoc()
        await update_statsvoc_guild(ctx.guild)
        await ctx.reply(embed=success_embed("📊 Format mis à jour", f"Nouveau format : `{new_fmt}`"))

    elif action == "remove":
        if not args or not args.strip().isdigit():
            return await ctx.reply(f"❌ Usage : `{PREFIX}statvoc remove <id_salon>` (voir `{PREFIX}statvoc list`)")
        chan_id = args.strip()
        if chan_id not in cfg["channels"]:
            return await ctx.reply("❌ Ce salon n'est pas un salon stat configuré.")
        cfg["channels"].pop(chan_id, None)
        save_statsvoc()
        channel = ctx.guild.get_channel(int(chan_id))
        if channel:
            try:
                await channel.delete(reason=f"Salon stat retiré par {ctx.author}")
            except Exception:
                pass
        await ctx.reply(embed=success_embed("📊 Salon stat retiré", "La configuration et le salon ont été supprimés."))

    elif action == "list":
        if not cfg["channels"]:
            return await ctx.reply(f"ℹ️ Aucun salon stat configuré. Crée-en un avec `{PREFIX}statvoc create <type>`.")
        lines = []
        for chan_id, data in cfg["channels"].items():
            channel = ctx.guild.get_channel(int(chan_id))
            label = STATSVOC_TYPES.get(data.get("type"), {}).get("label", data.get("type"))
            lines.append(f"{channel.mention if channel else f'`{chan_id}` (supprimé)'} — {label} — format : `{data.get('format')}`")
        await ctx.send(embed=info_embed("📊 Salons stats configurés", "\n".join(lines)))

    elif action in ("update", "refresh"):
        await update_statsvoc_guild(ctx.guild)
        await ctx.reply(embed=success_embed("📊 Actualisation", "Les salons stats ont été actualisés."))

    else:
        await ctx.reply("❌ Action invalide. Utilise `create`, `format`, `remove`, `list` ou `update`.")

# ─────────────────────────────────────────
#  UTILITAIRES
# ─────────────────────────────────────────
@bot.command()
async def stats(ctx):
    """Afficher les statistiques en direct du serveur : membres, en ligne/hors ligne, vocal, boosts."""
    g = ctx.guild

    # S'assurer que le cache des membres est bien rempli avant de compter
    # (sur un gros serveur, discord.py peut ne pas avoir tout chargé au moment
    # de la commande si le chunking initial n'est pas terminé).
    if g.chunked is False:
        try:
            await g.chunk(cache=True)
        except Exception:
            pass

    online = offline = in_voice = streaming = voice_muted = 0
    for member in g.members:
        if member.bot:
            continue
        if member.status is discord.Status.offline or member.status is None:
            offline += 1
        else:
            online += 1
        if member.voice and member.voice.channel:
            in_voice += 1
            if member.voice.self_stream or member.voice.self_video:
                streaming += 1
            if member.voice.self_mute or member.voice.mute:
                voice_muted += 1

    boosts     = g.premium_subscription_count or 0
    boost_tier = g.premium_tier or 0
    total      = g.member_count or len([m for m in g.members])
    humans     = total - sum(1 for m in g.members if m.bot)
    bots       = sum(1 for m in g.members if m.bot)

    e = discord.Embed(
        title=f"🏆 {g.name} Statistiques",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    if g.icon:
        e.set_thumbnail(url=g.icon.url)

    e.description = (
        f"*Membres :* **{total}**\n"
        f"*En ligne :* **{online}**\n"
        f"*En vocal :* **{in_voice}**\n"
        f"*En stream :* **{streaming}**\n"
        f"*Boosts :* **{boosts}**"
    )

    await ctx.send(embed=e)


@bot.command()
async def botinfo(ctx):
    """Afficher les informations et statistiques du bot."""
    delta = datetime.now(timezone.utc) - _start_time
    hours, remainder = divmod(int(delta.total_seconds()), 3600)
    minutes, seconds = divmod(remainder, 60)
    days = hours // 24
    hours %= 24
    uptime_str = f"{days}j {hours}h {minutes}m {seconds}s"

    total_members = sum(g.member_count for g in bot.guilds)
    total_commands = len(list(bot.commands))

    e = discord.Embed(
        title=f"🤖 {bot.user.name} — Informations",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    if bot.user.avatar:
        e.set_thumbnail(url=bot.user.avatar.url)

    e.add_field(name="🏷️ Nom",         value=str(bot.user),               inline=True)
    e.add_field(name="🔢 ID",           value=str(bot.user.id),            inline=True)
    e.add_field(name="🌐 Serveurs",     value=str(len(bot.guilds)),         inline=True)
    e.add_field(name="👥 Membres",      value=str(total_members),           inline=True)
    e.add_field(name="⚙️ Commandes",    value=str(total_commands),          inline=True)
    e.add_field(name="🏓 Latence",      value=f"{round(bot.latency*1000)}ms", inline=True)
    e.add_field(name="⏱️ Uptime",       value=uptime_str,                   inline=True)
    e.add_field(name="🚀 Démarré",      value=f"<t:{int(_start_time.timestamp())}:R>", inline=True)
    e.add_field(name="📚 Bibliothèque", value=f"discord.py {discord.__version__}", inline=True)
    e.add_field(name="🐍 Python",       value=f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}", inline=True)
    e.add_field(name="📊 Stats session",
                value=f"💬 Commandes : {_bot_stats['commands_used']}\n🤖 AutoMod : {_bot_stats['automod_actions']}\n📨 Messages : {_bot_stats['messages_today']}",
                inline=False)
    e.add_field(name="💾 Données",
                value=f"⚠️ Warns enregistrés : {sum(len(v) for gw in warns_db.values() for v in gw.values())}\n🎉 Giveaways : {sum(len(v) for v in giveaway_db.values())}\n💒 Mariages : {len(marriages_db.get(str(ctx.guild.id), {})) // 2}",
                inline=False)
    e.set_footer(text=f"Préfixe : {PREFIX}  •  Demandé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.send(embed=e)

@bot.command()
async def ping(ctx):
    """Afficher la latence du bot."""
    latency = round(bot.latency * 1000)
    e = discord.Embed(title="🏓 Pong !", color=discord.Color.from_rgb(0, 0, 0))
    e.add_field(name="Latence API", value=f"**{latency}ms**", inline=True)
    e.add_field(name="Statut", value="🟢 En ligne", inline=True)
    await ctx.send(embed=e)

@bot.command()
async def uptime(ctx):
    """Afficher le temps d'activité du bot."""
    delta = datetime.now(timezone.utc) - _start_time
    hours, remainder = divmod(int(delta.total_seconds()), 3600)
    minutes, seconds = divmod(remainder, 60)
    days = hours // 24
    hours %= 24
    e = info_embed("⏱️ Uptime", f"En ligne depuis **{days}j {hours}h {minutes}m {seconds}s**.\n**Démarré :** <t:{int(_start_time.timestamp())}:R>")
    await ctx.send(embed=e)

@bot.command()
async def calc(ctx, *, expression: str):
    """Calculatrice simple. Usage : +calc 2 + 2 * 10"""
    safe_expr = re.sub(r"[^0-9\s\+\-\*\/\.\(\)\%]", "", expression)
    if not safe_expr.strip():
        return await ctx.reply("❌ Expression invalide.")
    try:
        loop = asyncio.get_event_loop()
        result = await asyncio.wait_for(
            loop.run_in_executor(None, lambda: eval(safe_expr, {"__builtins__": {}})),
            timeout=2.0
        )
        e = success_embed("🧮 Calculatrice", f"**Expression :** `{safe_expr.strip()}`\n**Résultat :** `{result}`")
        await ctx.send(embed=e)
    except asyncio.TimeoutError:
        await ctx.reply("❌ Expression trop complexe ou boucle infinie détectée.")
    except ZeroDivisionError:
        await ctx.reply("❌ Division par zéro impossible.")
    except Exception:
        await ctx.reply("❌ Expression invalide.")

@bot.command(name="8ball")
async def eight_ball(ctx, *, question: str):
    """Boule magique. Usage : +8ball <question>"""
    reponses = [
        "✅ C'est certain.", "✅ Oui, absolument.", "✅ Sans aucun doute.",
        "✅ Oui, définitivement.", "✅ Tu peux compter dessus.",
        "🟡 À première vue, oui.", "🟡 Les signes sont favorables.", "🟡 Les perspectives sont bonnes.",
        "🟡 Tout indique que oui.", "🟡 C'est très probable.",
        "🟠 C'est flou, réessaie.", "🟠 Je préfère ne pas répondre.",
        "🟠 Je ne peux pas prédire ça maintenant.", "🟠 Concentre-toi et redemande.",
        "❌ N'y compte pas.", "❌ Ma réponse est non.", "❌ Mes sources disent non.",
        "❌ Les perspectives ne sont pas bonnes.", "❌ C'est très incertain.",
    ]
    e = discord.Embed(
        title="🎱 Boule Magique",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    e.add_field(name="❓ Question", value=question, inline=False)
    e.add_field(name="🔮 Réponse", value=random.choice(reponses), inline=False)
    e.set_footer(text=f"Demandé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.send(embed=e)

@bot.command(name="create")
@commands.has_permissions(manage_emojis=True)
@commands.bot_has_permissions(manage_emojis=True)
async def create_emoji(ctx, emoji: discord.PartialEmoji):
    """Voler un emoji d'un autre serveur et l'ajouter ici."""
    if len(ctx.guild.emojis) >= ctx.guild.emoji_limit:
        return await ctx.reply("❌ La limite d'emojis du serveur est atteinte.")
    try:
        data = await emoji.read()
        new_emoji = await ctx.guild.create_custom_emoji(name=emoji.name, image=data, reason=f"Emoji ajouté par {ctx.author}")
        e = success_embed("✅ Emoji ajouté", f"Emoji créé : {new_emoji}\nNom : `{new_emoji.name}`\nAjouté par : {ctx.author.mention}")
        await ctx.send(embed=e)
    except (discord.HTTPException, discord.NotFound):
        await ctx.reply("❌ Impossible d'ajouter cet emoji.")

@bot.command()
async def coinflip(ctx):
    """Lancer une pièce — Pile ou Face."""
    result = random.choice(["🪙 **Pile !**", "🪙 **Face !**"])
    await ctx.send(embed=info_embed("🪙 Pile ou Face", result))

@bot.command()
async def roll(ctx, dice: str = "1d6"):
    """Lancer des dés. Usage : +roll [NdN]"""
    m = re.fullmatch(r"(\d+)d(\d+)", dice.lower())
    if not m:
        return await ctx.reply("❌ Format invalide. Exemple : `2d6`, `1d20`.")
    nb, faces = int(m.group(1)), int(m.group(2))
    if nb < 1 or nb > 20 or faces < 2 or faces > 100:
        return await ctx.reply("❌ Entre 1-20 dés, 2-100 faces.")
    results = [random.randint(1, faces) for _ in range(nb)]
    total = sum(results)
    rolls_str = " + ".join(str(r) for r in results) if nb > 1 else str(results[0])
    desc = f"🎲 **{dice}** → {rolls_str}" + (f" = **{total}**" if nb > 1 else "")
    await ctx.send(embed=info_embed("🎲 Lancer de dés", desc))

@bot.command()
@commands.has_permissions(manage_messages=True)
async def say(ctx, *, message: str):
    """Faire parler le bot. Usage : +say <message>"""
    await ctx.message.delete()
    await ctx.send(message, allowed_mentions=discord.AllowedMentions.none())

@bot.command()
@commands.has_permissions(manage_guild=True)
async def poll(ctx, *, contenu: str):
    """Créer un sondage. Usage : +poll Question | Option1 | Option2 | ..."""
    parts = [p.strip() for p in contenu.split("|")]
    if len(parts) < 3:
        return await ctx.reply("❌ Format : `+poll Question | Option1 | Option2 | ...`")
    if len(parts) > 11:
        return await ctx.reply("❌ Maximum 10 options.")
    question = parts[0]
    options  = parts[1:]
    emojis   = ["1️⃣","2️⃣","3️⃣","4️⃣","5️⃣","6️⃣","7️⃣","8️⃣","9️⃣","🔟"]
    desc = "\n".join(f"{emojis[i]} {opt}" for i, opt in enumerate(options))
    e = info_embed(f"📊 {question}", desc)
    e.set_footer(text=f"Sondage créé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.message.delete()
    msg = await ctx.send(embed=e)
    for i in range(len(options)):
        await msg.add_reaction(emojis[i])

@bot.command(name="snipe")
@commands.has_permissions(manage_messages=True)
async def snipe(ctx, member: discord.Member = None):
    """Afficher les derniers messages supprimés d'un membre (ou du salon si aucun membre précisé)."""
    gid = ctx.guild.id
    now = datetime.now(timezone.utc)

    if member:
        raw_entries = _snipe_cache.get(gid, {}).get(member.id, [])
        title = f"🕵️ Messages supprimés de {member}"
    else:
        # Rassemble tous les messages supprimés du serveur, toutes provenances
        raw_entries = []
        for uid, entries in _snipe_cache.get(gid, {}).items():
            raw_entries.extend(entries)
        raw_entries.sort(key=lambda x: x.get("created_at", ""), reverse=True)
        title = "🕵️ Derniers messages supprimés du serveur"

    def _is_recent(entry):
        try:
            return now - datetime.fromisoformat(entry["created_at"]) <= SNIPE_MAX_AGE
        except Exception:
            return False

    valid = [entry for entry in raw_entries if _is_recent(entry)][:10]

    if not valid:
        return await ctx.reply("❌ Aucun message supprimé récent trouvé.")

    snipe_embed = warning_embed(title, "")
    for i, entry in enumerate(valid, 1):
        ch = ctx.guild.get_channel(entry["channel_id"])
        content = (entry["content"] or "[vide]")[:800]
        try:
            ts = f"<t:{int(datetime.fromisoformat(entry['created_at']).timestamp())}:R>"
        except Exception:
            ts = "?"
        # Identifier l'auteur si disponible (snipe global)
        author_id = entry.get("author_id")
        author_str = f"<@{author_id}> · " if author_id and not member else ""
        val = f"{author_str}**Salon :** {ch.mention if ch else '?'}\n**Supprimé :** {ts}\n\n{content}"
        if entry.get("attachments"):
            val += "\n\n📎 " + "\n".join(entry["attachments"][:3])
        snipe_embed.add_field(name=f"Message #{i}", value=val[:1024], inline=False)
    if member:
        snipe_embed.set_thumbnail(url=member.display_avatar.url)
    await ctx.send(embed=snipe_embed)

@bot.command()
async def remind(ctx, duration: str, *, message: str):
    """Te rappeler quelque chose après un délai. Usage : +remind <durée> <message>"""
    delta = parse_duration(duration)
    if not delta:
        return await ctx.reply("❌ Durée invalide. Exemples : `30m`, `1h`, `2d`.")
    end_ts = int((datetime.now(timezone.utc) + delta).timestamp())
    e = info_embed("⏰ Rappel créé", f"Je te rappellerai <t:{end_ts}:R> :\n**{message}**")
    await ctx.reply(embed=e)
    async def do_remind():
        await asyncio.sleep(delta.total_seconds())
        e2 = warning_embed("⏰ Rappel !", f"{ctx.author.mention}, tu voulais te souvenir de :\n**{message}**")
        try:
            await ctx.send(embed=e2)
        except Exception:
            try:
                await ctx.author.send(embed=e2)
            except Exception:
                pass
    asyncio.ensure_future(do_remind())

@bot.command()
@commands.has_permissions(manage_messages=True)
async def embed(ctx, *, contenu: str):
    """Envoyer un embed personnalisé. Usage : +embed Titre | Description"""
    parts = contenu.split("|", 1)
    if len(parts) < 2:
        return await ctx.reply("❌ Format : `+embed Titre | Description`")
    titre, description = parts[0].strip(), parts[1].strip()
    e = info_embed(titre, description)
    e.set_footer(text=f"Par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.message.delete()
    await ctx.send(embed=e)

@bot.command()
@commands.has_permissions(manage_guild=True)
async def announce(ctx, *, message: str):
    """Faire une annonce en embed. Usage : +announce <message>"""
    e = discord.Embed(title="📢 Annonce", description=message, color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    e.set_footer(text=f"Par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.message.delete()
    await ctx.send("@everyone", embed=e)

# ─────────────────────────────────────────
#  MEMBRES & RÔLES
# ─────────────────────────────────────────
@bot.command()
async def avatar(ctx, member: discord.Member = None):
    """Afficher l'avatar d'un membre."""
    member = member or ctx.author
    e = discord.Embed(title=f"🖼️ Avatar de {member}", color=discord.Color.from_rgb(0, 0, 0))
    e.set_image(url=member.display_avatar.url)
    e.add_field(name="Lien direct", value=f"[Ouvrir]({member.display_avatar.url})")
    await ctx.send(embed=e)

@bot.command()
@commands.has_permissions(manage_roles=True)
@commands.bot_has_permissions(manage_roles=True)
async def addrole(ctx, member: discord.Member, role: discord.Role):
    """Donner un rôle à un membre."""
    if role in member.roles:
        return await ctx.reply(f"❌ {member.mention} a déjà {role.mention}.")
    await member.add_roles(role, reason=f"Ajouté par {ctx.author}")
    e = success_embed("✅ Rôle ajouté", f"**Membre :** {member.mention}\n**Rôle :** {role.mention}\n**Modérateur :** {ctx.author.mention}")
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(manage_roles=True)
@commands.bot_has_permissions(manage_roles=True)
async def removerole(ctx, member: discord.Member, role: discord.Role):
    """Retirer un rôle d'un membre."""
    if role not in member.roles:
        return await ctx.reply(f"❌ {member.mention} n'a pas {role.mention}.")
    await member.remove_roles(role, reason=f"Retiré par {ctx.author}")
    e = mod_embed("✅ Rôle retiré", f"**Membre :** {member.mention}\n**Rôle :** {role.mention}\n**Modérateur :** {ctx.author.mention}", discord.Color.orange())
    await ctx.send(embed=e)
    await send_log(ctx.guild, e)

@bot.command()
@commands.has_permissions(administrator=True)
async def autorole(ctx, role: discord.Role):
    """Définir le rôle automatiquement donné aux nouveaux membres."""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg["auto_role"] = role.id
    save_config()
    await ctx.reply(f"✅ Auto-rôle défini sur {role.mention}.")

@bot.command()
@commands.has_permissions(administrator=True)
async def setwelcome(ctx, channel: discord.TextChannel, *, message: str):
    """Configurer le message de bienvenue. Variables : {mention}, {name}, {server}, {number} (nb de membres)"""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg["welcome_channel"] = channel.id
    cfg["welcome_message"]  = message
    save_config()
    preview_desc = (message.replace("{mention}", ctx.author.mention)
                       .replace("{server}", ctx.guild.name)
                       .replace("{name}", str(ctx.author))
                       .replace("{number}", str(ctx.guild.member_count)))
    preview_title = cfg.get("welcome_title", "Bienvenue sur le serveur !")
    e = success_embed("✅ Message de bienvenue configuré", "")
    e.add_field(name="Salon", value=channel.mention, inline=True)
    e.add_field(name="Variables disponibles", value="`{mention}` `{name}` `{server}` `{number}`", inline=False)
    await ctx.send(embed=e)

    aperçu = discord.Embed(title=preview_title, description=preview_desc, color=discord.Color.from_rgb(0, 0, 0))
    if cfg.get("welcome_image"):
        aperçu.set_image(url=cfg["welcome_image"])
    await ctx.send(content="👀 **Aperçu :**", embed=aperçu)

@bot.command(name="setwelcometitle")
@commands.has_permissions(administrator=True)
async def setwelcometitle(ctx, *, titre: str):
    """Définir le titre de l'embed de bienvenue (variables : {mention} {name} {server} {number}).
    Usage : +setwelcometitle Bienvenue sur le serveur !"""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg["welcome_title"] = titre[:256]
    save_config()
    await ctx.reply(embed=success_embed("✅ Titre de bienvenue défini", f"Nouveau titre : **{titre}**"))

@bot.command(name="setwelcomeimage", aliases=["setwelcomegif"])
@commands.has_permissions(administrator=True)
async def setwelcomeimage(ctx, url: str = None):
    """Définir l'image/gif affiché en grand dans le message de bienvenue (comme les bots type 'Rosa').
    Usage : +setwelcomeimage <url>  — ou joins directement une image/gif à ton message."""
    cfg = get_guild_cfg(ctx.guild.id)
    final_url = None
    if ctx.message.attachments:
        final_url = ctx.message.attachments[0].url
    elif url:
        final_url = url
    if not final_url:
        return await ctx.reply("❌ Fournis une URL, ou joins directement une image/gif à ton message.")
    cfg["welcome_image"] = final_url
    save_config()
    e = success_embed("✅ Image de bienvenue définie", "Voici un aperçu :")
    e.set_image(url=final_url)
    await ctx.send(embed=e)

@bot.command(name="removewelcomeimage")
@commands.has_permissions(administrator=True)
async def removewelcomeimage(ctx):
    """Retirer l'image/gif du message de bienvenue."""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg.pop("welcome_image", None)
    save_config()
    await ctx.reply(embed=success_embed("✅ Image retirée", "Le message de bienvenue n'affichera plus d'image."))

@bot.command(name="setinvitecheck", aliases=["setinvitelog"])
@commands.has_permissions(administrator=True)
async def setinvitecheck(ctx, channel: discord.TextChannel):
    """Choisir le salon où seront loggées les arrivées (qui a invité qui, invites vanity, arrivées OAuth).
    Usage : +setinvitecheck <#salon>"""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg["invite_log_channel"] = channel.id
    save_config()
    await refresh_invite_cache(ctx.guild)
    await ctx.reply(embed=success_embed(
        "✅ Invite-Check configuré",
        f"Les arrivées seront désormais suivies dans {channel.mention}."
    ))

@bot.command(name="removeinvitecheck")
@commands.has_permissions(administrator=True)
async def removeinvitecheck(ctx):
    """Désactiver le suivi des invitations (Invite-Check)."""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg.pop("invite_log_channel", None)
    save_config()
    await ctx.reply(embed=success_embed("✅ Invite-Check désactivé", "Le suivi des arrivées a été désactivé."))

@bot.command(name="setjtc", aliases=["setvocalcreator", "setcreatevoice"])
@commands.has_permissions(administrator=True)
async def setjtc(ctx, *, salon: str = None):
    """Configurer le salon 'Rejoindre pour créer' : quand un membre le rejoint, un salon vocal
    personnel 100% personnalisable est créé automatiquement, avec un panneau de gestion envoyé en MP.
    Usage :
      +setjtc create        → crée automatiquement le salon hub "➕ Créer un salon"
      +setjtc <#salon-vocal> → utilise un salon vocal existant comme hub"""
    cfg = get_guild_cfg(ctx.guild.id)

    if not salon or salon.lower() == "create":
        try:
            hub = await ctx.guild.create_voice_channel(
                "➕ Créer un salon",
                reason=f"Salon 'Rejoindre pour créer' créé par {ctx.author}"
            )
        except discord.Forbidden:
            return await ctx.reply("❌ Je n'ai pas la permission de créer un salon vocal.")
        cfg["jtc_channel"] = hub.id
        save_config()
        return await ctx.reply(embed=success_embed(
            "✅ Salon 'Créer un salon' configuré",
            f"{hub.mention} a été créé.\n"
            f"Quand un membre le rejoint, un salon vocal personnel lui est automatiquement créé, "
            f"avec un panneau de gestion (verrouiller, cacher, limite, renommer, qualité, mute/kick "
            f"quelqu'un, transférer, supprimer…) envoyé en message privé."
        ))

    try:
        channel = await commands.VoiceChannelConverter().convert(ctx, salon)
    except commands.BadArgument:
        return await ctx.reply("❌ Salon vocal introuvable. Utilise `+setjtc create` ou mentionne un salon vocal existant.")

    cfg["jtc_channel"] = channel.id
    save_config()
    await ctx.reply(embed=success_embed(
        "✅ Salon 'Créer un salon' configuré",
        f"{channel.mention} servira désormais de salon 'Rejoindre pour créer'."
    ))

@bot.command(name="removejtc")
@commands.has_permissions(administrator=True)
async def removejtc(ctx):
    """Désactiver le système de salons vocaux temporaires ('Rejoindre pour créer')."""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg.pop("jtc_channel", None)
    save_config()
    await ctx.reply(embed=success_embed(
        "✅ Désactivé",
        "Le système de salons vocaux temporaires a été désactivé (les salons déjà créés ne sont pas supprimés)."
    ))

@bot.command()
async def userinfo(ctx, member: discord.Member = None):
    """Afficher les informations d'un membre."""
    member = member or ctx.author
    roles  = [r.mention for r in member.roles if r != ctx.guild.default_role]
    gid, uid = str(ctx.guild.id), str(member.id)
    warn_count = len(warns_db.get(gid, {}).get(uid, []))
    married_to = marriages_db.get(gid, {}).get(uid)

    e = discord.Embed(title=f"👤 {member}", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    e.set_thumbnail(url=member.display_avatar.url)
    e.add_field(name="ID",          value=member.id,                                     inline=True)
    e.add_field(name="Surnom",      value=member.nick or "Aucun",                        inline=True)
    e.add_field(name="Bot",         value="✅" if member.bot else "❌",                   inline=True)
    e.add_field(name="Compte créé", value=f"<t:{int(member.created_at.timestamp())}:R>", inline=True)
    e.add_field(name="A rejoint",   value=f"<t:{int(member.joined_at.timestamp())}:R>",  inline=True)
    e.add_field(name="⚠️ Warns",    value=str(warn_count),                              inline=True)
    if married_to:
        partner = ctx.guild.get_member(int(married_to))
        e.add_field(name="💍 Marié(e) à", value=partner.mention if partner else f"<@{married_to}>", inline=True)
    e.add_field(name=f"Rôles ({len(roles)})", value=" ".join(roles) if roles else "Aucun", inline=False)
    if member.timed_out_until and member.timed_out_until > datetime.now(timezone.utc):
        e.add_field(name="🔇 Muet jusqu'à", value=f"<t:{int(member.timed_out_until.timestamp())}:R>", inline=False)
    await ctx.send(embed=e)

@bot.command()
async def whois(ctx, member: discord.Member = None):
    """Alias de userinfo."""
    await ctx.invoke(bot.get_command("userinfo"), member=member)

@bot.command()
async def serverinfo(ctx):
    """Afficher les informations du serveur."""
    g = ctx.guild
    e = discord.Embed(title=f"🏠 {g.name}", description="", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    if g.icon:
        e.set_thumbnail(url=g.icon.url)
    e.add_field(name="ID",            value=g.id,                                         inline=True)
    e.add_field(name="Propriétaire",  value=g.owner.mention,                              inline=True)
    e.add_field(name="Membres",       value=g.member_count,                               inline=True)
    e.add_field(name="Salons texte",  value=len(g.text_channels),                         inline=True)
    e.add_field(name="Salons vocaux", value=len(g.voice_channels),                        inline=True)
    e.add_field(name="Rôles",         value=len(g.roles),                                 inline=True)
    e.add_field(name="Emojis",        value=f"{len(g.emojis)}/{g.emoji_limit}",           inline=True)
    e.add_field(name="Niveau boost",  value=f"⭐ Niveau {g.premium_tier}",                inline=True)
    e.add_field(name="Boosts",        value=g.premium_subscription_count or 0,            inline=True)
    e.add_field(name="Créé le",       value=f"<t:{int(g.created_at.timestamp())}:F>",     inline=False)
    if g.banner:
        e.set_image(url=g.banner.url)
    await ctx.send(embed=e)

@bot.command()
async def roleinfo(ctx, role: discord.Role):
    """Afficher les informations d'un rôle."""
    perms = [p.replace("_", " ").title() for p, v in role.permissions if v]
    e = discord.Embed(title=f"🏷️ Rôle : {role.name}", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
    e.add_field(name="ID",           value=role.id,                         inline=True)
    e.add_field(name="Couleur",      value=str(role.color),                 inline=True)
    e.add_field(name="Membres",      value=len(role.members),               inline=True)
    e.add_field(name="Mentionnable", value="✅" if role.mentionable else "❌", inline=True)
    e.add_field(name="Hoisted",      value="✅" if role.hoist else "❌",     inline=True)
    e.add_field(name="Créé le",      value=f"<t:{int(role.created_at.timestamp())}:R>", inline=True)
    if perms:
        e.add_field(name=f"Permissions ({len(perms)})", value=", ".join(perms[:15]) + ("..." if len(perms) > 15 else ""), inline=False)
    await ctx.send(embed=e)

# ─────────────────────────────────────────
#  CONFIGURATION
# ─────────────────────────────────────────
@bot.command()
@commands.has_permissions(administrator=True)
async def setlog(ctx, channel: discord.TextChannel):
    """Définir le salon de logs de modération."""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg["log_channel"] = channel.id
    save_config()
    await ctx.reply(f"✅ Salon de logs défini sur {channel.mention}.")

@bot.command()
@commands.has_permissions(administrator=True)
async def setmuterole(ctx, role: discord.Role):
    """Définir le rôle utilisé pour les mutes manuels (legacy)."""
    cfg = get_guild_cfg(ctx.guild.id)
    cfg["mute_role"] = role.id
    save_config()
    await ctx.reply(f"✅ Rôle mute défini sur {role.mention}.")

# ─────────────────────────────────────────
#  AUTOMOD — Commande principale
# ─────────────────────────────────────────
AUTOMOD_RULES = {
    "links":       "anti_links",
    "invites":     "anti_invites",
    "spam":        "anti_spam",
    "caps":        "anti_caps",
    "mentions":    "anti_mentions",
    "badwords":    "anti_badwords",
    "zalgo":       "anti_zalgo",
    "flood":       "anti_flood",
    "scam":        "anti_scam",
    "emoji":       "anti_emoji",
    "attachments": "anti_attachments",
    "newlines":    "anti_newlines",
}

@bot.command(name="automod")
@commands.has_permissions(administrator=True)
async def automod_cmd(ctx, sous_commande: str = "status", *args):
    """Gérer l'automod du serveur."""
    am_cfg = get_automod_cfg(ctx.guild.id)
    sc = sous_commande.lower()

    # ── STATUS ────────────────────────────────────────────────────────────
    if sc == "status":
        def oc(val): return "🟢 ON" if val else "🔴 OFF"
        exempt_roles    = [ctx.guild.get_role(int(r)) for r in am_cfg.get("exempt_roles", []) if ctx.guild.get_role(int(r))]
        exempt_channels = [ctx.guild.get_channel(int(c)) for c in am_cfg.get("exempt_channels", []) if ctx.guild.get_channel(int(c))]
        whitelist = am_cfg.get("whitelist_domains", [])

        e = discord.Embed(title="🛡️ Configuration AutoMod", color=discord.Color.from_rgb(0, 0, 0), timestamp=datetime.now(timezone.utc))
        e.add_field(name="🔘 Statut global", value=oc(am_cfg.get("enabled")), inline=False)
        e.add_field(
            name="📋 Règles",
            value=(
                f"{oc(am_cfg.get('anti_links'))} **Anti-liens** *(GIFs autorisés)*\n"
                f"{oc(am_cfg.get('anti_invites'))} **Anti-invitations Discord**\n"
                f"{oc(am_cfg.get('anti_spam'))} **Anti-spam** ({am_cfg.get('spam_threshold')} msg/{am_cfg.get('spam_interval')}s)\n"
                f"{oc(am_cfg.get('anti_caps'))} **Anti-majuscules** ({am_cfg.get('caps_percent')}%)\n"
                f"{oc(am_cfg.get('anti_mentions'))} **Anti-@mentions** (max {am_cfg.get('max_mentions')})\n"
                f"{oc(am_cfg.get('anti_badwords'))} **Mots interdits** ({len(am_cfg.get('badwords', []))} mot(s))\n"
                f"{oc(am_cfg.get('anti_zalgo'))} **Anti-Zalgo**\n"
                f"{oc(am_cfg.get('anti_flood'))} **Anti-flood** (seuil {am_cfg.get('flood_count')})\n"
                f"{oc(am_cfg.get('anti_scam'))} **Anti-scam**\n"
                f"{oc(am_cfg.get('anti_emoji'))} **Anti-emoji** (max {am_cfg.get('max_emojis')})\n"
                f"{oc(am_cfg.get('anti_attachments'))} **Anti-pièces jointes** (max {am_cfg.get('max_attachments')})\n"
                f"{oc(am_cfg.get('anti_newlines'))} **Anti-retours à la ligne** (max {am_cfg.get('max_newlines')})"
            ),
            inline=False
        )
        threshold = am_cfg.get("warn_threshold", 0)
        e.add_field(
            name="⚙️ Action & Seuil Warns",
            value=(
                f"**Action :** `{am_cfg.get('action', 'delete')}`\n"
                f"**Durée mute auto :** `{am_cfg.get('mute_duration', '10m')}`\n"
                f"**Seuil warns :** `{threshold if threshold > 0 else 'désactivé'}`"
                + (f"\n**Action au seuil :** `{am_cfg.get('warn_action')}` ({am_cfg.get('warn_action_dur')})" if threshold > 0 else "") + f"\n**Log automod :** {oc(am_cfg.get('log_automod', True))}"
            ),
            inline=True
        )
        e.add_field(
            name="🚫 Exemptions",
            value=(
                f"**Rôles :** {', '.join(r.mention for r in exempt_roles) or 'Aucun'}\n"
                f"**Salons :** {', '.join(c.mention for c in exempt_channels) or 'Aucun'}\n"
                f"**Domaines whitelist :** {', '.join(f'`{d}`' for d in whitelist) or 'Aucun'}"
            ),
            inline=True
        )
        await ctx.send(embed=e)

    # ── ENABLE / DISABLE ──────────────────────────────────────────────────
    elif sc in ("enable", "disable"):
        am_cfg["enabled"] = (sc == "enable")
        save_config()
        state = "activé 🟢" if am_cfg["enabled"] else "désactivé 🔴"
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"L'automod a été **{state}**."))

    # ── SET <règle> on/off ────────────────────────────────────────────────
    elif sc == "set":
        if len(args) < 2:
            return await ctx.reply("❌ Usage : `+automod set <règle> on/off`\nRègles : " + ", ".join(AUTOMOD_RULES.keys()))
        rule_name, toggle = args[0].lower(), args[1].lower()
        if rule_name not in AUTOMOD_RULES:
            return await ctx.reply(f"❌ Règle inconnue. Disponibles : `{'`, `'.join(AUTOMOD_RULES.keys())}`")
        if toggle not in ("on", "off"):
            return await ctx.reply("❌ Valeur : `on` ou `off`.")
        am_cfg[AUTOMOD_RULES[rule_name]] = (toggle == "on")
        save_config()
        state = "activée 🟢" if toggle == "on" else "désactivée 🔴"
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Règle **{rule_name}** {state}."))

    # ── ACTION ────────────────────────────────────────────────────────────
    elif sc == "action":
        if not args:
            return await ctx.reply("❌ Usage : `+automod action <delete|warn|mute|kick|ban>`")
        action = args[0].lower()
        if action not in ("delete", "warn", "mute", "kick", "ban"):
            return await ctx.reply("❌ Actions : `delete`, `warn`, `mute`, `kick`, `ban`.")
        am_cfg["action"] = action
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Action définie sur **{action}**."))

    # ── MUTE_DURATION ─────────────────────────────────────────────────────
    elif sc == "mute_duration":
        if not args or not parse_duration(args[0]):
            return await ctx.reply("❌ Usage : `+automod mute_duration <durée>` (ex : `10m`, `1h`)")
        am_cfg["mute_duration"] = args[0]
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Durée de mute auto : **{args[0]}**."))

    # ── WARN_THRESHOLD ────────────────────────────────────────────────────
    elif sc == "warn_threshold":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod warn_threshold <nombre>` (0 = désactivé)")
        val = int(args[0])
        am_cfg["warn_threshold"] = val
        save_config()
        msg = f"Seuil warns défini sur **{val}**." if val > 0 else "Seuil warns **désactivé**."
        await ctx.reply(embed=success_embed("🛡️ AutoMod", msg))

    # ── WARN_ACTION ───────────────────────────────────────────────────────
    elif sc == "warn_action":
        if not args or args[0].lower() not in ("mute", "kick", "ban", "tempban"):
            return await ctx.reply("❌ Usage : `+automod warn_action <mute|kick|ban|tempban>`")
        am_cfg["warn_action"] = args[0].lower()
        if len(args) >= 2 and parse_duration(args[1]):
            am_cfg["warn_action_dur"] = args[1]
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Action au seuil de warns : **{args[0]}**."))

    # ── WHITELIST_DOMAIN ──────────────────────────────────────────────────
    elif sc == "whitelist_domain":
        if len(args) < 2:
            return await ctx.reply("❌ Usage : `+automod whitelist_domain add/remove <domaine>`")
        action = args[0].lower()
        domain = args[1].lower()
        whitelist = am_cfg.setdefault("whitelist_domains", [])
        if action == "add":
            if domain in whitelist:
                return await ctx.reply(f"❌ `{domain}` est déjà dans la whitelist.")
            whitelist.append(domain)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Domaine `{domain}` ajouté à la whitelist."))
        elif action == "remove":
            if domain not in whitelist:
                return await ctx.reply(f"❌ `{domain}` n'est pas dans la whitelist.")
            whitelist.remove(domain)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Domaine `{domain}` retiré de la whitelist."))
        else:
            await ctx.reply("❌ Action invalide. Utilise `add` ou `remove`.")

    # ── SPAM_THRESHOLD ────────────────────────────────────────────────────
    elif sc == "spam_threshold":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod spam_threshold <nombre>`")
        val = int(args[0])
        if not 2 <= val <= 50:
            return await ctx.reply("❌ Valeur entre 2 et 50.")
        am_cfg["spam_threshold"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Seuil spam : **{val}** messages."))

    # ── SPAM_INTERVAL ─────────────────────────────────────────────────────
    elif sc == "spam_interval":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod spam_interval <secondes>`")
        val = int(args[0])
        if not 1 <= val <= 60:
            return await ctx.reply("❌ Valeur entre 1 et 60.")
        am_cfg["spam_interval"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Intervalle spam : **{val}s**."))

    # ── CAPS_PERCENT ──────────────────────────────────────────────────────
    elif sc == "caps_percent":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod caps_percent <nombre>` (ex : 70)")
        val = int(args[0])
        if not 10 <= val <= 100:
            return await ctx.reply("❌ Valeur entre 10 et 100.")
        am_cfg["caps_percent"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Seuil majuscules : **{val}%**."))

    # ── MAX_MENTIONS ──────────────────────────────────────────────────────
    elif sc == "max_mentions":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod max_mentions <nombre>`")
        val = int(args[0])
        if not 1 <= val <= 50:
            return await ctx.reply("❌ Valeur entre 1 et 50.")
        am_cfg["max_mentions"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Nb max mentions : **{val}**."))

    # ── MAX_EMOJIS ────────────────────────────────────────────────────────
    elif sc == "max_emojis":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod max_emojis <nombre>`")
        val = int(args[0])
        if not 1 <= val <= 100:
            return await ctx.reply("❌ Valeur entre 1 et 100.")
        am_cfg["max_emojis"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Nb max emojis : **{val}**."))

    # ── MAX_ATTACHMENTS ───────────────────────────────────────────────────
    elif sc == "max_attachments":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod max_attachments <nombre>`")
        val = int(args[0])
        if not 1 <= val <= 20:
            return await ctx.reply("❌ Valeur entre 1 et 20.")
        am_cfg["max_attachments"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Nb max pièces jointes : **{val}**."))

    # ── MAX_NEWLINES ──────────────────────────────────────────────────────
    elif sc == "max_newlines":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod max_newlines <nombre>`")
        val = int(args[0])
        if not 1 <= val <= 100:
            return await ctx.reply("❌ Valeur entre 1 et 100.")
        am_cfg["max_newlines"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Nb max retours à la ligne : **{val}**."))

    # ── FLOOD_COUNT ───────────────────────────────────────────────────────
    elif sc == "flood_count":
        if not args or not args[0].isdigit():
            return await ctx.reply("❌ Usage : `+automod flood_count <nombre>`")
        val = int(args[0])
        if not 2 <= val <= 20:
            return await ctx.reply("❌ Valeur entre 2 et 20.")
        am_cfg["flood_count"] = val
        save_config()
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Seuil flood : **{val}** messages identiques."))

    # ── BADWORD add/remove/list ───────────────────────────────────────────
    elif sc == "badword":
        if not args:
            return await ctx.reply("❌ Usage : `+automod badword add/remove/list <mot>`")
        action = args[0].lower()
        badwords = am_cfg.setdefault("badwords", [])
        if action == "list":
            if not badwords:
                return await ctx.reply("ℹ️ Aucun mot interdit configuré.")
            return await ctx.send(embed=warning_embed("🚫 Mots interdits", "\n".join(f"`{w}`" for w in badwords)))
        if len(args) < 2:
            return await ctx.reply(f"❌ Usage : `+automod badword {action} <mot>`")
        word = args[1].lower()
        if action == "add":
            if word in badwords:
                return await ctx.reply(f"❌ `{word}` est déjà dans la liste.")
            badwords.append(word)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Mot `{word}` ajouté."))
        elif action == "remove":
            if word not in badwords:
                return await ctx.reply(f"❌ `{word}` n'est pas dans la liste.")
            badwords.remove(word)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Mot `{word}` retiré."))
        else:
            await ctx.reply("❌ Action invalide. Utilise `add`, `remove` ou `list`.")

    # ── EXEMPT_ROLE ───────────────────────────────────────────────────────
    elif sc == "exempt_role":
        if len(args) < 2 or not ctx.message.role_mentions:
            return await ctx.reply("❌ Usage : `+automod exempt_role @rôle add/remove`")
        role   = ctx.message.role_mentions[0]
        action = args[-1].lower()
        exempt = am_cfg.setdefault("exempt_roles", [])
        rid    = str(role.id)
        if action == "add":
            if rid in exempt:
                return await ctx.reply(f"❌ {role.mention} est déjà exempté.")
            exempt.append(rid)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"{role.mention} ajouté aux rôles exemptés."))
        elif action == "remove":
            if rid not in exempt:
                return await ctx.reply(f"❌ {role.mention} n'est pas exempté.")
            exempt.remove(rid)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"{role.mention} retiré des rôles exemptés."))
        else:
            await ctx.reply("❌ Action invalide. Utilise `add` ou `remove`.")

    # ── EXEMPT_CHANNEL ────────────────────────────────────────────────────
    elif sc == "exempt_channel":
        if len(args) < 2 or not ctx.message.channel_mentions:
            return await ctx.reply("❌ Usage : `+automod exempt_channel #salon add/remove`")
        channel = ctx.message.channel_mentions[0]
        action  = args[-1].lower()
        exempt  = am_cfg.setdefault("exempt_channels", [])
        cid     = str(channel.id)
        if action == "add":
            if cid in exempt:
                return await ctx.reply(f"❌ {channel.mention} est déjà exempté.")
            exempt.append(cid)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"{channel.mention} ajouté aux salons exemptés."))
        elif action == "remove":
            if cid not in exempt:
                return await ctx.reply(f"❌ {channel.mention} n'est pas exempté.")
            exempt.remove(cid)
            save_config()
            await ctx.reply(embed=success_embed("🛡️ AutoMod", f"{channel.mention} retiré des salons exemptés."))
        else:
            await ctx.reply("❌ Action invalide. Utilise `add` ou `remove`.")

    # ── LOG_AUTOMOD ───────────────────────────────────────────────────────
    elif sc == "log":
        if not args or args[0].lower() not in ("on", "off"):
            return await ctx.reply("❌ Usage : `+automod log on/off`")
        am_cfg["log_automod"] = (args[0].lower() == "on")
        save_config()
        state = "activé 🟢" if am_cfg["log_automod"] else "désactivé 🔴"
        await ctx.reply(embed=success_embed("🛡️ AutoMod", f"Log automod **{state}**."))

    else:
        await ctx.reply(f"❌ Sous-commande inconnue. Tape `{PREFIX}help automod` pour l'aide.")

# ─────────────────────────────────────────
#  INVITATIONS & STATISTIQUES MEMBRES
# ─────────────────────────────────────────
@bot.command(name="invites")
async def invites_cmd(ctx, member: discord.Member = None):
    """Afficher le nombre d'invitations d'un membre sur le serveur. Usage : +invites [@membre]"""
    member = member or ctx.author
    try:
        guild_invites = await ctx.guild.invites()
    except discord.Forbidden:
        return await ctx.reply("❌ Je n'ai pas la permission de voir les invitations du serveur (`Gérer le serveur` requis).")

    joins   = 0
    leaves  = 0
    fake    = 0
    bonus   = 0

    for inv in guild_invites:
        if inv.inviter and inv.inviter.id == member.id:
            uses = inv.uses or 0
            joins += uses

    # Discord ne fournit pas nativement leaves/fake/bonus via l'API — on affiche
    # joins (réel) et les 3 autres à 0 (comme la plupart des bots invites).
    total = joins + bonus - leaves - fake

    e = discord.Embed(
        title=f"Invites count of 🌐 @{member.display_name}",
        description=(
            f"*generated in {round(ctx.bot.latency * 1000)}ms*\n\n"
            f"✅ **{joins}** joins in total\n"
            f"❌ **{leaves}** leaves\n"
            f"💩 **{fake}** fake\n"
            f"✨ **{bonus}** bonus\n\n"
            f"This user has currently **{max(total, 0)}** invites ! 👋"
        ),
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    e.set_thumbnail(url=member.display_avatar.url)
    e.set_footer(text=f"Demandé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.send(embed=e)


@bot.command(name="statistic")
async def statistic_cmd(ctx, member: discord.Member = None):
    """Afficher les statistiques de messages et de temps vocal d'un membre. Usage : +statistic [@membre]"""
    member = member or ctx.author
    stats  = _member_stats[ctx.guild.id][member.id]

    # Temps vocal : accumulé + session en cours (si actuellement connecté)
    voice_seconds = stats["voice_seconds"]
    if stats["voice_joined"] is not None:
        voice_seconds += time.time() - stats["voice_joined"]

    msg_count = stats["messages"]

    # Formatage du temps vocal
    total_s = int(voice_seconds)
    hours   = total_s // 3600
    minutes = (total_s % 3600) // 60
    seconds = total_s % 60
    if hours > 0:
        voice_str = f"{hours}h {minutes}m {seconds}s"
    elif minutes > 0:
        voice_str = f"{minutes}m {seconds}s"
    else:
        voice_str = f"{seconds}s"

    # Salon vocal actuel (le cas échéant)
    voice_channel = member.voice.channel if member.voice else None

    e = discord.Embed(
        title=f"📊 Statistiques de {member.display_name}",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    e.set_thumbnail(url=member.display_avatar.url)
    e.add_field(
        name="💬 Messages",
        value=f"**{msg_count}** message(s) envoyé(s)\n*(depuis le dernier démarrage du bot)*",
        inline=False
    )
    e.add_field(
        name="🔊 Temps en vocal",
        value=(
            f"**{voice_str}**\n"
            f"*(depuis le dernier démarrage du bot)*\n"
            + (f"📍 Actuellement dans {voice_channel.mention}" if voice_channel else "📴 Pas en vocal")
        ),
        inline=False
    )
    e.add_field(name="📅 A rejoint le serveur", value=f"<t:{int(member.joined_at.timestamp())}:R>" if member.joined_at else "Inconnu", inline=True)
    e.add_field(name="🏷️ Compte créé le",      value=f"<t:{int(member.created_at.timestamp())}:R>", inline=True)
    e.set_footer(text=f"Demandé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.send(embed=e)


@bot.command(name="leaderboard")
async def leaderboard_cmd(ctx):
    """Afficher le top 3 messages & top 3 temps vocal, ainsi que ton propre classement. Usage : +leaderboard"""
    guild_stats = _member_stats[ctx.guild.id]

    # Construire les listes en incluant la session vocal en cours
    now_ts = time.time()
    msg_list = []
    voice_list = []
    for uid, stats in guild_stats.items():
        member = ctx.guild.get_member(uid)
        if not member or member.bot:
            continue
        msg_count = stats["messages"]
        voice_s = stats["voice_seconds"]
        if stats["voice_joined"] is not None:
            voice_s += now_ts - stats["voice_joined"]
        msg_list.append((uid, msg_count))
        voice_list.append((uid, voice_s))

    # Trier par valeur décroissante
    msg_list.sort(key=lambda x: x[1], reverse=True)
    voice_list.sort(key=lambda x: x[1], reverse=True)

    def format_voice(seconds: float) -> str:
        total_s = int(seconds)
        h = total_s // 3600
        m = (total_s % 3600) // 60
        s = total_s % 60
        if h > 0:
            return f"{h}h {m}m {s}s"
        elif m > 0:
            return f"{m}m {s}s"
        return f"{s}s"

    medals = ["🥇", "🥈", "🥉"]

    # ── Top 3 Messages ──
    msg_lines = []
    for i, (uid, count) in enumerate(msg_list[:3]):
        member = ctx.guild.get_member(uid)
        name = member.display_name if member else f"<@{uid}>"
        medal = medals[i] if i < 3 else f"#{i+1}"
        msg_lines.append(f"{medal} **{name}** — `{count}` message(s)")

    if not msg_lines:
        msg_lines = ["*Aucune donnée disponible*"]

    # ── Top 3 Vocal ──
    voice_lines = []
    for i, (uid, seconds) in enumerate(voice_list[:3]):
        member = ctx.guild.get_member(uid)
        name = member.display_name if member else f"<@{uid}>"
        medal = medals[i] if i < 3 else f"#{i+1}"
        voice_lines.append(f"{medal} **{name}** — `{format_voice(seconds)}`")

    if not voice_lines:
        voice_lines = ["*Aucune donnée disponible*"]

    # ── Classement de l'appelant ──
    author_id = ctx.author.id
    author_msg_rank = next((i + 1 for i, (uid, _) in enumerate(msg_list) if uid == author_id), None)
    author_voice_rank = next((i + 1 for i, (uid, _) in enumerate(voice_list) if uid == author_id), None)
    author_msg_count = guild_stats[author_id]["messages"]
    author_voice_s = guild_stats[author_id]["voice_seconds"]
    if guild_stats[author_id]["voice_joined"] is not None:
        author_voice_s += now_ts - guild_stats[author_id]["voice_joined"]

    if author_msg_rank:
        your_msg_str = f"#{author_msg_rank} — `{author_msg_count}` message(s)"
    else:
        your_msg_str = "Aucune donnée"

    if author_voice_rank:
        your_voice_str = f"#{author_voice_rank} — `{format_voice(author_voice_s)}`"
    else:
        your_voice_str = "Aucune donnée"

    e = discord.Embed(
        title=f"🏆 Classement de {ctx.guild.name}",
        description="*Statistiques depuis le dernier démarrage du bot.*",
        color=discord.Color.from_rgb(0, 0, 0),
        timestamp=datetime.now(timezone.utc)
    )
    if ctx.guild.icon:
        e.set_thumbnail(url=ctx.guild.icon.url)

    e.add_field(
        name="💬 Top 3 — Messages",
        value="\n".join(msg_lines),
        inline=False
    )
    e.add_field(
        name="🔊 Top 3 — Temps vocal",
        value="\n".join(voice_lines),
        inline=False
    )
    e.add_field(
        name=f"📊 Ton classement — {ctx.author.display_name}",
        value=(
            f"💬 Messages : {your_msg_str}\n"
            f"🔊 Vocal : {your_voice_str}"
        ),
        inline=False
    )
    e.set_footer(text=f"Demandé par {ctx.author}", icon_url=ctx.author.display_avatar.url)
    await ctx.send(embed=e)


# ─────────────────────────────────────────
#  Lancement avec reconnexion automatique
# ─────────────────────────────────────────
if __name__ == "__main__":
    if not TOKEN:
        log.error("❌ DISCORD_TOKEN manquant ! Vérifie tes variables d'environnement.")
        exit(1)

    RETRY_DELAY = 5
    MAX_RETRIES = 10
    attempts = 0

    while True:
        try:
            log.info(f"🚀 Démarrage du bot (tentative {attempts + 1})...")
            bot.run(TOKEN, log_handler=None)
            # bot.run() est revenu proprement (arrêt interne discord.py) — on remet le compteur à zéro
            attempts = 0
        except discord.errors.LoginFailure:
            log.error("❌ Token Discord invalide.")
            break
        except (discord.errors.ConnectionClosed,
                discord.errors.GatewayNotFound,
                discord.errors.HTTPException) as e:
            attempts += 1
            log.warning(f"⚠️ Erreur réseau : {e}. Reconnexion dans {RETRY_DELAY}s... ({attempts}/{MAX_RETRIES})")
        except KeyboardInterrupt:
            log.info("🛑 Arrêt manuel du bot.")
            break
        except Exception as e:
            attempts += 1
            log.error(f"💥 Erreur inattendue :\n{traceback.format_exc()}")
            log.warning(f"🔄 Redémarrage dans {RETRY_DELAY}s... ({attempts}/{MAX_RETRIES})")

        if attempts >= MAX_RETRIES:
            log.error(f"❌ {MAX_RETRIES} tentatives échouées. Arrêt du bot.")
            break

        time.sleep(RETRY_DELAY)