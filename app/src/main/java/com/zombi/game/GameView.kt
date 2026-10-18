package com.zombi.game

import android.app.Activity
import android.app.AlertDialog
import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.RectF
import android.view.MotionEvent
import android.view.SurfaceHolder
import android.view.SurfaceView
import android.widget.EditText
import java.util.concurrent.ConcurrentLinkedQueue
import kotlin.math.atan2
import kotlin.math.cos
import kotlin.math.floor
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.random.Random

class GameView(ctx: Context) : SurfaceView(ctx), SurfaceHolder.Callback, Runnable {

    class Zombie(var x: Float, var y: Float, var hp: Float, val speed: Float, val r: Float, val big: Boolean)
    class Guard(
        var x: Float, var y: Float, var hp: Float, val speed: Float,
        val base: Int, val clan: Int, val attacker: Boolean, val hx: Float, val hy: Float
    )
    class Bullet(var x: Float, var y: Float, val vx: Float, val vy: Float, var life: Float, val dmg: Float)
    class Pickup(var x: Float, var y: Float, val type: Int, var life: Float)
    class Base(val id: Int, val x: Float, val y: Float, var owner: Int, var level: Int) {
        var spawned = false
        var cap = 0f
        var attackTimer = 0f
        var attackClan = 1
        var attackersSpawned = false
    }
    class Quest(
        val type: Int, val target: Int, val resType: Int,
        val rewardXp: Int, val rewardRes: Int, val rewardResType: Int
    ) { var prog = 0 }

    companion object {
        const val BX = 1600f          // görev panosu (zombi bölgesi merkezi)
        const val BY = 1600f
        const val BOARD_R = 170f
        const val BASE_R = 150f
        val RES_NAMES = arrayOf("Odun", "Taş", "Metal")
        val RECIPES = arrayOf("Silah Yükselt", "Zırh Yükselt", "Medkit")
        val CLAN_NAMES = arrayOf("", "Kara Kurtlar", "Demir Yumruk", "Gölge", "Kızıl Kartal", "Yılan", "Çelik Kalkan", "Akrep")
        val CLAN_COLORS = intArrayOf(
            Color.rgb(60, 130, 230), Color.rgb(200, 60, 60), Color.rgb(230, 150, 40),
            Color.rgb(150, 80, 200), Color.rgb(60, 170, 110), Color.rgb(220, 200, 60),
            Color.rgb(200, 100, 160), Color.rgb(130, 130, 130)
        )
    }

    private var thread: Thread? = null
    @Volatile private var running = false
    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val actions = ConcurrentLinkedQueue<() -> Unit>()

    private var w = 1f
    private var h = 1f
    private var started = false

    // bölge: 0 = zombi bölgesi, 1 = üs bölgesi
    @Volatile private var zone = 0
    private val worldW: Float get() = if (zone == 0) 3200f else 5400f
    private val worldH: Float get() = if (zone == 0) 3200f else 3000f

    // oyuncu
    private var px = BX
    private var py = BY + 80f
    private var hp = 100f
    private var maxHp = 100f
    private var angle = 0f
    private var level = 1
    private var xp = 0
    private var kills = 0
    private var weaponLvl = 0
    private var armorLvl = 0
    private val res = IntArray(3)
    private var medkits = 0
    @Volatile private var dead = false
    @Volatile private var menuMode = 0   // 0 kapalı, 1 üretim, 2 görev, 3 klan

    // klan
    private var hasClan = false
    private var clanName = ""

    private var camX = 0f
    private var camY = 0f
    private var spawnTimer = 0f
    private var fireTimer = 0f
    private var attackEvtTimer = 40f
    private var warTimer = 7f
    private var incomeTimer = 10f

    @Volatile private var msg = ""
    @Volatile private var msgTimer = 0f

    private val zombies = ArrayList<Zombie>()
    private val guards = ArrayList<Guard>()
    private val bullets = ArrayList<Bullet>()
    private val pickups = ArrayList<Pickup>()
    private val bases = ArrayList<Base>()
    private val alive = IntArray(50)
    private val attAlive = IntArray(50)

    // görevler
    private val offers = ArrayList<Quest>()
    private var active: Quest? = null

    // dokunmatik
    @Volatile private var moveId = -1
    @Volatile private var moveCx = 0f
    @Volatile private var moveCy = 0f
    @Volatile private var moveX = 0f
    @Volatile private var moveY = 0f
    @Volatile private var aimId = -1
    @Volatile private var aimX = 0f
    @Volatile private var aimY = 0f

    init {
        holder.addCallback(this)
        val rng = Random(7)
        for (i in 0 until 50) {
            val col = i % 10
            val row = i / 10
            bases.add(
                Base(
                    i, 320f + col * 520f + rng.nextInt(-50, 51), 300f + row * 520f + rng.nextInt(-50, 51),
                    1 + rng.nextInt(7), 1 + rng.nextInt(5)
                )
            )
        }
        genOffers()
    }

    // ---------- yaşam döngüsü ----------
    override fun surfaceCreated(holder: SurfaceHolder) {
        running = true
        thread = Thread(this).also { it.start() }
    }

    override fun surfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
        w = width.toFloat(); h = height.toFloat()
        started = true
    }

    override fun surfaceDestroyed(holder: SurfaceHolder) {
        running = false
        try { thread?.join() } catch (_: InterruptedException) {}
    }

    override fun run() {
        var last = System.nanoTime()
        while (running) {
            val now = System.nanoTime()
            val dt = min((now - last) / 1e9f, 0.05f)
            last = now
            if (started) {
                msgTimer -= dt
                while (true) { val a = actions.poll() ?: break; a() }
                if (!dead && menuMode == 0) update(dt)
                val c = holder.lockCanvas()
                if (c != null) {
                    try { draw(c) } finally { holder.unlockCanvasAndPost(c) }
                }
            }
            try { Thread.sleep(8) } catch (_: InterruptedException) {}
        }
    }

    private fun say(s: String) { msg = s; msgTimer = 3.5f }

    // ---------- üretim ----------
    private fun cost(i: Int): IntArray = when (i) {
        0 -> intArrayOf(4, 0, 6 * (weaponLvl + 1))
        1 -> intArrayOf(4, 3 + 2 * armorLvl, 3 + 3 * armorLvl)
        else -> intArrayOf(3, 0, 2)
    }

    private fun affordable(c: IntArray) = res[0] >= c[0] && res[1] >= c[1] && res[2] >= c[2]
    private fun canCraft(i: Int) = affordable(cost(i))
    private val clanCost = intArrayOf(20, 20, 20)

    private fun craft(i: Int) {
        if (!canCraft(i)) return
        val c = cost(i)
        for (k in 0..2) res[k] -= c[k]
        when (i) {
            0 -> weaponLvl++
            1 -> armorLvl++
            else -> medkits++
        }
    }

    private fun useMedkit() {
        if (medkits > 0 && hp < maxHp) { hp = min(maxHp, hp + 50f); medkits-- }
    }

    private fun armorMul() = 1f / (1f + 0.15f * armorLvl)

    // ---------- klan ----------
    private fun askClanName() {
        (context as Activity).runOnUiThread {
            val et = EditText(context)
            et.setSingleLine()
            AlertDialog.Builder(context)
                .setTitle("Klan adı")
                .setView(et)
                .setPositiveButton("Kur") { _, _ ->
                    val n = et.text.toString().trim().take(14).ifEmpty { "Klanım" }
                    actions.add { foundClan(n) }
                }
                .setNegativeButton("İptal", null)
                .show()
        }
    }

    private fun foundClan(name: String) {
        if (hasClan || !affordable(clanCost)) return
        for (k in 0..2) res[k] -= clanCost[k]
        hasClan = true
        clanName = name
        say("$name klanı kuruldu! Üs Bölgesi'nden üs ele geçir.")
    }

    // ---------- görevler ----------
    private fun makeQuest(): Quest = when (Random.nextInt(3)) {
        0 -> { val n = 8 + level * 2; Quest(0, n, 0, n * 8, 3 + level, 2) }
        1 -> { val rt = Random.nextInt(3); val n = 10 + level * 2; Quest(1, n, rt, n * 6, 3 + level, 2) }
        else -> { val n = 2 + level / 3; Quest(2, n, 0, n * 40, 5 + level * 2, 2) }
    }

    private fun genOffers() {
        offers.clear()
        repeat(3) { offers.add(makeQuest()) }
    }

    private fun questTitle(q: Quest) = when (q.type) {
        0 -> "Zombi öldür: ${q.target}"
        1 -> "${RES_NAMES[q.resType]} topla: ${q.target}"
        else -> "İri zombi öldür: ${q.target}"
    }

    private fun questProgress(type: Int, resType: Int = -1) {
        val q = active ?: return
        if (q.type != type) return
        if (type == 1 && q.resType != resType) return
        q.prog++
        if (q.prog >= q.target) {
            addXp(q.rewardXp)
            res[q.rewardResType] += q.rewardRes
            say("Görev tamam! +${q.rewardXp} XP, +${q.rewardRes} Metal")
            active = null
        }
    }

    private fun xpNeed() = 30 + level * 20

    private fun addXp(n: Int) {
        xp += n
        while (xp >= xpNeed()) {
            xp -= xpNeed(); level++; maxHp += 10f; hp = maxHp
            say("Seviye $level!")
        }
    }

    // ---------- bölge geçişi / yeniden doğuş ----------
    private fun resetZoneState() {
        zombies.clear(); bullets.clear(); pickups.clear(); guards.clear()
        for (b in bases) { b.spawned = false; b.attackersSpawned = false; b.cap = 0f }
        if (zone == 0) { px = BX; py = BY + 80f } else { px = 2700f; py = 2900f }
    }

    private fun switchZone() {
        zone = 1 - zone
        resetZoneState()
        menuMode = 0; moveId = -1; aimId = -1
        say(if (zone == 0) "Zombi Bölgesi" else "Üs Bölgesi")
    }

    private fun respawn() {
        for (i in 0..2) res[i] /= 2
        hp = maxHp
        resetZoneState()
        menuMode = 0
        dead = false
    }

    // ---------- güncelleme ----------
    private fun update(dt: Float) {
        // hareket
        if (moveId != -1) {
            val dx = moveX - moveCx
            val dy = moveY - moveCy
            val d = hypot(dx, dy)
            if (d > 10f) {
                val power = min(d, 110f) / 110f
                px += dx / d * 280f * power * dt
                py += dy / d * 280f * power * dt
                if (aimId == -1) angle = atan2(dy, dx)
            }
        }
        px = px.coerceIn(20f, worldW - 20f)
        py = py.coerceIn(20f, worldH - 20f)
        camX = (px - w / 2).coerceIn(0f, max(0f, worldW - w))
        camY = (py - h / 2).coerceIn(0f, max(0f, worldH - h))

        // ateş
        fireTimer -= dt
        if (aimId != -1) {
            angle = atan2(aimY + camY - py, aimX + camX - px)
            if (fireTimer <= 0f) {
                fireTimer = 0.2f
                bullets.add(Bullet(px, py, cos(angle) * 720f, sin(angle) * 720f, 1.0f, 20f + weaponLvl * 8f + level * 2f))
            }
        }

        if (zone == 0) updateZombies(dt) else updateGuards(dt)

        // mermiler
        val bi = bullets.iterator()
        while (bi.hasNext()) {
            val b = bi.next()
            b.x += b.vx * dt; b.y += b.vy * dt; b.life -= dt
            var hit = false
            for (z in zombies) {
                if (hypot(b.x - z.x, b.y - z.y) < z.r + 4f) { z.hp -= b.dmg; hit = true; break }
            }
            if (!hit) for (g in guards) {
                if (hypot(b.x - g.x, b.y - g.y) < 20f) { g.hp -= b.dmg; hit = true; break }
            }
            if (hit || b.life <= 0f) bi.remove()
        }

        // ölen zombiler
        val zk = zombies.iterator()
        while (zk.hasNext()) {
            val z = zk.next()
            if (z.hp <= 0f) {
                zk.remove()
                kills++
                addXp(if (z.big) 40 else 10)
                questProgress(0)
                if (z.big) questProgress(2)
                val n = if (z.big) 3 + Random.nextInt(3) else 1 + Random.nextInt(2)
                repeat(n) { dropAt(z.x, z.y) }
            }
        }
        // ölen muhafızlar
        val gk = guards.iterator()
        while (gk.hasNext()) {
            val g = gk.next()
            if (g.hp <= 0f) { gk.remove(); addXp(15); dropAt(g.x, g.y) }
        }

        // kaynak toplama
        val pi = pickups.iterator()
        while (pi.hasNext()) {
            val p = pi.next()
            p.life -= dt
            val dx = px - p.x
            val dy = py - p.y
            val d = max(hypot(dx, dy), 0.001f)
            if (d < 110f) { p.x += dx / d * 320f * dt; p.y += dy / d * 320f * dt }
            if (d < 26f) { res[p.type]++; questProgress(1, p.type); pi.remove() }
            else if (p.life <= 0f) pi.remove()
        }

        // canlı muhafız sayıları
        alive.fill(0); attAlive.fill(0)
        for (g in guards) if (g.attacker) attAlive[g.base]++ else alive[g.base]++

        if (zone == 1) baseLogic(dt)
        globalTimers(dt)

        if (hp <= 0f) { hp = 0f; dead = true }
    }

    private fun dropAt(x: Float, y: Float) {
        val r = Random.nextInt(10)
        val type = if (r < 4) 0 else if (r < 7) 1 else 2
        pickups.add(Pickup(x + Random.nextInt(-25, 26), y + Random.nextInt(-25, 26), type, 40f))
    }

    private fun updateZombies(dt: Float) {
        spawnTimer -= dt
        val cap = min(8 + level * 2, 45)
        if (spawnTimer <= 0f && zombies.size < cap) {
            spawnTimer = max(0.4f, 1.2f - level * 0.03f)
            val a = Random.nextFloat() * 6.2832f
            val dist = hypot(w, h) / 2f + 80f
            val sx = (px + cos(a) * dist).coerceIn(0f, worldW)
            val sy = (py + sin(a) * dist).coerceIn(0f, worldH)
            if (hypot(sx - BX, sy - BY) > BOARD_R + 40f) {
                val big = Random.nextInt(10) == 0
                val m = if (big) 3f else 1f
                zombies.add(
                    Zombie(
                        sx, sy, (40f + level * 6f) * m,
                        (55f + min(level * 3f, 60f) + Random.nextFloat() * 25f) * (if (big) 0.7f else 1f),
                        if (big) 28f else 18f, big
                    )
                )
            }
        }
        val zi = zombies.iterator()
        while (zi.hasNext()) {
            val z = zi.next()
            val dx = px - z.x
            val dy = py - z.y
            val d = max(hypot(dx, dy), 0.001f)
            if (d > 1500f) { zi.remove(); continue }
            z.x += dx / d * z.speed * dt
            z.y += dy / d * z.speed * dt
            // görev panosu çevresi güvenli bölge
            val bx = z.x - BX
            val by = z.y - BY
            val bd = max(hypot(bx, by), 0.001f)
            if (bd < BOARD_R + z.r) {
                z.x = BX + bx / bd * (BOARD_R + z.r)
                z.y = BY + by / bd * (BOARD_R + z.r)
            }
            if (d < z.r + 16f) hp -= (if (z.big) 30f else 18f) * armorMul() * dt
        }
        if (hypot(px - BX, py - BY) < BOARD_R) hp = min(maxHp, hp + 6f * dt)
    }

    private fun updateGuards(dt: Float) {
        for (g in guards) {
            val dx = px - g.x
            val dy = py - g.y
            val d = max(hypot(dx, dy), 0.001f)
            if (d < 600f) {
                g.x += dx / d * g.speed * dt
                g.y += dy / d * g.speed * dt
            } else {
                val hx = g.hx - g.x
                val hy = g.hy - g.y
                val hd = hypot(hx, hy)
                if (hd > 8f) { g.x += hx / hd * g.speed * dt; g.y += hy / hd * g.speed * dt }
            }
            if (d < 32f) hp -= 16f * armorMul() * dt
        }
    }

    private fun spawnDefenders(b: Base) {
        val n = 2 + b.level
        for (k in 0 until n) {
            val a = 6.2832f * k / n
            val gx = b.x + cos(a) * 80f
            val gy = b.y + sin(a) * 80f
            guards.add(Guard(gx, gy, 60f + b.level * 35f + level * 4f, 110f, b.id, b.owner, false, gx, gy))
        }
    }

    private fun spawnAttackers(b: Base) {
        val n = 3 + b.level
        for (k in 0 until n) {
            val a = 6.2832f * k / n
            val gx = b.x + cos(a) * 120f
            val gy = b.y + sin(a) * 120f
            guards.add(Guard(gx, gy, 60f + b.level * 30f + level * 4f, 120f, b.id, b.attackClan, true, gx, gy))
        }
        attAlive[b.id] = n
    }

    private fun baseLogic(dt: Float) {
        for (b in bases) {
            val d = hypot(px - b.x, py - b.y)
            if (b.owner != 0) {
                if (!b.spawned && d < 400f) {
                    spawnDefenders(b); b.spawned = true
                    alive[b.id] = 2 + b.level
                } else if (b.spawned && d > 1000f) {
                    guards.removeAll { it.base == b.id && !it.attacker }
                    b.spawned = false; b.cap = 0f
                }
                if (d < 110f) {
                    if (!hasClan) {
                        if (msgTimer <= 0f) say("Üs almak için önce klan kur! (KLAN)")
                    } else if (b.spawned && alive[b.id] == 0) {
                        b.cap += dt / 4f
                        if (b.cap >= 1f) {
                            b.owner = 0; b.cap = 0f; b.spawned = false
                            guards.removeAll { it.base == b.id && !it.attacker }
                            addXp(40 * b.level)
                            say("Üs #${b.id + 1} ele geçirildi! +${40 * b.level} XP")
                        }
                    } else {
                        b.cap = max(0f, b.cap - dt / 2f)
                    }
                } else {
                    b.cap = max(0f, b.cap - dt / 2f)
                }
            } else if (d < BASE_R) {
                hp = min(maxHp, hp + 6f * dt)
            }
        }
    }

    private fun globalTimers(dt: Float) {
        // üs geliri
        incomeTimer -= dt
        if (incomeTimer <= 0f) {
            incomeTimer = 10f
            for (b in bases) if (b.owner == 0) res[Random.nextInt(3)] += b.level
        }

        // NPC klanlar birbirleriyle savaşır
        warTimer -= dt
        if (warTimer <= 0f) {
            warTimer = 7f
            val a = bases[Random.nextInt(bases.size)]
            if (a.owner != 0) {
                val cand = bases.filter {
                    it.owner != 0 && it.owner != a.owner && !it.spawned && hypot(it.x - a.x, it.y - a.y) < 800f
                }
                if (cand.isNotEmpty()) cand.random().owner = a.owner
            }
        }

        // oyuncunun üslerine saldırı
        attackEvtTimer -= dt
        if (attackEvtTimer <= 0f) {
            attackEvtTimer = 50f + Random.nextFloat() * 40f
            val mine = bases.filter { it.owner == 0 && it.attackTimer <= 0f }
            if (mine.isNotEmpty()) {
                val b = mine.random()
                b.attackTimer = 50f
                b.attackClan = 1 + Random.nextInt(7)
                b.attackersSpawned = false
                say("${CLAN_NAMES[b.attackClan]} Üs #${b.id + 1}'e saldırıyor! (50 sn)")
            }
        }
        for (b in bases) {
            if (b.attackTimer <= 0f) continue
            b.attackTimer -= dt
            if (zone == 1 && !b.attackersSpawned) { spawnAttackers(b); b.attackersSpawned = true }
            if (zone == 1 && b.attackersSpawned && attAlive[b.id] == 0) {
                b.attackTimer = 0f; b.attackersSpawned = false
                addXp(40 + 10 * b.level)
                say("Üs #${b.id + 1} savunuldu! +${40 + 10 * b.level} XP")
            } else if (b.attackTimer <= 0f) {
                b.attackTimer = 0f
                b.owner = b.attackClan
                b.attackersSpawned = false; b.spawned = false; b.cap = 0f
                guards.removeAll { it.base == b.id && it.attacker }
                say("Üs #${b.id + 1} kaybedildi: ${CLAN_NAMES[b.owner]} aldı")
            }
        }
    }

    // ---------- arayüz alanları ----------
    private fun topBtn(i: Int) = RectF(w - 180f, 10f + i * 62f, w - 10f, 64f + i * 62f)
    private fun panel() = RectF(w * 0.12f, 90f, w * 0.88f, h - 20f)
    private fun rowCount() = if (menuMode == 3) 6 else 3
    private fun rowRect(i: Int): RectF {
        val p = panel()
        val rh = min(76f, (p.height() - 70f) / rowCount())
        val top = p.top + 60f + i * rh
        return RectF(p.left + 12f, top, p.right - 12f, top + rh - 8f)
    }
    private fun nearBoard() = zone == 0 && hypot(px - BX, py - BY) < BOARD_R + 40f
    private fun questBtn() = RectF(w / 2 - 90f, h - 76f, w / 2 + 90f, h - 12f)
    private fun medBtn() = RectF(w / 2 - 260f, h - 76f, w / 2 - 100f, h - 12f)

    // ---------- çizim ----------
    private fun drawBtn(c: Canvas, r: RectF, label: String, bg: Int) {
        paint.style = Paint.Style.FILL
        paint.color = bg
        c.drawRoundRect(r, 12f, 12f, paint)
        paint.color = Color.WHITE
        paint.textSize = 28f
        paint.textAlign = Paint.Align.CENTER
        c.drawText(label, r.centerX(), r.centerY() + 10f, paint)
        paint.textAlign = Paint.Align.LEFT
    }

    private fun costText(c: IntArray): String {
        val sb = StringBuilder()
        for (k in 0..2) if (c[k] > 0) sb.append(RES_NAMES[k]).append(' ').append(c[k]).append("  ")
        return sb.toString().trim()
    }

    private fun clanLabel(i: Int) = if (i == 0) clanName else CLAN_NAMES[i]

    private fun draw(c: Canvas) {
        c.drawColor(if (zone == 0) Color.rgb(28, 40, 28) else Color.rgb(46, 40, 30))
        c.save()
        c.translate(-camX, -camY)

        // ızgara
        paint.style = Paint.Style.STROKE
        paint.strokeWidth = 2f
        paint.color = Color.argb(40, 255, 255, 255)
        var gx = floor(camX / 200f) * 200f
        while (gx <= camX + w) { c.drawLine(gx, camY, gx, camY + h, paint); gx += 200f }
        var gy = floor(camY / 200f) * 200f
        while (gy <= camY + h) { c.drawLine(camX, gy, camX + w, gy, paint); gy += 200f }
        paint.strokeWidth = 8f
        paint.color = Color.RED
        c.drawRect(0f, 0f, worldW, worldH, paint)

        if (zone == 0) {
            // görev panosu
            paint.style = Paint.Style.FILL
            paint.color = Color.argb(35, 255, 255, 255)
            c.drawCircle(BX, BY, BOARD_R, paint)
            paint.style = Paint.Style.STROKE
            paint.strokeWidth = 4f
            paint.color = Color.argb(160, 255, 255, 255)
            c.drawCircle(BX, BY, BOARD_R, paint)
            paint.style = Paint.Style.FILL
            paint.color = Color.rgb(120, 80, 40)
            c.drawRect(BX - 40f, BY - 30f, BX + 40f, BY + 20f, paint)
            paint.color = Color.WHITE
            paint.textSize = 22f
            paint.textAlign = Paint.Align.CENTER
            c.drawText("GÖREV", BX, BY + 6f, paint)
            paint.textAlign = Paint.Align.LEFT
        } else {
            for (b in bases) {
                if (b.x < camX - 250f || b.x > camX + w + 250f || b.y < camY - 250f || b.y > camY + h + 250f) continue
                val col = CLAN_COLORS[b.owner]
                paint.style = Paint.Style.FILL
                paint.color = Color.argb(35, Color.red(col), Color.green(col), Color.blue(col))
                c.drawCircle(b.x, b.y, BASE_R, paint)
                paint.style = Paint.Style.STROKE
                paint.strokeWidth = if (b.attackTimer > 0f) 8f else 3f
                paint.color = if (b.attackTimer > 0f) Color.RED else col
                c.drawCircle(b.x, b.y, BASE_R, paint)
                paint.style = Paint.Style.FILL
                paint.color = col
                c.drawRect(b.x - 22f, b.y - 22f, b.x + 22f, b.y + 22f, paint)
                paint.color = Color.WHITE
                paint.textAlign = Paint.Align.CENTER
                paint.textSize = 24f
                c.drawText("#${b.id + 1} Sv${b.level}", b.x, b.y - 32f, paint)
                paint.textSize = 20f
                c.drawText(clanLabel(b.owner), b.x, b.y + 46f, paint)
                paint.textAlign = Paint.Align.LEFT
                if (b.cap > 0f) {
                    paint.color = Color.DKGRAY
                    c.drawRect(b.x - 40f, b.y + 54f, b.x + 40f, b.y + 64f, paint)
                    paint.color = Color.GREEN
                    c.drawRect(b.x - 40f, b.y + 54f, b.x - 40f + 80f * b.cap, b.y + 64f, paint)
                }
            }
        }

        paint.style = Paint.Style.FILL
        for (p in pickups) {
            paint.color = when (p.type) {
                0 -> Color.rgb(160, 100, 50)
                1 -> Color.rgb(180, 180, 180)
                else -> Color.rgb(90, 200, 230)
            }
            c.drawRect(p.x - 7f, p.y - 7f, p.x + 7f, p.y + 7f, paint)
        }
        for (z in zombies) {
            paint.color = if (z.big) Color.rgb(60, 110, 50) else Color.rgb(90, 160, 70)
            c.drawCircle(z.x, z.y, z.r, paint)
            paint.color = Color.RED
            c.drawCircle(z.x - 6f, z.y - 4f, 3f, paint)
            c.drawCircle(z.x + 6f, z.y - 4f, 3f, paint)
        }
        for (g in guards) {
            paint.color = CLAN_COLORS[g.clan]
            c.drawCircle(g.x, g.y, 16f, paint)
            paint.color = if (g.attacker) Color.RED else Color.WHITE
            c.drawCircle(g.x, g.y, 5f, paint)
        }
        paint.color = Color.YELLOW
        for (b in bullets) c.drawCircle(b.x, b.y, 4f, paint)

        // oyuncu
        paint.color = CLAN_COLORS[0]
        c.drawCircle(px, py, 16f, paint)
        paint.color = Color.LTGRAY
        paint.strokeWidth = 6f
        c.drawLine(px, py, px + cos(angle) * 28f, py + sin(angle) * 28f, paint)
        c.restore()

        // joystick
        if (moveId != -1) {
            paint.style = Paint.Style.STROKE
            paint.strokeWidth = 3f
            paint.color = Color.argb(120, 255, 255, 255)
            c.drawCircle(moveCx, moveCy, 110f, paint)
            paint.style = Paint.Style.FILL
            val dx = moveX - moveCx
            val dy = moveY - moveCy
            val d = max(hypot(dx, dy), 0.001f)
            val k = min(d, 110f) / d
            c.drawCircle(moveCx + dx * k, moveCy + dy * k, 36f, paint)
        }

        // HUD
        paint.style = Paint.Style.FILL
        paint.color = Color.WHITE
        paint.textSize = 32f
        c.drawText("Sv $level   Öldürme: $kills", 24f, 40f, paint)
        paint.color = Color.DKGRAY
        c.drawRect(24f, 52f, 264f, 72f, paint)
        paint.color = Color.rgb(220, 50, 50)
        c.drawRect(24f, 52f, 24f + 240f * (hp / maxHp), 72f, paint)
        paint.color = Color.DKGRAY
        c.drawRect(24f, 78f, 264f, 90f, paint)
        paint.color = Color.rgb(160, 90, 230)
        c.drawRect(24f, 78f, 24f + 240f * (xp.toFloat() / xpNeed()), 90f, paint)
        paint.color = Color.WHITE
        paint.textSize = 28f
        c.drawText("Odun ${res[0]}   Taş ${res[1]}   Metal ${res[2]}", 24f, 124f, paint)
        val q = active
        if (q != null) {
            paint.textSize = 24f
            paint.color = Color.YELLOW
            c.drawText("Görev: ${questTitle(q)}  (${q.prog}/${q.target})", 24f, 156f, paint)
        }
        val atk = bases.firstOrNull { it.attackTimer > 0f }
        if (atk != null) {
            paint.textSize = 24f
            paint.color = Color.rgb(255, 90, 90)
            c.drawText("SALDIRI: Üs #${atk.id + 1}  ${atk.attackTimer.toInt()} sn", 24f, 186f, paint)
        }

        // mini harita
        if (zone == 1) {
            val mx = 24f; val my = 200f; val mw = 216f; val mh = 120f
            paint.color = Color.argb(140, 0, 0, 0)
            c.drawRect(mx, my, mx + mw, my + mh, paint)
            for (b in bases) {
                paint.color = CLAN_COLORS[b.owner]
                c.drawCircle(mx + b.x / worldW * mw, my + b.y / worldH * mh, if (b.attackTimer > 0f) 5f else 3f, paint)
            }
            paint.color = Color.WHITE
            c.drawCircle(mx + px / worldW * mw, my + py / worldH * mh, 4f, paint)
        }

        // bölge etiketi + mesaj
        paint.textAlign = Paint.Align.CENTER
        paint.color = Color.argb(170, 255, 255, 255)
        paint.textSize = 24f
        c.drawText(if (zone == 0) "Zombi Bölgesi" else "Üs Bölgesi", w / 2, 28f, paint)
        if (msgTimer > 0f) {
            paint.color = Color.YELLOW
            paint.textSize = 30f
            c.drawText(msg, w / 2, 70f, paint)
        }
        paint.textAlign = Paint.Align.LEFT

        // butonlar
        drawBtn(c, topBtn(0), "ÜRET", Color.rgb(60, 90, 160))
        drawBtn(c, topBtn(1), "KLAN", Color.rgb(120, 70, 150))
        drawBtn(c, topBtn(2), if (zone == 0) "ÜSLER" else "ZOMBİ", Color.rgb(150, 90, 40))
        if (medkits > 0) drawBtn(c, medBtn(), "Medkit x$medkits", Color.rgb(160, 50, 50))
        if (nearBoard() && menuMode == 0) drawBtn(c, questBtn(), "GÖREV", Color.rgb(40, 110, 50))

        if (menuMode != 0) drawMenu(c)

        if (dead) {
            paint.style = Paint.Style.FILL
            paint.color = Color.argb(170, 0, 0, 0)
            c.drawRect(0f, 0f, w, h, paint)
            paint.color = Color.WHITE
            paint.textSize = 72f
            paint.textAlign = Paint.Align.CENTER
            c.drawText("ÖLDÜN", w / 2, h / 2 - 20f, paint)
            paint.textSize = 36f
            c.drawText("Dokun: yeniden doğ (kaynakların yarısı gider)", w / 2, h / 2 + 50f, paint)
            paint.textAlign = Paint.Align.LEFT
        }
    }

    private fun drawMenu(c: Canvas) {
        val p = panel()
        paint.style = Paint.Style.FILL
        paint.color = Color.argb(235, 20, 20, 30)
        c.drawRoundRect(p, 16f, 16f, paint)
        paint.color = Color.WHITE
        paint.textSize = 34f
        c.drawText(
            when (menuMode) { 1 -> "Üretim (oyun durdu)"; 2 -> "Görev Panosu"; else -> "Klan" },
            p.left + 20f, p.top + 42f, paint
        )
        if (menuMode == 2) {
            val a = active
            paint.textSize = 22f
            paint.textAlign = Paint.Align.RIGHT
            paint.color = Color.YELLOW
            c.drawText(
                if (a != null) "Aktif: ${questTitle(a)} (${a.prog}/${a.target})" else "Aktif görev yok",
                p.right - 20f, p.top + 40f, paint
            )
            paint.textAlign = Paint.Align.LEFT
        }

        val counts = IntArray(8)
        for (b in bases) counts[b.owner]++
        val order = (0..7).filter { it != 0 || hasClan }.sortedByDescending { counts[it] }

        for (i in 0 until rowCount()) {
            val r = rowRect(i)
            var left = ""
            var right = ""
            var bg = Color.rgb(55, 55, 60)
            when (menuMode) {
                1 -> {
                    val cs = cost(i)
                    left = RECIPES[i] + when (i) { 0 -> " (Sv${weaponLvl + 1})"; 1 -> " (Sv${armorLvl + 1})"; else -> "" }
                    right = costText(cs)
                    if (affordable(cs)) bg = Color.rgb(40, 110, 50)
                }
                2 -> {
                    val o = offers.getOrNull(i)
                    if (o != null) {
                        left = questTitle(o)
                        right = "XP ${o.rewardXp} + Metal ${o.rewardRes}"
                        bg = Color.rgb(40, 110, 50)
                    }
                }
                else -> {
                    if (i == 0) {
                        if (hasClan) {
                            var inc = 0
                            for (b in bases) if (b.owner == 0) inc += b.level
                            left = clanName
                            right = "Üs: ${counts[0]}/50  Gelir: +$inc/10sn"
                            bg = Color.rgb(40, 70, 130)
                        } else {
                            left = "Klan Kur"
                            right = costText(clanCost)
                            if (affordable(clanCost)) bg = Color.rgb(40, 110, 50)
                        }
                    } else if (i - 1 < order.size) {
                        val cl = order[i - 1]
                        left = "$i. ${clanLabel(cl)}"
                        right = "${counts[cl]} üs"
                        bg = Color.rgb(35, 35, 45)
                    }
                }
            }
            paint.color = bg
            c.drawRoundRect(r, 10f, 10f, paint)
            if (menuMode == 3 && i > 0 && i - 1 < order.size) {
                paint.color = CLAN_COLORS[order[i - 1]]
                c.drawRect(r.left + 6f, r.top + 8f, r.left + 16f, r.bottom - 8f, paint)
            }
            paint.color = Color.WHITE
            paint.textSize = 26f
            c.drawText(left, r.left + 26f, r.centerY() + 9f, paint)
            paint.textAlign = Paint.Align.RIGHT
            c.drawText(right, r.right - 16f, r.centerY() + 9f, paint)
            paint.textAlign = Paint.Align.LEFT
        }
    }

    // ---------- dokunma ----------
    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.actionMasked) {
            MotionEvent.ACTION_DOWN, MotionEvent.ACTION_POINTER_DOWN -> {
                val i = e.actionIndex
                val id = e.getPointerId(i)
                val x = e.getX(i)
                val y = e.getY(i)
                if (dead) { actions.add { respawn() }; return true }

                if (topBtn(0).contains(x, y)) {
                    menuMode = if (menuMode == 1) 0 else 1; moveId = -1; aimId = -1; return true
                }
                if (topBtn(1).contains(x, y)) {
                    menuMode = if (menuMode == 3) 0 else 3; moveId = -1; aimId = -1; return true
                }
                if (topBtn(2).contains(x, y)) { actions.add { switchZone() }; return true }

                if (menuMode != 0) {
                    for (r in 0 until rowCount()) {
                        if (!rowRect(r).contains(x, y)) continue
                        val k = r
                        when (menuMode) {
                            1 -> actions.add { craft(k) }
                            2 -> actions.add {
                                val o = offers.getOrNull(k)
                                if (o != null) {
                                    active = Quest(o.type, o.target, o.resType, o.rewardXp, o.rewardRes, o.rewardResType)
                                    genOffers()
                                    menuMode = 0
                                    say("Görev alındı")
                                }
                            }
                            else -> if (k == 0 && !hasClan && affordable(clanCost)) askClanName()
                        }
                    }
                    return true
                }
                if (medkits > 0 && medBtn().contains(x, y)) { actions.add { useMedkit() }; return true }
                if (nearBoard() && questBtn().contains(x, y)) {
                    menuMode = 2; moveId = -1; aimId = -1; return true
                }

                if (x < w / 2 && moveId == -1) {
                    moveId = id; moveCx = x; moveCy = y; moveX = x; moveY = y
                } else if (x >= w / 2 && aimId == -1) {
                    aimId = id; aimX = x; aimY = y
                }
            }
            MotionEvent.ACTION_MOVE -> {
                for (i in 0 until e.pointerCount) {
                    val id = e.getPointerId(i)
                    if (id == moveId) { moveX = e.getX(i); moveY = e.getY(i) }
                    if (id == aimId) { aimX = e.getX(i); aimY = e.getY(i) }
                }
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_POINTER_UP -> {
                val id = e.getPointerId(e.actionIndex)
                if (id == moveId) moveId = -1
                if (id == aimId) aimId = -1
            }
            MotionEvent.ACTION_CANCEL -> { moveId = -1; aimId = -1 }
        }
        return true
    }
}
