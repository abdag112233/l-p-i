package me.mahdi18.pixeladmin.managers;

import com.destroystokyo.paper.event.server.AsyncTabCompleteEvent;
import io.papermc.paper.event.player.AsyncChatEvent;
import io.papermc.paper.event.player.PlayerTrackEntityEvent;
import me.mahdi18.pixeladmin.PixelAdmin;
import net.kyori.adventure.audience.Audience;
import net.kyori.adventure.text.Component;
import net.kyori.adventure.text.format.NamedTextColor;
import org.bukkit.Bukkit;
import org.bukkit.Location;
import org.bukkit.OfflinePlayer;
import org.bukkit.ScoreboardManager;
import org.bukkit.World;
import org.bukkit.command.CommandSender;
import org.bukkit.configuration.file.YamlConfiguration;
import org.bukkit.entity.Entity;
import org.bukkit.entity.LivingEntity;
import org.bukkit.entity.Mob;
import org.bukkit.entity.Player;
import org.bukkit.event.EventHandler;
import org.bukkit.event.EventPriority;
import org.bukkit.event.Listener;
import org.bukkit.event.entity.EntityDamageByEntityEvent;
import org.bukkit.event.entity.EntityPickupItemEvent;
import org.bukkit.event.entity.EntityTargetLivingEntityEvent;
import org.bukkit.event.entity.PlayerDeathEvent;
import org.bukkit.event.player.PlayerAttemptPickupItemEvent;
import org.bukkit.event.player.PlayerChangedWorldEvent;
import org.bukkit.event.player.PlayerCommandPreprocessEvent;
import org.bukkit.event.player.PlayerCommandSendEvent;
import org.bukkit.event.player.PlayerDropItemEvent;
import org.bukkit.event.player.PlayerInteractEntityEvent;
import org.bukkit.event.player.PlayerJoinEvent;
import org.bukkit.event.player.PlayerKickEvent;
import org.bukkit.event.player.PlayerLocaleChangeEvent;
import org.bukkit.event.player.PlayerPickupExperienceEvent;
import org.bukkit.event.player.PlayerQuitEvent;
import org.bukkit.event.player.PlayerRespawnEvent;
import org.bukkit.event.player.PlayerTeleportEvent;
import org.bukkit.event.server.PluginDisableEvent;
import org.bukkit.event.server.PluginEnableEvent;
import org.bukkit.event.server.TabCompleteEvent;
import org.bukkit.metadata.FixedMetadataValue;
import org.bukkit.plugin.Plugin;
import org.bukkit.scheduler.BukkitTask;
import org.bukkit.scoreboard.Scoreboard;
import org.bukkit.scoreboard.Team;

import java.io.File;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Consumer;
import java.util.logging.Level;
import java.util.regex.Pattern;

public final class VanishManager implements Listener {

    private static final String PIXELADMIN_SEE_PERMISSION = "pixeladmin.vanish.see";
    private static final String TAB_SEE_PERMISSION = "tab.seevanished";
    private static final String VANISH_METADATA = "vanished";
    private static final String VANISH_TEAM_NAME = "pa_vanish";
    private static final String TAB_PLUGIN_NAME = "TAB";
    private static final String STORAGE_FILE_NAME = "vanished-players.yml";
    private static final String STORAGE_KEY = "vanished";

    private static final String VANISH_ENABLED_AR = "أنت الآن مختفٍ عن الأنظار";
    private static final String VANISH_ENABLED_EN = "You are now vanished";
    private static final String VANISH_DISABLED_AR = "أنت الآن ظاهر للآخرين";
    private static final String VANISH_DISABLED_EN = "You are now visible";

    private static final String JOIN_AR = " انضم إلى اللعبة";
    private static final String JOIN_EN = " joined the game";
    private static final String QUIT_AR = " غادر اللعبة";
    private static final String QUIT_EN = " left the game";

    private static final String COMMAND_TARGET_NOT_FOUND_AR = "هذا اللاعب غير موجود";
    private static final String COMMAND_TARGET_NOT_FOUND_EN = "That player could not be found";

    private static final long FIRST_REFRESH_DELAY_TICKS = 1L;
    private static final long SECOND_REFRESH_DELAY_TICKS = 5L;
    private static final long SAVE_DEBOUNCE_TICKS = 40L;
    private static final int REFRESH_BATCH_SIZE = 96;
    private static final double TARGET_CLEAR_RADIUS = 128.0D;

    private static final boolean PERSIST_VANISH_ACROSS_RESTARTS = true;
    private static final boolean USE_PAPER_PLAYER_LIST_API = true;
    private static final boolean CHECK_TAB_SEE_PERMISSION_AS_FALLBACK = true;
    private static final boolean BLOCK_ITEM_PICKUP = true;
    private static final boolean BLOCK_EXPERIENCE_PICKUP = true;
    private static final boolean BLOCK_ITEM_DROPS_WHILE_VANISHED = true;
    private static final boolean BLOCK_NON_STAFF_INTERACTION_WITH_VANISHED = true;
    private static final boolean BLOCK_NON_STAFF_DAMAGE_TO_VANISHED = true;
    private static final boolean HIDE_VANISHED_CHAT_FROM_NON_STAFF = true;
    private static final boolean FILTER_VANISHED_NAMES_FROM_COMMANDS = true;
    private static final boolean SILENCE_VANISHED_DEATH_MESSAGES = true;

    private final PixelAdmin plugin;
    private final File storageFile;
    private final Set<UUID> vanishedPlayers = ConcurrentHashMap.newKeySet();
    private final Set<UUID> pendingVanishedRefreshes = ConcurrentHashMap.newKeySet();
    private final Set<UUID> pendingViewerRefreshes = ConcurrentHashMap.newKeySet();
    private final Map<UUID, Set<UUID>> playerListUnlistedByPixelAdmin = new ConcurrentHashMap<>();
    private final Map<UUID, Boolean> previousCollidableStates = new ConcurrentHashMap<>();
    private final Map<UUID, Boolean> previousSleepingIgnoredStates = new ConcurrentHashMap<>();
    private final Map<UUID, Boolean> canSeeVanishedCache = new ConcurrentHashMap<>();
    private final Map<UUID, String> knownPlayerNames = new ConcurrentHashMap<>();
    private final Map<UUID, String> knownLowercaseNames = new ConcurrentHashMap<>();

    private BukkitTask refreshTask;
    private BukkitTask saveTask;
    private TabBridge tabBridge = TabBridge.noop();
    private boolean shuttingDown;

    public VanishManager(PixelAdmin plugin) {
        this.plugin = Objects.requireNonNull(plugin, "plugin");
        this.storageFile = new File(plugin.getDataFolder(), STORAGE_FILE_NAME);

        loadVanishedPlayers();
        Bukkit.getPluginManager().registerEvents(this, plugin);
        connectTabBridgeIfPossible();
        configureAllKnownVanishTeams();
        refreshAll();
    }

    public void toggleVanish(Player player) {
        Objects.requireNonNull(player, "player");

        if (runSyncIfNeeded(() -> toggleVanish(player))) {
            return;
        }

        if (isVanished(player)) {
            unVanish(player);
            return;
        }

        vanish(player);
    }

    public void vanish(Player player) {
        Objects.requireNonNull(player, "player");

        if (runSyncIfNeeded(() -> vanish(player))) {
            return;
        }

        UUID uuid = player.getUniqueId();
        boolean changed = vanishedPlayers.add(uuid);

        rememberPlayer(player);
        applyVanishedState(player);
        queueVanishRefresh(uuid);
        scheduleDelayedVanishRefresh(uuid);

        if (changed) {
            requestSave();
            broadcastLocalizedVanishQuit(player);
            sendLocalized(player, VANISH_ENABLED_AR, VANISH_ENABLED_EN);
            logInfo(player.getName() + " (" + uuid + ") vanished and was announced as having left the game.");
        }
    }

    public void unVanish(Player player) {
        Objects.requireNonNull(player, "player");

        if (runSyncIfNeeded(() -> unVanish(player))) {
            return;
        }

        UUID uuid = player.getUniqueId();
        boolean changed = vanishedPlayers.remove(uuid);

        rememberPlayer(player);
        clearVanishedState(player, true);
        revealPlayerToEveryone(player);
        clearTrackedListState(player);

        if (changed) {
            requestSave();
            broadcastLocalizedVanishJoin(player);
            sendLocalized(player, VANISH_DISABLED_AR, VANISH_DISABLED_EN);
            logInfo(player.getName() + " (" + uuid + ") unvanished and was announced as having joined the game.");
        }
    }

    public boolean isVanished(Player player) {
        return player != null && isVanished(player.getUniqueId());
    }

    public boolean isVanished(UUID uuid) {
        return uuid != null && vanishedPlayers.contains(uuid);
    }

    public Set<UUID> getVanishedPlayers() {
        return Set.copyOf(vanishedPlayers);
    }

    public boolean canSeeVanished(Player player) {
        if (player == null) {
            return false;
        }

        return evaluateCanSeeVanished(player);
    }

    public void refreshAll() {
        if (runSyncIfNeeded(this::refreshAll)) {
            return;
        }

        removeOfflineEntriesFromScoreboards();
        cleanupOfflineListTracking();

        for (Player player : Bukkit.getOnlinePlayers()) {
            rememberPlayer(player);

            if (isVanished(player)) {
                applyVanishedState(player);
            }
        }

        for (Player viewer : Bukkit.getOnlinePlayers()) {
            refreshVisibilityForViewer(viewer);
        }

        tabBridge.refreshAll(Bukkit.getOnlinePlayers(), snapshotVanishedPlayers());
    }

    public void refreshPlayer(Player player) {
        Objects.requireNonNull(player, "player");

        if (runSyncIfNeeded(() -> refreshPlayer(player))) {
            return;
        }

        rememberPlayer(player);
        refreshVisibilityForViewer(player);

        if (isVanished(player)) {
            applyVanishedState(player);
            refreshVisibilityForVanishedPlayer(player);
        }
    }

    public void shutdown() {
        if (!Bukkit.isPrimaryThread() && plugin.isEnabled()) {
            Bukkit.getScheduler().runTask(plugin, this::shutdown);
            return;
        }

        shuttingDown = true;
        cancelRefreshTask();
        cancelSaveTask();
        saveVanishedPlayersNow();

        List<Player> onlineVanishedPlayers = getOnlineVanishedPlayers();

        for (Player vanished : onlineVanishedPlayers) {
            clearVanishedState(vanished, true);
        }

        for (Player vanished : onlineVanishedPlayers) {
            revealPlayerToEveryone(vanished);
            clearTrackedListState(vanished);
        }

        tabBridge.close();
        unregisterEmptyVanishTeams();

        pendingVanishedRefreshes.clear();
        pendingViewerRefreshes.clear();
        playerListUnlistedByPixelAdmin.clear();
        previousCollidableStates.clear();
        previousSleepingIgnoredStates.clear();
        canSeeVanishedCache.clear();
    }

    @EventHandler(priority = EventPriority.HIGHEST)
    public void onPlayerJoin(PlayerJoinEvent event) {
        Player player = event.getPlayer();

        event.joinMessage(null);
        rememberPlayer(player);
        refreshVisibilityForViewer(player);

        if (isVanished(player)) {
            applyVanishedState(player);
            refreshVisibilityForVanishedPlayer(player);
            scheduleDelayedVanishRefresh(player.getUniqueId());
            logInfo(player.getName() + " (" + player.getUniqueId() + ") joined silently while vanished.");
            return;
        }

        queueViewerRefresh(player.getUniqueId());
        scheduleDelayedViewerRefresh(player.getUniqueId());
        broadcastLocalizedJoin(player);
        logInfo(player.getName() + " (" + player.getUniqueId() + ") joined the game.");
    }

    @EventHandler(priority = EventPriority.HIGHEST)
    public void onPlayerQuit(PlayerQuitEvent event) {
        Player player = event.getPlayer();

        event.quitMessage(null);
        rememberPlayer(player);

        if (isVanished(player)) {
            clearVanishedState(player, false);
            clearTrackedListState(player);
            canSeeVanishedCache.remove(player.getUniqueId());
            logInfo(player.getName() + " (" + player.getUniqueId() + ") quit silently while vanished.");
            return;
        }

        broadcastLocalizedQuit(player, false);
        canSeeVanishedCache.remove(player.getUniqueId());
        logInfo(player.getName() + " (" + player.getUniqueId() + ") left the game.");
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerKick(PlayerKickEvent event) {
        Player player = event.getPlayer();

        if (!isVanished(player)) {
            return;
        }

        event.leaveMessage(null);
        logInfo(player.getName() + " (" + player.getUniqueId() + ") was kicked silently while vanished.");
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerDeath(PlayerDeathEvent event) {
        Player player = event.getPlayer();

        if (!SILENCE_VANISHED_DEATH_MESSAGES || !isVanished(player)) {
            return;
        }

        event.deathMessage(null);
        logInfo(player.getName() + " (" + player.getUniqueId() + ") died silently while vanished.");
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onEntityTarget(EntityTargetLivingEntityEvent event) {
        LivingEntity target = event.getTarget();

        if (target instanceof Player player && isVanished(player)) {
            event.setCancelled(true);
            event.setTarget(null);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onEntityPickupItem(EntityPickupItemEvent event) {
        if (!BLOCK_ITEM_PICKUP) {
            return;
        }

        Entity entity = event.getEntity();

        if (entity instanceof Player player && isVanished(player)) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerAttemptPickupItem(PlayerAttemptPickupItemEvent event) {
        if (!BLOCK_ITEM_PICKUP) {
            return;
        }

        if (isVanished(event.getPlayer())) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerPickupExperience(PlayerPickupExperienceEvent event) {
        if (!BLOCK_EXPERIENCE_PICKUP) {
            return;
        }

        if (isVanished(event.getPlayer())) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerDropItem(PlayerDropItemEvent event) {
        if (!BLOCK_ITEM_DROPS_WHILE_VANISHED) {
            return;
        }

        if (isVanished(event.getPlayer())) {
            event.setCancelled(true);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerInteractEntity(PlayerInteractEntityEvent event) {
        if (!BLOCK_NON_STAFF_INTERACTION_WITH_VANISHED) {
            return;
        }

        if (!(event.getRightClicked() instanceof Player target)) {
            return;
        }

        Player viewer = event.getPlayer();

        if (isVanished(target) && !viewer.equals(target) && !canSeeVanished(viewer)) {
            event.setCancelled(true);
            updateVisibility(viewer, target);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onEntityDamageByEntity(EntityDamageByEntityEvent event) {
        if (!BLOCK_NON_STAFF_DAMAGE_TO_VANISHED) {
            return;
        }

        if (!(event.getEntity() instanceof Player target) || !isVanished(target)) {
            return;
        }

        Optional<Player> attacker = findAttackingPlayer(event.getDamager());

        if (attacker.isPresent() && !attacker.get().equals(target) && !canSeeVanished(attacker.get())) {
            event.setCancelled(true);
            updateVisibility(attacker.get(), target);
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerTrackEntity(PlayerTrackEntityEvent event) {
        Entity entity = event.getEntity();

        if (!(entity instanceof Player vanished) || !isVanished(vanished)) {
            return;
        }

        Player viewer = event.getPlayer();

        if (!viewer.equals(vanished) && !canSeeVanished(viewer)) {
            event.setCancelled(true);
            queueViewerRefresh(viewer.getUniqueId());
        }
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onAsyncChat(AsyncChatEvent event) {
        if (!HIDE_VANISHED_CHAT_FROM_NON_STAFF) {
            return;
        }

        Player sender = event.getPlayer();

        if (!isVanished(sender)) {
            return;
        }

        event.viewers().removeIf(audience -> shouldHideVanishedChatFromAsync(audience, sender));
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onTabComplete(TabCompleteEvent event) {
        if (!FILTER_VANISHED_NAMES_FROM_COMMANDS) {
            return;
        }

        CommandSender sender = event.getSender();

        if (sender instanceof Player player && canSeeVanished(player)) {
            return;
        }

        removeVanishedNameCompletions(event.getCompletions());
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onAsyncTabComplete(AsyncTabCompleteEvent event) {
        if (!FILTER_VANISHED_NAMES_FROM_COMMANDS) {
            return;
        }

        CommandSender sender = event.getSender();

        if (sender instanceof Player player && cachedCanSeeVanished(player)) {
            return;
        }

        removeVanishedNameCompletions(event.getCompletions(), true);
    }

    @EventHandler(priority = EventPriority.HIGHEST)
    public void onPlayerCommandSend(PlayerCommandSendEvent event) {
        if (!FILTER_VANISHED_NAMES_FROM_COMMANDS || canSeeVanished(event.getPlayer())) {
            return;
        }

        removeVanishedNameCompletions(event.getCommands());
    }

    @EventHandler(priority = EventPriority.HIGHEST, ignoreCancelled = true)
    public void onPlayerCommandPreprocess(PlayerCommandPreprocessEvent event) {
        if (!FILTER_VANISHED_NAMES_FROM_COMMANDS || canSeeVanished(event.getPlayer())) {
            return;
        }

        if (commandMentionsVanishedPlayer(event.getMessage())) {
            event.setCancelled(true);
            sendLocalized(event.getPlayer(), COMMAND_TARGET_NOT_FOUND_AR, COMMAND_TARGET_NOT_FOUND_EN);
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerChangedWorld(PlayerChangedWorldEvent event) {
        Player player = event.getPlayer();

        rememberPlayer(player);
        queueViewerRefresh(player.getUniqueId());

        if (isVanished(player)) {
            queueVanishRefresh(player.getUniqueId());
            scheduleDelayedVanishRefresh(player.getUniqueId());
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerRespawn(PlayerRespawnEvent event) {
        Player player = event.getPlayer();

        rememberPlayer(player);
        queueViewerRefresh(player.getUniqueId());

        if (isVanished(player)) {
            queueVanishRefresh(player.getUniqueId());
            scheduleDelayedVanishRefresh(player.getUniqueId());
        }
    }

    @EventHandler(priority = EventPriority.MONITOR, ignoreCancelled = true)
    public void onPlayerTeleport(PlayerTeleportEvent event) {
        Player player = event.getPlayer();

        rememberPlayer(player);
        queueViewerRefresh(player.getUniqueId());

        if (isVanished(player)) {
            queueVanishRefresh(player.getUniqueId());
            scheduleDelayedVanishRefresh(player.getUniqueId());
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPlayerLocaleChange(PlayerLocaleChangeEvent event) {
        rememberPlayer(event.getPlayer());
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPluginEnable(PluginEnableEvent event) {
        if (isTabPlugin(event.getPlugin())) {
            connectTabBridgeIfPossible();
            queueFullRefresh();
        }
    }

    @EventHandler(priority = EventPriority.MONITOR)
    public void onPluginDisable(PluginDisableEvent event) {
        Plugin disabled = event.getPlugin();

        if (disabled.equals(plugin)) {
            shutdown();
            return;
        }

        if (isTabPlugin(disabled)) {
            tabBridge.close();
            tabBridge = TabBridge.noop();
        }
    }

    private void applyVanishedState(Player player) {
        player.setMetadata(VANISH_METADATA, new FixedMetadataValue(plugin, true));
        rememberPlayer(player);
        applyGameplayProtections(player);
        applyNameTagFallback(player);
        clearCurrentMobTargets(player);
        tabBridge.applyVanish(player, Bukkit.getOnlinePlayers(), this::canSeeVanished);
    }

    private void clearVanishedState(Player player, boolean restoreGameplayState) {
        player.removeMetadata(VANISH_METADATA, plugin);
        clearNameTagFallback(player);
        tabBridge.reveal(player, Bukkit.getOnlinePlayers());

        if (restoreGameplayState) {
            restoreGameplayProtections(player);
        } else {
            previousCollidableStates.remove(player.getUniqueId());
            previousSleepingIgnoredStates.remove(player.getUniqueId());
        }
    }

    private void applyGameplayProtections(Player player) {
        UUID uuid = player.getUniqueId();

        previousCollidableStates.putIfAbsent(uuid, player.isCollidable());
        previousSleepingIgnoredStates.putIfAbsent(uuid, player.isSleepingIgnored());

        player.setCollidable(false);
        player.setSleepingIgnored(true);
    }

    private void restoreGameplayProtections(Player player) {
        UUID uuid = player.getUniqueId();

        Boolean previousCollidable = previousCollidableStates.remove(uuid);
        if (previousCollidable != null) {
            player.setCollidable(previousCollidable);
        }

        Boolean previousSleepingIgnored = previousSleepingIgnoredStates.remove(uuid);
        if (previousSleepingIgnored != null) {
            player.setSleepingIgnored(previousSleepingIgnored);
        }
    }

    private void refreshVisibilityForVanishedPlayer(Player vanished) {
        if (!isVanished(vanished) || !vanished.isOnline()) {
            return;
        }

        rememberPlayer(vanished);

        for (Player viewer : Bukkit.getOnlinePlayers()) {
            updateVisibility(viewer, vanished);
        }
    }

    private void refreshVisibilityForViewer(Player viewer) {
        if (!viewer.isOnline()) {
            return;
        }

        rememberPlayer(viewer);

        for (UUID vanishedUuid : snapshotVanishedPlayers()) {
            Player vanished = Bukkit.getPlayer(vanishedUuid);

            if (vanished == null || !vanished.isOnline()) {
                continue;
            }

            updateVisibility(viewer, vanished);
        }
    }

    private void updateVisibility(Player viewer, Player vanished) {
        if (viewer.equals(vanished)) {
            return;
        }

        boolean canSee = canSeeVanished(viewer);

        if (canSee) {
            showVanishedPlayerToViewer(viewer, vanished);
            return;
        }

        hideVanishedPlayerFromViewer(viewer, vanished);
    }

    private void hideVanishedPlayerFromViewer(Player viewer, Player vanished) {
        viewer.hidePlayer(plugin, vanished);
        unlistPlayerForViewer(viewer, vanished);
        tabBridge.updateVisibility(viewer, vanished, false);
    }

    private void showVanishedPlayerToViewer(Player viewer, Player vanished) {
        viewer.showPlayer(plugin, vanished);
        relistPlayerForViewer(viewer, vanished);
        tabBridge.updateVisibility(viewer, vanished, true);
    }

    private void revealPlayerToEveryone(Player player) {
        for (Player viewer : Bukkit.getOnlinePlayers()) {
            viewer.showPlayer(plugin, player);
            relistPlayerForViewer(viewer, player);
            tabBridge.updateVisibility(viewer, player, true);
        }
    }

    private void unlistPlayerForViewer(Player viewer, Player vanished) {
        if (!USE_PAPER_PLAYER_LIST_API || viewer.equals(vanished)) {
            return;
        }

        UUID vanishedUuid = vanished.getUniqueId();
        UUID viewerUuid = viewer.getUniqueId();

        if (!viewer.isListed(vanished)) {
            return;
        }

        viewer.unlistPlayer(vanished);
        playerListUnlistedByPixelAdmin
                .computeIfAbsent(vanishedUuid, ignored -> ConcurrentHashMap.newKeySet())
                .add(viewerUuid);
    }

    private void relistPlayerForViewer(Player viewer, Player vanished) {
        if (!USE_PAPER_PLAYER_LIST_API || viewer.equals(vanished)) {
            return;
        }

        UUID vanishedUuid = vanished.getUniqueId();
        UUID viewerUuid = viewer.getUniqueId();
        Set<UUID> viewers = playerListUnlistedByPixelAdmin.get(vanishedUuid);

        if (viewers == null || !viewers.remove(viewerUuid)) {
            return;
        }

        if (viewers.isEmpty()) {
            playerListUnlistedByPixelAdmin.remove(vanishedUuid);
        }

        safelyListPlayer(viewer, vanished);
    }

    private void clearTrackedListState(Player vanished) {
        UUID vanishedUuid = vanished.getUniqueId();
        Set<UUID> viewers = playerListUnlistedByPixelAdmin.remove(vanishedUuid);

        if (viewers == null || viewers.isEmpty()) {
            return;
        }

        for (UUID viewerUuid : viewers) {
            Player viewer = Bukkit.getPlayer(viewerUuid);

            if (viewer != null && viewer.isOnline()) {
                safelyListPlayer(viewer, vanished);
            }
        }
    }

    private void safelyListPlayer(Player viewer, Player vanished) {
        if (!viewer.canSee(vanished)) {
            return;
        }

        try {
            viewer.listPlayer(vanished);
        } catch (IllegalStateException ignored) {
            // Another plugin may still be hiding the player; keep its visibility decision intact.
        }
    }

    private void cleanupOfflineListTracking() {
        Set<UUID> online = new HashSet<>();

        for (Player player : Bukkit.getOnlinePlayers()) {
            online.add(player.getUniqueId());
        }

        playerListUnlistedByPixelAdmin.entrySet().removeIf(entry -> {
            if (!online.contains(entry.getKey())) {
                return true;
            }

            entry.getValue().removeIf(uuid -> !online.contains(uuid));
            return entry.getValue().isEmpty();
        });
    }

    private void queueFullRefresh() {
        for (Player player : Bukkit.getOnlinePlayers()) {
            rememberPlayer(player);
            queueViewerRefresh(player.getUniqueId());

            if (isVanished(player)) {
                queueVanishRefresh(player.getUniqueId());
            }
        }
    }

    private void queueVanishRefresh(UUID vanishedUuid) {
        if (vanishedUuid == null || shuttingDown) {
            return;
        }

        pendingVanishedRefreshes.add(vanishedUuid);
        ensureRefreshTask();
    }

    private void queueViewerRefresh(UUID viewerUuid) {
        if (viewerUuid == null || shuttingDown) {
            return;
        }

        pendingViewerRefreshes.add(viewerUuid);
        ensureRefreshTask();
    }

    private void ensureRefreshTask() {
        if (refreshTask != null || !plugin.isEnabled()) {
            return;
        }

        refreshTask = Bukkit.getScheduler().runTaskTimer(plugin, this::processRefreshQueues, 1L, 1L);
    }

    private void processRefreshQueues() {
        int processed = 0;
        Deque<UUID> vanishedQueue = new ArrayDeque<>(pendingVanishedRefreshes);
        Deque<UUID> viewerQueue = new ArrayDeque<>(pendingViewerRefreshes);

        while (!vanishedQueue.isEmpty() && processed < REFRESH_BATCH_SIZE) {
            UUID uuid = vanishedQueue.removeFirst();
            pendingVanishedRefreshes.remove(uuid);
            Player vanished = Bukkit.getPlayer(uuid);

            if (vanished != null && vanished.isOnline() && isVanished(vanished)) {
                applyVanishedState(vanished);
                refreshVisibilityForVanishedPlayer(vanished);
            }

            processed++;
        }

        while (!viewerQueue.isEmpty() && processed < REFRESH_BATCH_SIZE) {
            UUID uuid = viewerQueue.removeFirst();
            pendingViewerRefreshes.remove(uuid);
            Player viewer = Bukkit.getPlayer(uuid);

            if (viewer != null && viewer.isOnline()) {
                refreshVisibilityForViewer(viewer);
            }

            processed++;
        }

        if (pendingVanishedRefreshes.isEmpty() && pendingViewerRefreshes.isEmpty()) {
            cancelRefreshTask();
        }
    }

    private void cancelRefreshTask() {
        if (refreshTask != null) {
            refreshTask.cancel();
            refreshTask = null;
        }
    }

    private void scheduleDelayedVanishRefresh(UUID vanishedUuid) {
        scheduleDelayedVanishRefresh(vanishedUuid, FIRST_REFRESH_DELAY_TICKS);
        scheduleDelayedVanishRefresh(vanishedUuid, SECOND_REFRESH_DELAY_TICKS);
    }

    private void scheduleDelayedVanishRefresh(UUID vanishedUuid, long delayTicks) {
        if (!plugin.isEnabled() || shuttingDown) {
            return;
        }

        Bukkit.getScheduler().runTaskLater(plugin, () -> queueVanishRefresh(vanishedUuid), delayTicks);
    }

    private void scheduleDelayedViewerRefresh(UUID viewerUuid) {
        scheduleDelayedViewerRefresh(viewerUuid, FIRST_REFRESH_DELAY_TICKS);
        scheduleDelayedViewerRefresh(viewerUuid, SECOND_REFRESH_DELAY_TICKS);
    }

    private void scheduleDelayedViewerRefresh(UUID viewerUuid, long delayTicks) {
        if (!plugin.isEnabled() || shuttingDown) {
            return;
        }

        Bukkit.getScheduler().runTaskLater(plugin, () -> queueViewerRefresh(viewerUuid), delayTicks);
    }

    private void broadcastLocalizedJoin(Player player) {
        String name = player.getName();

        for (Player recipient : Bukkit.getOnlinePlayers()) {
            recipient.sendMessage(Component.text(name + localized(recipient, JOIN_AR, JOIN_EN), NamedTextColor.YELLOW));
        }
    }

    private void broadcastLocalizedVanishJoin(Player player) {
        broadcastLocalizedJoin(player);
    }

    private void broadcastLocalizedVanishQuit(Player player) {
        broadcastLocalizedQuit(player, true);
    }

    private void broadcastLocalizedQuit(Player player, boolean includeSubject) {
        String name = player.getName();

        for (Player recipient : Bukkit.getOnlinePlayers()) {
            if (includeSubject || !recipient.equals(player)) {
                recipient.sendMessage(Component.text(name + localized(recipient, QUIT_AR, QUIT_EN), NamedTextColor.YELLOW));
            }
        }
    }

    private void sendLocalized(Player player, String arabic, String english) {
        player.sendMessage(Component.text(localized(player, arabic, english)));
    }

    private String localized(Player player, String arabic, String english) {
        return isArabic(player) ? arabic : english;
    }

    private boolean isArabic(Player player) {
        String locale = player.getLocale();
        return locale != null && locale.toLowerCase(Locale.ROOT).startsWith("ar");
    }

    private boolean shouldHideVanishedChatFromAsync(Audience audience, Player sender) {
        if (!(audience instanceof Player viewer)) {
            return false;
        }

        return !viewer.equals(sender) && !cachedCanSeeVanished(viewer);
    }

    private Optional<Player> findAttackingPlayer(Entity damager) {
        if (damager instanceof Player player) {
            return Optional.of(player);
        }

        if (damager instanceof org.bukkit.entity.Projectile projectile && projectile.getShooter() instanceof Player player) {
            return Optional.of(player);
        }

        if (damager instanceof org.bukkit.entity.Tameable tameable && tameable.getOwner() instanceof Player player) {
            return Optional.of(player);
        }

        return Optional.empty();
    }

    private void clearCurrentMobTargets(Player player) {
        Location location = player.getLocation();
        World world = location.getWorld();

        if (world == null) {
            return;
        }

        Collection<Entity> nearbyEntities = world.getNearbyEntities(
                location,
                TARGET_CLEAR_RADIUS,
                TARGET_CLEAR_RADIUS,
                TARGET_CLEAR_RADIUS,
                entity -> entity instanceof Mob
        );

        for (Entity entity : nearbyEntities) {
            Mob mob = (Mob) entity;

            if (player.equals(mob.getTarget())) {
                mob.setTarget(null);
            }
        }
    }

    private void removeVanishedNameCompletions(Collection<String> completions) {
        removeVanishedNameCompletions(completions, false);
    }

    private void removeVanishedNameCompletions(Collection<String> completions, boolean cachedOnly) {
        if (completions == null || completions.isEmpty() || vanishedPlayers.isEmpty()) {
            return;
        }

        Set<String> names = cachedOnly ? vanishedNamesLowercaseCached() : vanishedNamesLowercase();
        completions.removeIf(completion -> isHiddenNameCompletion(completion, names));
    }

    private boolean isHiddenNameCompletion(String completion, Set<String> vanishedNamesLowercase) {
        if (completion == null || completion.isBlank()) {
            return false;
        }

        String normalized = normalizeCompletion(completion);
        return vanishedNamesLowercase.contains(normalized);
    }

    private String normalizeCompletion(String completion) {
        int namespaceIndex = completion.indexOf(':');
        String candidate = namespaceIndex >= 0 ? completion.substring(namespaceIndex + 1) : completion;
        return candidate.toLowerCase(Locale.ROOT);
    }

    private boolean commandMentionsVanishedPlayer(String command) {
        if (command == null || command.isBlank() || vanishedPlayers.isEmpty()) {
            return false;
        }

        String lowercaseCommand = command.toLowerCase(Locale.ROOT);

        for (String vanishedName : vanishedNamesLowercase()) {
            Pattern pattern = Pattern.compile("(?<![A-Za-z0-9_])" + Pattern.quote(vanishedName) + "(?![A-Za-z0-9_])");

            if (pattern.matcher(lowercaseCommand).find()) {
                return true;
            }
        }

        return false;
    }

    private Set<String> vanishedNamesLowercase() {
        Set<String> names = new HashSet<>();

        for (UUID uuid : snapshotVanishedPlayers()) {
            String name = knownLowercaseNames.get(uuid);

            if (name != null && !name.isBlank()) {
                names.add(name);
                continue;
            }

            Player online = Bukkit.getPlayer(uuid);

            if (online != null) {
                rememberPlayer(online);
                names.add(online.getName().toLowerCase(Locale.ROOT));
                continue;
            }

            OfflinePlayer offline = Bukkit.getOfflinePlayer(uuid);
            String offlineName = offline.getName();

            if (offlineName != null && !offlineName.isBlank()) {
                knownPlayerNames.put(uuid, offlineName);
                knownLowercaseNames.put(uuid, offlineName.toLowerCase(Locale.ROOT));
                names.add(offlineName.toLowerCase(Locale.ROOT));
            }
        }

        return names;
    }

    private Set<String> vanishedNamesLowercaseCached() {
        Set<String> names = new HashSet<>();

        for (UUID uuid : snapshotVanishedPlayers()) {
            String name = knownLowercaseNames.get(uuid);

            if (name != null && !name.isBlank()) {
                names.add(name);
            }
        }

        return names;
    }

    private void applyNameTagFallback(Player player) {
        String entry = player.getName();

        forEachKnownScoreboard(scoreboard -> addToVanishTeamIfSafe(scoreboard, entry));
    }

    private void clearNameTagFallback(Player player) {
        String entry = player.getName();

        forEachKnownScoreboard(scoreboard -> removeFromVanishTeam(scoreboard, entry));
    }

    private void configureAllKnownVanishTeams() {
        forEachKnownScoreboard(this::getOrCreateVanishTeam);
    }

    private void addToVanishTeamIfSafe(Scoreboard scoreboard, String entry) {
        Team existingTeam = scoreboard.getEntryTeam(entry);

        if (existingTeam != null && !VANISH_TEAM_NAME.equals(existingTeam.getName())) {
            return;
        }

        Team vanishTeam = getOrCreateVanishTeam(scoreboard);

        if (!vanishTeam.hasEntry(entry)) {
            vanishTeam.addEntry(entry);
        }
    }

    private void removeFromVanishTeam(Scoreboard scoreboard, String entry) {
        Team vanishTeam = scoreboard.getTeam(VANISH_TEAM_NAME);

        if (vanishTeam != null && vanishTeam.hasEntry(entry)) {
            vanishTeam.removeEntry(entry);
        }
    }

    private Team getOrCreateVanishTeam(Scoreboard scoreboard) {
        Team team = scoreboard.getTeam(VANISH_TEAM_NAME);

        if (team == null) {
            team = scoreboard.registerNewTeam(VANISH_TEAM_NAME);
        }

        configureVanishTeam(team);
        return team;
    }

    private void configureVanishTeam(Team team) {
        team.setOption(Team.Option.NAME_TAG_VISIBILITY, Team.OptionStatus.NEVER);
        team.setOption(Team.Option.COLLISION_RULE, Team.OptionStatus.NEVER);
        team.setCanSeeFriendlyInvisibles(false);
    }

    private void forEachKnownScoreboard(Consumer<Scoreboard> action) {
        Set<Scoreboard> scoreboards = Collections.newSetFromMap(new IdentityHashMap<>());
        Scoreboard mainScoreboard = getMainScoreboard();

        if (mainScoreboard != null) {
            scoreboards.add(mainScoreboard);
        }

        for (Player player : Bukkit.getOnlinePlayers()) {
            scoreboards.add(player.getScoreboard());
        }

        for (Scoreboard scoreboard : scoreboards) {
            if (scoreboard != null) {
                action.accept(scoreboard);
            }
        }
    }

    private Scoreboard getMainScoreboard() {
        ScoreboardManager manager = Bukkit.getScoreboardManager();
        return manager == null ? null : manager.getMainScoreboard();
    }

    private void removeOfflineEntriesFromScoreboards() {
        Set<String> onlineVanishedNames = new HashSet<>();

        for (Player player : getOnlineVanishedPlayers()) {
            onlineVanishedNames.add(player.getName());
        }

        forEachKnownScoreboard(scoreboard -> {
            Team vanishTeam = scoreboard.getTeam(VANISH_TEAM_NAME);

            if (vanishTeam == null) {
                return;
            }

            for (String entry : Set.copyOf(vanishTeam.getEntries())) {
                if (!onlineVanishedNames.contains(entry)) {
                    vanishTeam.removeEntry(entry);
                }
            }
        });
    }

    private void unregisterEmptyVanishTeams() {
        forEachKnownScoreboard(scoreboard -> {
            Team vanishTeam = scoreboard.getTeam(VANISH_TEAM_NAME);

            if (vanishTeam != null && vanishTeam.getEntries().isEmpty()) {
                vanishTeam.unregister();
            }
        });
    }

    private void loadVanishedPlayers() {
        if (!PERSIST_VANISH_ACROSS_RESTARTS || !storageFile.exists()) {
            return;
        }

        YamlConfiguration configuration = YamlConfiguration.loadConfiguration(storageFile);

        for (String rawUuid : configuration.getStringList(STORAGE_KEY)) {
            try {
                vanishedPlayers.add(UUID.fromString(rawUuid));
            } catch (IllegalArgumentException exception) {
                logWarning("Ignoring invalid vanished player UUID in " + storageFile.getName() + ": " + rawUuid);
            }
        }
    }

    private void requestSave() {
        if (!PERSIST_VANISH_ACROSS_RESTARTS || shuttingDown || !plugin.isEnabled()) {
            return;
        }

        if (saveTask != null) {
            return;
        }

        saveTask = Bukkit.getScheduler().runTaskLater(plugin, () -> {
            saveTask = null;
            saveVanishedPlayersNow();
        }, SAVE_DEBOUNCE_TICKS);
    }

    private void cancelSaveTask() {
        if (saveTask != null) {
            saveTask.cancel();
            saveTask = null;
        }
    }

    private void saveVanishedPlayersNow() {
        if (!PERSIST_VANISH_ACROSS_RESTARTS) {
            return;
        }

        File parent = storageFile.getParentFile();

        if (parent != null && !parent.exists() && !parent.mkdirs()) {
            logWarning("Could not create plugin data folder: " + parent.getAbsolutePath());
            return;
        }

        YamlConfiguration configuration = new YamlConfiguration();
        List<String> serialized = snapshotVanishedPlayers()
                .stream()
                .map(UUID::toString)
                .sorted()
                .toList();

        configuration.set(STORAGE_KEY, serialized);

        try {
            configuration.save(storageFile);
        } catch (IOException exception) {
            logWarning("Could not save vanished player storage: " + exception.getMessage());
        }
    }

    private void rememberPlayer(Player player) {
        UUID uuid = player.getUniqueId();

        knownPlayerNames.put(uuid, player.getName());
        knownLowercaseNames.put(uuid, player.getName().toLowerCase(Locale.ROOT));
        canSeeVanishedCache.put(uuid, evaluateCanSeeVanished(player));
    }

    private boolean cachedCanSeeVanished(Player player) {
        if (player == null) {
            return false;
        }

        return canSeeVanishedCache.getOrDefault(player.getUniqueId(), false);
    }

    private boolean evaluateCanSeeVanished(Player player) {
        if (player.hasPermission(PIXELADMIN_SEE_PERMISSION)) {
            return true;
        }

        return CHECK_TAB_SEE_PERMISSION_AS_FALLBACK && player.hasPermission(TAB_SEE_PERMISSION);
    }

    private List<Player> getOnlineVanishedPlayers() {
        List<Player> players = new ArrayList<>();

        for (UUID uuid : snapshotVanishedPlayers()) {
            Player player = Bukkit.getPlayer(uuid);

            if (player != null && player.isOnline()) {
                players.add(player);
            }
        }

        return players;
    }

    private Set<UUID> snapshotVanishedPlayers() {
        return new LinkedHashSet<>(vanishedPlayers);
    }

    private boolean runSyncIfNeeded(Runnable action) {
        if (Bukkit.isPrimaryThread()) {
            return false;
        }

        if (plugin.isEnabled()) {
            Bukkit.getScheduler().runTask(plugin, action);
        }

        return true;
    }

    private void connectTabBridgeIfPossible() {
        if (tabBridge.isAvailable()) {
            return;
        }

        Plugin tabPlugin = Bukkit.getPluginManager().getPlugin(TAB_PLUGIN_NAME);

        if (tabPlugin == null || !tabPlugin.isEnabled()) {
            return;
        }

        try {
            tabBridge = new NeznamyTabBridge(this);
            tabBridge.open();
            logInfo("Hooked into NEZNAMY TAB API.");
        } catch (Throwable throwable) {
            tabBridge = TabBridge.noop();
            logWarning("TAB plugin was found, but PixelAdmin could not hook into its API: " + throwable.getMessage());
        }
    }

    private boolean isTabPlugin(Plugin plugin) {
        return plugin != null && TAB_PLUGIN_NAME.equalsIgnoreCase(plugin.getName());
    }

    private void logInfo(String message) {
        Bukkit.getLogger().info("[PixelAdmin] " + message);
    }

    private void logWarning(String message) {
        Bukkit.getLogger().warning("[PixelAdmin] " + message);
    }

    private void logWarning(String message, Throwable throwable) {
        Bukkit.getLogger().log(Level.WARNING, "[PixelAdmin] " + message, throwable);
    }

    @FunctionalInterface
    private interface ViewerPermissionResolver {

        boolean canSee(Player player);
    }

    private interface TabBridge {

        static TabBridge noop() {
            return NoopTabBridge.INSTANCE;
        }

        boolean isAvailable();

        default void open() {
        }

        default void close() {
        }

        default void applyVanish(Player vanished, Collection<? extends Player> viewers, ViewerPermissionResolver resolver) {
        }

        default void updateVisibility(Player viewer, Player vanished, boolean visible) {
        }

        default void reveal(Player player, Collection<? extends Player> viewers) {
        }

        default void refreshAll(Collection<? extends Player> onlinePlayers, Set<UUID> vanishedPlayers) {
        }
    }

    private enum NoopTabBridge implements TabBridge {

        INSTANCE;

        @Override
        public boolean isAvailable() {
            return false;
        }
    }

    private static final class NeznamyTabBridge implements TabBridge {

        private final VanishManager vanishManager;
        private final me.neznamy.tab.api.TabAPI tabApi;
        private final me.neznamy.tab.api.event.EventBus eventBus;
        private final Map<UUID, Set<UUID>> hiddenNameTags = new HashMap<>();
        private me.neznamy.tab.api.event.EventHandler<me.neznamy.tab.api.event.player.PlayerLoadEvent> playerLoadHandler;
        private me.neznamy.tab.api.event.EventHandler<me.neznamy.tab.api.event.plugin.TabLoadEvent> tabLoadHandler;
        private boolean opened;

        private NeznamyTabBridge(VanishManager vanishManager) {
            this.vanishManager = vanishManager;
            this.tabApi = me.neznamy.tab.api.TabAPI.getInstance();

            if (tabApi == null) {
                throw new IllegalStateException("TabAPI#getInstance returned null");
            }

            this.eventBus = tabApi.getEventBus();

            if (eventBus == null) {
                throw new IllegalStateException("TAB EventBus is not available");
            }
        }

        @Override
        public boolean isAvailable() {
            return true;
        }

        @Override
        public void open() {
            if (opened) {
                return;
            }

            playerLoadHandler = event -> {
                me.neznamy.tab.api.TabPlayer tabPlayer = event.getPlayer();

                if (tabPlayer == null) {
                    return;
                }

                UUID uuid = tabPlayer.getUniqueId();

                Bukkit.getScheduler().runTask(vanishManager.plugin, () -> {
                    Player player = Bukkit.getPlayer(uuid);

                    if (player == null || !player.isOnline()) {
                        return;
                    }

                    vanishManager.queueViewerRefresh(uuid);

                    if (vanishManager.isVanished(player)) {
                        vanishManager.queueVanishRefresh(uuid);
                    }
                });
            };

            tabLoadHandler = event -> Bukkit.getScheduler().runTask(vanishManager.plugin, vanishManager::queueFullRefresh);

            eventBus.register(me.neznamy.tab.api.event.player.PlayerLoadEvent.class, playerLoadHandler);
            eventBus.register(me.neznamy.tab.api.event.plugin.TabLoadEvent.class, tabLoadHandler);
            opened = true;
        }

        @Override
        public void close() {
            if (!opened) {
                return;
            }

            try {
                if (playerLoadHandler != null) {
                    eventBus.unregister(playerLoadHandler);
                    playerLoadHandler = null;
                }

                if (tabLoadHandler != null) {
                    eventBus.unregister(tabLoadHandler);
                    tabLoadHandler = null;
                }

                revealAllTrackedNameTags();
            } catch (Throwable throwable) {
                vanishManager.logWarning("Could not cleanly close TAB bridge: " + throwable.getMessage());
            } finally {
                hiddenNameTags.clear();
                opened = false;
            }
        }

        @Override
        public void applyVanish(Player vanished, Collection<? extends Player> viewers, ViewerPermissionResolver resolver) {
            me.neznamy.tab.api.TabPlayer tabVanished = getTabPlayer(vanished);

            if (tabVanished == null) {
                return;
            }

            disableTabCollision(tabVanished);

            for (Player viewer : viewers) {
                if (viewer.equals(vanished)) {
                    continue;
                }

                updateVisibility(viewer, vanished, resolver.canSee(viewer));
            }
        }

        @Override
        public void updateVisibility(Player viewer, Player vanished, boolean visible) {
            me.neznamy.tab.api.TabPlayer tabViewer = getTabPlayer(viewer);
            me.neznamy.tab.api.TabPlayer tabVanished = getTabPlayer(vanished);

            if (tabViewer == null || tabVanished == null || viewer.equals(vanished)) {
                return;
            }

            if (visible) {
                showNameTag(tabVanished, tabViewer);
                return;
            }

            hideNameTag(tabVanished, tabViewer);
        }

        @Override
        public void reveal(Player player, Collection<? extends Player> viewers) {
            me.neznamy.tab.api.TabPlayer tabPlayer = getTabPlayer(player);

            if (tabPlayer == null) {
                return;
            }

            restoreTabCollision(tabPlayer);

            for (Player viewer : viewers) {
                me.neznamy.tab.api.TabPlayer tabViewer = getTabPlayer(viewer);

                if (tabViewer != null && !viewer.equals(player)) {
                    showNameTag(tabPlayer, tabViewer);
                }
            }

            hiddenNameTags.remove(player.getUniqueId());
        }

        @Override
        public void refreshAll(Collection<? extends Player> onlinePlayers, Set<UUID> vanishedPlayers) {
            for (Player player : onlinePlayers) {
                if (vanishedPlayers.contains(player.getUniqueId())) {
                    applyVanish(player, onlinePlayers, vanishManager::canSeeVanished);
                    continue;
                }

                reveal(player, onlinePlayers);
            }
        }

        private me.neznamy.tab.api.TabPlayer getTabPlayer(Player player) {
            if (player == null) {
                return null;
            }

            try {
                return tabApi.getPlayer(player.getUniqueId());
            } catch (Throwable throwable) {
                return null;
            }
        }

        private void hideNameTag(me.neznamy.tab.api.TabPlayer vanished, me.neznamy.tab.api.TabPlayer viewer) {
            me.neznamy.tab.api.nametag.NameTagManager nameTagManager = tabApi.getNameTagManager();

            if (nameTagManager == null) {
                return;
            }

            try {
                nameTagManager.hideNameTag(vanished, viewer);
                hiddenNameTags
                        .computeIfAbsent(vanished.getUniqueId(), ignored -> new HashSet<>())
                        .add(viewer.getUniqueId());
            } catch (Throwable throwable) {
                vanishManager.logWarning("TAB NameTagManager#hideNameTag failed: " + throwable.getMessage());
            }
        }

        private void showNameTag(me.neznamy.tab.api.TabPlayer vanished, me.neznamy.tab.api.TabPlayer viewer) {
            me.neznamy.tab.api.nametag.NameTagManager nameTagManager = tabApi.getNameTagManager();

            if (nameTagManager == null) {
                return;
            }

            try {
                nameTagManager.showNameTag(vanished, viewer);
                Set<UUID> viewers = hiddenNameTags.get(vanished.getUniqueId());

                if (viewers != null) {
                    viewers.remove(viewer.getUniqueId());

                    if (viewers.isEmpty()) {
                        hiddenNameTags.remove(vanished.getUniqueId());
                    }
                }
            } catch (Throwable throwable) {
                vanishManager.logWarning("TAB NameTagManager#showNameTag failed: " + throwable.getMessage());
            }
        }

        private void disableTabCollision(me.neznamy.tab.api.TabPlayer tabPlayer) {
            me.neznamy.tab.api.nametag.NameTagManager nameTagManager = tabApi.getNameTagManager();

            if (nameTagManager == null) {
                return;
            }

            try {
                nameTagManager.setCollisionRule(tabPlayer, false);
            } catch (Throwable throwable) {
                vanishManager.logWarning("TAB NameTagManager#setCollisionRule(false) failed: " + throwable.getMessage());
            }
        }

        private void restoreTabCollision(me.neznamy.tab.api.TabPlayer tabPlayer) {
            me.neznamy.tab.api.nametag.NameTagManager nameTagManager = tabApi.getNameTagManager();

            if (nameTagManager == null) {
                return;
            }

            try {
                nameTagManager.setCollisionRule(tabPlayer, null);
            } catch (Throwable throwable) {
                vanishManager.logWarning("TAB NameTagManager#setCollisionRule(null) failed: " + throwable.getMessage());
            }
        }

        private void revealAllTrackedNameTags() {
            me.neznamy.tab.api.nametag.NameTagManager nameTagManager = tabApi.getNameTagManager();

            if (nameTagManager == null) {
                return;
            }

            for (Map.Entry<UUID, Set<UUID>> entry : new HashMap<>(hiddenNameTags).entrySet()) {
                me.neznamy.tab.api.TabPlayer vanished = tabApi.getPlayer(entry.getKey());

                if (vanished == null) {
                    continue;
                }

                for (UUID viewerUuid : new HashSet<>(entry.getValue())) {
                    me.neznamy.tab.api.TabPlayer viewer = tabApi.getPlayer(viewerUuid);

                    if (viewer != null) {
                        nameTagManager.showNameTag(vanished, viewer);
                    }
                }
            }
        }
    }
}
