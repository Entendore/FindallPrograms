import sys
import math
import random
import subprocess
import tempfile
import os
import time
import json
import traceback
from collections import deque
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QGraphicsView, QGraphicsScene, QGraphicsObject, QGraphicsTextItem,
    QLabel, QPushButton, QFormLayout, QLineEdit, QListWidget,
    QListWidgetItem, QGroupBox, QSplitter, QPlainTextEdit, QFileDialog,
    QCheckBox, QDoubleSpinBox, QSpinBox, QMenu, QMessageBox,
    QProgressBar, QComboBox, QToolButton, QStatusBar
)
from PySide6.QtCore import (
    Qt, QRectF, Signal, QThread, QMutex, QWaitCondition, QSettings, QPointF
)
from PySide6.QtGui import (
    QPen, QBrush, QColor, QPainter, QKeySequence, QShortcut, QFont,
    QPolygonF, QPainterPath, QImage
)

# ==========================================
# Theme Stylesheets
# ==========================================
DARK_QSS = """
QMainWindow, QWidget { background-color: #1e1e2e; color: #cdd6f4; font-family: "Segoe UI", "SF Pro", sans-serif; font-size: 10pt; }
QGroupBox { border: 1px solid #45475a; border-radius: 8px; margin-top: 12px; padding-top: 10px; font-weight: bold; color: #cba6f7; }
QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 4px; }
QPushButton { background-color: #313244; border: 1px solid #45475a; border-radius: 6px; padding: 6px 12px; color: #cdd6f4; }
QPushButton:hover { background-color: #45475a; border-color: #89b4fa; }
QPushButton:pressed { background-color: #11111b; }
QPushButton:checked { background-color: #89b4fa; color: #1e1e2e; font-weight: bold; }
QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox { background-color: #313244; border: 1px solid #45475a; border-radius: 4px; padding: 4px 6px; color: #cdd6f4; selection-background-color: #89b4fa; }
QListWidget { background-color: #181825; border: 1px solid #45475a; border-radius: 4px; }
QPlainTextEdit { background-color: #181825; border: 1px solid #45475a; border-radius: 4px; font-family: "JetBrains Mono", "Consolas", monospace; font-size: 9pt; }
QLabel { color: #cdd6f4; }
QCheckBox { spacing: 6px; }
QCheckBox::indicator { width: 14px; height: 14px; border-radius: 3px; border: 1px solid #45475a; background: #313244; }
QCheckBox::indicator:checked { background: #89b4fa; border: #89b4fa; }
QSplitter::handle { background: #45475a; width: 2px; }
QScrollBar:vertical { background: #181825; width: 10px; }
QScrollBar::handle:vertical { background: #45475a; border-radius: 5px; min-height: 20px; }
QStatusBar { background: #181825; color: #a6adc8; }
QToolBar { background: #181825; border: none; }
"""

LIGHT_QSS = """
QMainWindow, QWidget { background-color: #fafafa; color: #1e1e2e; font-family: "Segoe UI", sans-serif; font-size: 10pt; }
QGroupBox { border: 1px solid #d4d4d8; border-radius: 8px; margin-top: 12px; padding-top: 10px; font-weight: bold; color: #6b21a8; }
QPushButton { background-color: #ffffff; border: 1px solid #d4d4d8; border-radius: 6px; padding: 6px 12px; }
QPushButton:hover { border-color: #3b82f6; background: #eff6ff; }
QStatusBar { background: #f4f4f5; color: #525252; }
"""

# ==========================================
# 1. Subprocess Execution Validator
# ==========================================
def _kill_process(proc):
    """Kill the process tree, not just the parent."""
    try:
        if os.name == 'nt':
            subprocess.run(
                ['taskkill', '/F', '/T', '/PID', str(proc.pid)],
                capture_output=True, timeout=5
            )
        else:
            import signal
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    except Exception:
        pass
    finally:
        try:
            proc.wait(timeout=2)
        except Exception:
            pass

def execute_and_check_compile(program_string, interpreter_path=None, timeout=1.0):
    """Write program to a temp file and run with the current interpreter."""
    if not program_string.strip():
        return False, "Empty program", ""

    fd, temp_path = tempfile.mkstemp(suffix=".py")
    try:
        with os.fdopen(fd, 'w') as f:
            f.write(program_string)

        kwargs = {}
        if os.name == 'nt':
            kwargs['creationflags'] = subprocess.CREATE_NEW_PROCESS_GROUP
        else:
            kwargs['start_new_session'] = True

        cmd = [interpreter_path or sys.executable, temp_path]
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            **kwargs
        )
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
            if proc.returncode == 0:
                snippet = stdout.strip()[:200] if stdout and stdout.strip() else ""
                return True, "OK exit 0", snippet
            err_lines = stderr.strip().split('\n') if stderr else []
            last = err_lines[-1] if err_lines else f"Exit {proc.returncode}"
            return False, f"Error: {last[:120]}", ""
        except subprocess.TimeoutExpired:
            _kill_process(proc)
            return False, "Timeout (likely infinite loop)", ""
    except Exception as e:
        return False, f"Exception: {e}", ""
    finally:
        try:
            os.unlink(temp_path)
        except OSError:
            pass


# ==========================================
# 2. MCTS Core Logic (Threaded)
# ==========================================
class Node:
    __slots__ = ("state", "parent", "children", "dead_actions", "visits",
                 "reward", "last_reward", "untried_actions", "layout_x",
                 "layout_y", "status_msg", "compile_status",
                 "_layout_dirty", "_child_count_at_layout")

    def __init__(self, state, parent=None):
        self.state = state
        self.parent = parent
        self.children = {}
        self.dead_actions = set()
        self.visits = 0
        self.reward = 0.0
        self.last_reward = 0.0
        self.untried_actions = None
        self.layout_x = 0.0
        self.layout_y = 0.0
        self.status_msg = "Unvisited"
        self.compile_status = "unknown"
        self._layout_dirty = True
        self._child_count_at_layout = 0

    def mark_dirty(self):
        n = self
        while n is not None and not n._layout_dirty:
            n._layout_dirty = True
            n = n.parent


class MCTSWorker(QThread):
    update_tree = Signal(object, object)
    update_stats = Signal(int, int, int, float, int, int, float, int)
    program_found = Signal(str, str)
    log_output = Signal(str, str)

    def __init__(self, alphabet, min_n, max_n, forbids,
                 exploration=1.414, timeout=1.0, max_tree_size=20000,
                 heuristic_epsilon=0.15, interpreter_path=None,
                 max_iterations=0, stop_on_first=False):
        super().__init__()
        self.alphabet = list(dict.fromkeys(alphabet))
        
        if min_n > max_n:
            min_n, max_n = max_n, min_n
            
        self.min_n = min_n
        self.max_n = max_n
        self.forbids = [f for f in forbids if f]
        self.exploration = exploration
        self.timeout = timeout
        self.max_tree_size = max_tree_size
        self.heuristic_epsilon = heuristic_epsilon
        self.interpreter_path = interpreter_path
        self.max_iterations = max_iterations
        self.stop_on_first = stop_on_first

        self._pause_mutex = QMutex()
        self._pause_cond = QWaitCondition()
        self._paused = False
        self._running = True
        self._running_mutex = QMutex()

        self.total_programs = sum(len(self.alphabet) ** i for i in range(min_n, max_n + 1)) if self.alphabet else 0

        self.root = Node("")
        self.state_to_node = {"": self.root}
        self.discovered_programs = {}
        self.failed_programs = {}
        self.duplicates = 0
        self.iterations = 0
        self.tree_size = 1
        self.max_depth = 0
        self.best_program = None
        self.best_reward = -1.0
        self.last_update_time = 0.0

        self.char_success = {a: 0 for a in self.alphabet}
        self.iter_timestamps = deque(maxlen=200)

    @property
    def running(self):
        self._running_mutex.lock()
        val = self._running
        self._running_mutex.unlock()
        return val

    @running.setter
    def running(self, val):
        self._running_mutex.lock()
        self._running = val
        self._running_mutex.unlock()
        if not val:
            self.resume()  # Unblock wait if stopping

    def is_paused(self):
        self._pause_mutex.lock()
        val = self._paused
        self._pause_mutex.unlock()
        return val

    def pause(self):
        self._pause_mutex.lock()
        self._paused = True
        self._pause_mutex.unlock()

    def resume(self):
        self._pause_mutex.lock()
        self._paused = False
        self._pause_cond.wakeAll()
        self._pause_mutex.unlock()

    def is_terminal(self, state):
        return len(state) >= self.max_n

    def get_untried_actions(self, node):
        if node.untried_actions is None:
            valid = []
            for a in self.alphabet:
                state = node.state + a
                if not any(f in state for f in self.forbids):
                    valid.append(a)
                else:
                    node.dead_actions.add(a)
            node.untried_actions = valid
        return node.untried_actions

    def uct_select_child(self, node):
        log_visits = math.log(max(1, node.visits))
        best_score = -float('inf')
        best_child = None

        for child in node.children.values():
            if child.visits == 0:
                return child
            exploit = child.reward / child.visits
            explore = math.sqrt(log_visits / child.visits)
            score = exploit + self.exploration * explore
            if score > best_score:
                best_score = score
                best_child = child
        return best_child or random.choice(list(node.children.values()))

    def select(self):
        node = self.root
        path = [node]
        while not self.is_terminal(node.state):
            untried = self.get_untried_actions(node)
            if untried:
                return node, path
            node = self.uct_select_child(node)
            if node is None:
                break
            path.append(node)
        return node, path

    def expand(self, node):
        untried = self.get_untried_actions(node)
        if not untried:
            return node
        action = random.choice(untried)
        child = Node(node.state + action, parent=node)
        node.children[action] = child
        node.mark_dirty()
        self.state_to_node[child.state] = child
        self.tree_size += 1
        depth = len(child.state)
        if depth > self.max_depth:
            self.max_depth = depth
        return child

    def simulate(self, node):
        """Epsilon-greedy rollout to terminal."""
        state = node.state
        if len(state) >= self.min_n:
            return state

        curr_node = node
        while len(state) < self.max_n:
            valid = [a for a in self.alphabet if not any(f in state + a for f in self.forbids)]
            if not valid:
                return None

            if random.random() < self.heuristic_epsilon:
                action = random.choice(valid)
            else:
                best_q, best_a = -1.0, valid[0]
                for a in valid:
                    child = curr_node.children.get(a)
                    if child and child.visits > 0:
                        q = child.reward / child.visits
                        if q > best_q:
                            best_q, best_a = q, a
                action = best_a

            state += action
            next_node = curr_node.children.get(action)
            if next_node:
                curr_node = next_node
            else:
                break
        return state if len(state) >= self.min_n else None

    def _shape_reward(self, is_valid, msg):
        if is_valid:
            return 1.0
        if "SyntaxError" in msg:
            return 0.0
        if "NameError" in msg or "ImportError" in msg:
            return 0.1
        if "TypeError" in msg or "ValueError" in msg:
            return 0.2
        if "IndexError" in msg or "KeyError" in msg:
            return 0.25
        if "ZeroDivisionError" in msg:
            return 0.3
        return 0.0

    def backpropagate(self, node, reward, msg):
        while node is not None:
            node.visits += 1
            node.reward += reward
            node.last_reward = reward
            if not node.children and node.parent is not None:
                node.status_msg = msg
                if reward >= 1.0:
                    node.compile_status = "valid"
                elif reward == 0.5:
                    node.compile_status = "duplicate"
                elif reward == 0.0:
                    node.compile_status = "invalid"
            node = node.parent

    def step(self):
        if self.total_programs == 0 or len(self.discovered_programs) >= self.total_programs:
            return False
        if self.tree_size >= self.max_tree_size:
            return False
        if self.max_iterations > 0 and self.iterations >= self.max_iterations:
            return False
        if self.stop_on_first and len(self.discovered_programs) > 0:
            return False

        self.iterations += 1
        self.iter_timestamps.append(time.time())

        self.tree_mutex.lock()
        try:
            node, select_path = self.select()
            expanded_node = self.expand(node) if not self.is_terminal(node.state) else node
            select_path = list(select_path)
            select_path.append(expanded_node)
        finally:
            self.tree_mutex.unlock()

        terminal_state = self.simulate(expanded_node)

        reward = 0.0
        msg = "Expanding prefix..."

        if terminal_state is not None:
            if terminal_state in self.discovered_programs:
                reward = 0.5
                msg = "Valid, but duplicate (cached)"
                self.duplicates += 1
                self.log_output.emit(terminal_state, msg)
            elif terminal_state in self.failed_programs:
                msg = self.failed_programs[terminal_state]
                reward = self._shape_reward(False, msg)
                self.log_output.emit(terminal_state, "Known invalid (cached)")
            else:
                is_valid, msg, stdout_snippet = execute_and_check_compile(
                    terminal_state, self.interpreter_path, self.timeout
                )
                reward = self._shape_reward(is_valid, msg)
                if is_valid:
                    self.discovered_programs[terminal_state] = stdout_snippet
                    if reward > self.best_reward:
                        self.best_reward = reward
                        self.best_program = terminal_state
                    for c in terminal_state:
                        if c in self.char_success:
                            self.char_success[c] += 1
                    self.program_found.emit(terminal_state, stdout_snippet)
                else:
                    self.failed_programs[terminal_state] = msg
                self.log_output.emit(terminal_state, msg)

        self.tree_mutex.lock()
        try:
            self.backpropagate(expanded_node, reward, msg)
        finally:
            self.tree_mutex.unlock()

        now = time.time()
        if now - self.last_update_time > 0.2 or reward == 1.0:
            ips = self._compute_ips()
            self.update_tree.emit(self.root, select_path)
            self.update_stats.emit(
                self.iterations,
                len(self.discovered_programs),
                self.duplicates,
                (len(self.discovered_programs) / max(1, self.total_programs)) * 100,
                self.tree_size,
                self.max_depth,
                ips,
                len(self.failed_programs)
            )
            self.last_update_time = now
        return True

    def _compute_ips(self):
        if len(self.iter_timestamps) < 2:
            return 0.0
        span = self.iter_timestamps[-1] - self.iter_timestamps[0]
        if span <= 0:
            return 0.0
        return len(self.iter_timestamps) / span

    def run(self):
        try:
            while self.running:
                self._pause_mutex.lock()
                while self._paused and self.running:
                    self._pause_cond.wait(self._pause_mutex, 100)
                self._pause_mutex.unlock()

                if not self.running:
                    break
                try:
                    if not self.step():
                        break
                except Exception as e:
                    err_msg = f"{type(e).__name__}: {str(e)}"
                    self.log_output.emit("ERROR", err_msg)
                    traceback.print_exc()
        finally:
            self.update_tree.emit(self.root, [])
            self.update_stats.emit(
                self.iterations, len(self.discovered_programs), self.duplicates,
                (len(self.discovered_programs) / max(1, self.total_programs)) * 100,
                self.tree_size, self.max_depth, self._compute_ips(), len(self.failed_programs)
            )

    def stop(self):
        self.running = False
        self.wait(3000)


# ==========================================
# 3. Tree Layout Algorithm
# ==========================================
def calculate_layout(root, max_depth=None, layout_mode="h"):
    """Iterative layout to prevent recursion limits."""
    leaf_counter = [0]
    stack = [(root, False, 0)]
    
    while stack:
        node, visited, d = stack.pop()
        is_leaf = not node.children or (max_depth is not None and d >= max_depth)
        
        if not visited and not is_leaf:
            stack.append((node, True, d))
            for child in reversed(list(node.children.values())):
                stack.append((child, False, d + 1))
        else:
            if is_leaf:
                if layout_mode == "h":
                    node.layout_x = d * 220
                    node.layout_y = leaf_counter[0] * 80
                else:
                    node.layout_x = leaf_counter[0] * 120
                    node.layout_y = d * 80
                leaf_counter[0] += 1
            else:
                kids = list(node.children.values())
                if layout_mode == "h":
                    node.layout_x = d * 220
                    node.layout_y = (kids[0].layout_y + kids[-1].layout_y) / 2
                else:
                    node.layout_x = (kids[0].layout_x + kids[-1].layout_x) / 2
                    node.layout_y = d * 80
            node._layout_dirty = False
            node._child_count_at_layout = len(node.children)


def compute_best_path(root):
    path = [root]
    node = root
    while node.children:
        best = None
        best_q = -float('inf')
        for child in node.children.values():
            if child.visits == 0:
                continue
            q = child.reward / child.visits
            if q > best_q:
                best_q = q
                best = child
        if best is None:
            best = next(iter(node.children.values()))
        path.append(best)
        node = best
    return path


# ==========================================
# 4. PySide6 Graphics Items
# ==========================================
class NodeItem(QGraphicsObject):
    node_clicked = Signal(object)
    run_requested = Signal(str)

    ICONS = {
        "valid":     "✓",
        "duplicate": "≡",
        "invalid":   "✗",
        "unknown":   "?",
        "root":      "⌂",
    }

    def __init__(self, mcts_node):
        super().__init__()
        self.mcts_node = mcts_node
        self.is_active = False
        self.is_highlighted = False
        self.is_best = False
        self.width = 90
        self.height = 44
        self.color = QColor("#89b4fa")
        self._pulse_phase = 1.0
        self.setFlag(QGraphicsObject.ItemIsSelectable)
        self.setZValue(10)
        self.setAcceptHoverEvents(True)
        self._recompute()

    def set_visual_flags(self, is_active, is_highlighted, is_best):
        changed = (self.is_active != is_active or
                    self.is_highlighted != is_highlighted or
                    self.is_best != is_best)
        self.is_active = is_active
        self.is_highlighted = is_highlighted
        self.is_best = is_best
        if changed:
            self._recompute()

    def set_visual_config(self, size_mode, color_mode):
        self.size_mode = size_mode
        self.color_mode = color_mode
        self._recompute()

    def trigger_pulse(self):
        self._pulse_phase = 0.0
        self.update()

    def _recompute(self):
        self.setPos(self.mcts_node.layout_x, self.mcts_node.layout_y)
        
        size_mode = getattr(self, 'size_mode', 'By Visits')
        if size_mode == "Fixed":
            new_w, new_h = 90, 44
        elif size_mode == "By Q-Value":
            q = self.mcts_node.reward / max(1, self.mcts_node.visits)
            new_w = 70 + q * 50
            new_h = 34 + q * 25
        else:
            size_boost = min(18, self.mcts_node.visits * 0.15)
            new_w = 90 + size_boost
            new_h = 44 + size_boost * 0.5
            
        if new_w != self.width or new_h != self.height:
            self.prepareGeometryChange()
            self.width = new_w
            self.height = new_h

        state = self.mcts_node.state
        q = self.mcts_node.reward / max(1, self.mcts_node.visits)
        color_mode = getattr(self, 'color_mode', 'By Status')
        
        if self.is_best:
            self.color = QColor("#9D4EDD")
        elif self.is_active:
            self.color = QColor("#FFD700")
        elif self.is_highlighted:
            self.color = QColor("#00E5FF")
        elif color_mode == "By Depth":
            depth = len(state)
            self.color = QColor.fromHsv((depth * 25) % 360, 150, 200)
        elif color_mode == "By Q-Value":
            if q >= 1.0: self.color = QColor("#7BE495")
            elif q >= 0.5: self.color = QColor("#FFA500")
            elif q > 0.0: self.color = QColor("#FFB347")
            else: self.color = QColor("#FF6B6B")
        else:
            if not state:
                self.color = QColor("#FB7E81")
            elif self.mcts_node.compile_status == "valid":
                self.color = QColor("#7BE495")
            elif self.mcts_node.compile_status == "duplicate":
                self.color = QColor("#FFA500")
            elif self.mcts_node.compile_status == "invalid":
                self.color = QColor("#FF6B6B")
            elif (not self.mcts_node.children
                  and self.mcts_node.untried_actions is not None
                  and len(self.mcts_node.untried_actions) == 0):
                self.color = QColor("#FF6B6B")
            else:
                self.color = QColor("#89b4fa")

        if not state:
            self._icon = self.ICONS["root"]
        else:
            self._icon = self.ICONS.get(self.mcts_node.compile_status, "")

        tooltip = (f"<b>State:</b> {state or 'ROOT'}<br>"
                   f"<b>Depth:</b> {len(state)}<br>"
                   f"<b>Visits:</b> {self.mcts_node.visits}<br>"
                   f"<b>Reward:</b> {self.mcts_node.reward:.2f}<br>"
                   f"<b>Q-value:</b> {q:.3f}<br>"
                   f"<b>Status:</b> {self.mcts_node.status_msg}")
        self.setToolTip(tooltip)
        self.update()

    def boundingRect(self):
        return QRectF(-self.width / 2 - 4, -self.height / 2 - 4,
                       self.width + 8, self.height + 8)

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        rect = QRectF(-self.width / 2, -self.height / 2, self.width, self.height)

        if self._pulse_phase < 1.0:
            glow = QColor(self.color)
            glow.setAlpha(int(150 * (1 - self._pulse_phase)))
            painter.setBrush(QBrush(glow))
            painter.setPen(Qt.NoPen)
            grow = self._pulse_phase * 20
            painter.drawRoundedRect(rect.adjusted(-grow, -grow, grow, grow), 12, 12)
            self._pulse_phase += 0.05
            self.update()

        depth = len(self.mcts_node.state)
        ring_color = QColor.fromHsv((depth * 25) % 360, 120, 200)
        painter.setPen(QPen(ring_color, 2))
        painter.setBrush(QBrush(self.color))
        painter.drawRoundedRect(rect, 8, 8)

        if self.isSelected():
            painter.setPen(QPen(QColor("#3b82f6"), 3))
        elif self.is_best:
            painter.setPen(QPen(QColor("#9D4EDD"), 3))
        elif self.is_active:
            painter.setPen(QPen(QColor("#FFD700"), 3))
        else:
            painter.setPen(QPen(QColor(0, 0, 0, 80), 1))
        painter.setBrush(Qt.NoBrush)
        painter.drawRoundedRect(rect, 8, 8)

        text = self.mcts_node.state if self.mcts_node.state else "ROOT"
        if len(text) > 10:
            text = "…" + text[-9:]

        font = QFont("Segoe UI", 8, QFont.Bold)
        painter.setFont(font)
        painter.setPen(QPen(QColor("#1e1e2e") if self.color.lightness() > 128 else QColor("#ffffff")))
        text_rect = QRectF(rect.x() + 4, rect.y() + 3, rect.width() - 8, rect.height() - 16)
        painter.drawText(text_rect, Qt.AlignCenter, text)

        if self._icon:
            painter.setFont(QFont("Segoe UI", 7, QFont.Bold))
            icon_rect = QRectF(rect.right() - 14, rect.top() + 2, 12, 12)
            painter.drawText(icon_rect, Qt.AlignCenter, self._icon)

        if self.mcts_node.visits > 0:
            q = self.mcts_node.reward / self.mcts_node.visits
            painter.setFont(QFont("Consolas", 6))
            painter.setPen(QPen(QColor(60, 60, 60)))
            stats_rect = QRectF(rect.x(), rect.bottom() - 12, rect.width(), 10)
            painter.drawText(stats_rect, Qt.AlignCenter,
                             f"v={self.mcts_node.visits}  q={q:.2f}")

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.node_clicked.emit(self.mcts_node)
        super().mousePressEvent(event)

    def contextMenuEvent(self, event):
        menu = QMenu()
        act_copy = menu.addAction("📋 Copy State")
        act_run = menu.addAction("▶ Run Manually")
        act_expand = menu.addAction("🔍 Inspect")
        action = menu.exec(event.screenPos())
        
        if action == act_copy:
            QApplication.clipboard().setText(self.mcts_node.state)
        elif action == act_run:
            self.run_requested.emit(self.mcts_node.state)
        elif action == act_expand:
            self.node_clicked.emit(self.mcts_node)


class EdgeItem(QGraphicsObject):
    def __init__(self, parent_node, child_node, action):
        super().__init__()
        self.parent_node = parent_node
        self.child_node = child_node
        self.action = action
        self.color = QColor(150, 150, 150)
        self.thickness = 1.5
        self.is_active = False
        self.is_best = False
        self.is_highlighted = False
        self.setZValue(-1)

    def boundingRect(self):
        p1, p2 = self.parent_node.layout_x, self.parent_node.layout_y
        c1, c2 = self.child_node.layout_x, self.child_node.layout_y
        return QRectF(QPointF(min(p1, c1), min(p2, c2)),
                      QPointF(max(p1, c1), max(p2, c2))).normalized()

    def shape(self):
        path = QPainterPath()
        path.moveTo(self.parent_node.layout_x, self.parent_node.layout_y)
        path.lineTo(self.child_node.layout_x, self.child_node.layout_y)
        return path

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        x1, y1 = self.parent_node.layout_x, self.parent_node.layout_y
        x2, y2 = self.child_node.layout_x, self.child_node.layout_y

        dx, dy = x2 - x1, y2 - y1
        dist = max(1e-6, (dx*dx + dy*dy) ** 0.5)
        
        # Mathematically correct line-rectangle intersection
        t_x = (self.child_node.width / 2 + 4) / abs(dx) if dx != 0 else float('inf')
        t_y = (self.child_node.height / 2 + 4) / abs(dy) if dy != 0 else float('inf')
        t = min(1.0, t_x, t_y)
        x2_adj = x2 - dx * t
        y2_adj = y2 - dy * t

        pen = QPen(self.color, self.thickness)
        if self.is_active:
            pen.setStyle(Qt.DashLine)
            pen.setDashPattern([4, 3])
        pen.setCapStyle(Qt.RoundCap)
        painter.setPen(pen)
        painter.drawLine(QPointF(x1, y1), QPointF(x2_adj, y2_adj))

        if self.thickness >= 1.5:
            angle = math.atan2(dy, dx)
            arrow_size = 6 + self.thickness
            p1 = QPointF(x2_adj, y2_adj)
            p2 = QPointF(x2_adj - arrow_size * math.cos(angle - 0.4),
                         y2_adj - arrow_size * math.sin(angle - 0.4))
            p3 = QPointF(x2_adj - arrow_size * math.cos(angle + 0.4),
                         y2_adj - arrow_size * math.sin(angle + 0.4))
            painter.setBrush(QBrush(self.color))
            painter.setPen(Qt.NoPen)
            painter.drawPolygon(QPolygonF([p1, p2, p3]))


class EdgeLabel(QGraphicsTextItem):
    def __init__(self, action, x, y):
        super().__init__(action)
        self.setPos(x, y)
        self.setDefaultTextColor(QColor(80, 80, 80))
        f = QFont(); f.setPointSize(7); self.setFont(f)
        self.setZValue(5)


class GraphView(QGraphicsView):
    def __init__(self, scene):
        super().__init__(scene)
        self.setDragMode(QGraphicsView.ScrollHandDrag)
        self.setRenderHint(QPainter.Antialiasing)
        self.setBackgroundBrush(QBrush(QColor("#181825")))
        self.setCacheMode(QGraphicsView.CacheBackground)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorUnderMouse)
        self.setViewportUpdateMode(QGraphicsView.SmartViewportUpdate)
        self.placeholder = None

    def drawBackground(self, painter, rect):
        painter.fillRect(rect, QColor("#181825"))
        pen = QPen(QColor(255, 255, 255, 12), 1)
        painter.setPen(pen)
        grid = 40
        x = int(rect.left()) - (int(rect.left()) % grid)
        while x < rect.right():
            painter.drawLine(x, rect.top(), x, rect.bottom())
            x += grid
        y = int(rect.top()) - (int(rect.top()) % grid)
        while y < rect.bottom():
            painter.drawLine(rect.left(), y, rect.right(), y)
            y += grid

    def drawForeground(self, painter, rect):
        if not self.scene().items() and not self.placeholder:
            self.placeholder = QGraphicsTextItem("Search space empty. Click 'Restart MCTS Thread' to begin.")
            self.placeholder.setDefaultTextColor(QColor(150, 150, 150))
            font = QFont("Segoe UI", 14); self.placeholder.setFont(font)
            self.placeholder.setPos(50, 50)
            self.scene().addItem(self.placeholder)
        elif self.scene().items() and self.placeholder:
            self.scene().removeItem(self.placeholder)
            self.placeholder = None

    def wheelEvent(self, event):
        factor = 1.25 if event.angleDelta().y() > 0 else 1 / 1.25
        self.scale(factor, factor)


# ==========================================
# 5. Main Application Window
# ==========================================
class MainWindow(QMainWindow):
    MAX_LOG_LINES = 300

    def __init__(self):
        super().__init__()
        self.setWindowTitle("MCTS Subprocess Compiler Visualizer")
        self.resize(1600, 980)
        self.worker = None
        self.active_path_nodes = []
        self.highlighted_path = []
        self.best_path = []
        self.node_items = {}
        self.edge_items = {}
        self.edge_labels = {}
        self.settings = QSettings("MCTS", "Visualizer")
        
        self.init_ui()
        self.setup_shortcuts()
        self.load_settings()
        self.restart_mcts()
        
        self.statusBar().showMessage(
            "Space=Pause  R=Restart  F=Fit  Esc=Clear highlight  Ctrl+S=Save  Ctrl+E=Export  Ctrl+H=Help"
        )

    def init_ui(self):
        central = QWidget(); self.setCentralWidget(central)
        main_layout = QHBoxLayout(central)
        main_layout.setContentsMargins(5, 5, 5, 5)

        splitter = QSplitter(Qt.Horizontal)
        main_layout.addWidget(splitter)

        # ===== LEFT: graph + toolbar =====
        graph_container = QWidget()
        gl = QVBoxLayout(graph_container)
        gl.setContentsMargins(0, 0, 0, 0); gl.setSpacing(0)

        # --- Search & Zoom Bar ---
        search_layout = QHBoxLayout()
        search_layout.setContentsMargins(6, 4, 6, 0)
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("🔍 Search tree for state (e.g. 'print(')...")
        self.search_input.returnPressed.connect(self.search_graph)
        search_layout.addWidget(self.search_input)
        
        self.zoom_in_btn = QToolButton(); self.zoom_in_btn.setText("➕")
        self.zoom_in_btn.clicked.connect(lambda: self.view.scale(1.2, 1.2))
        self.zoom_out_btn = QToolButton(); self.zoom_out_btn.setText("➖")
        self.zoom_out_btn.clicked.connect(lambda: self.view.scale(1/1.2, 1/1.2))
        self.zoom_reset_btn = QToolButton(); self.zoom_reset_btn.setText("1:1")
        self.zoom_reset_btn.clicked.connect(lambda: self.view.resetTransform())
        
        search_layout.addWidget(self.zoom_in_btn)
        search_layout.addWidget(self.zoom_out_btn)
        search_layout.addWidget(self.zoom_reset_btn)
        gl.addLayout(search_layout)

        # --- Main Toolbar ---
        toolbar = QHBoxLayout()
        toolbar.setContentsMargins(6, 6, 6, 6)
        toolbar.setSpacing(8)

        play_group = QGroupBox("Playback")
        play_l = QHBoxLayout(play_group)
        play_l.setContentsMargins(4, 2, 4, 2); play_l.setSpacing(4)
        self.pause_btn = QPushButton("⏸")
        self.pause_btn.setFixedSize(34, 34)
        self.pause_btn.setToolTip("Pause/Resume [Space]")
        self.pause_btn.setCheckable(True)
        self.pause_btn.clicked.connect(self.toggle_timer)
        self.restart_btn2 = QPushButton("🔄")
        self.restart_btn2.setFixedSize(34, 34)
        self.restart_btn2.setToolTip("Restart [R]")
        self.restart_btn2.clicked.connect(self.restart_mcts)
        play_l.addWidget(self.pause_btn); play_l.addWidget(self.restart_btn2)
        toolbar.addWidget(play_group)

        view_group = QGroupBox("View")
        view_l = QHBoxLayout(view_group)
        view_l.setContentsMargins(4, 2, 4, 2); view_l.setSpacing(4)
        self.fit_btn = QPushButton("🔲")
        self.fit_btn.setFixedSize(34, 34)
        self.fit_btn.setToolTip("Fit View [F]")
        self.fit_btn.clicked.connect(self.fit_view)
        self.root_btn = QPushButton("⌂")
        self.root_btn.setFixedSize(34, 34)
        self.root_btn.setToolTip("Center on Root")
        self.root_btn.clicked.connect(self.center_on_root)
        view_l.addWidget(self.fit_btn); view_l.addWidget(self.root_btn)
        toolbar.addWidget(view_group)

        io_group = QGroupBox("IO")
        io_l = QHBoxLayout(io_group)
        io_l.setContentsMargins(4, 2, 4, 2); io_l.setSpacing(4)
        self.save_btn = QPushButton("💾")
        self.save_btn.setFixedSize(34, 34)
        self.save_btn.setToolTip("Save programs [Ctrl+S]")
        self.save_btn.clicked.connect(self.save_programs)
        self.export_img_btn = QPushButton("🖼️")
        self.export_img_btn.setFixedSize(34, 34)
        self.export_img_btn.setToolTip("Export tree image [Ctrl+E]")
        self.export_img_btn.clicked.connect(self.export_image)
        self.export_json_btn = QPushButton("📄")
        self.export_json_btn.setFixedSize(34, 34)
        self.export_json_btn.setToolTip("Export tree JSON")
        self.export_json_btn.clicked.connect(self.export_tree_json)
        io_l.addWidget(self.save_btn); io_l.addWidget(self.export_img_btn); io_l.addWidget(self.export_json_btn)
        toolbar.addWidget(io_group)

        toggle_group = QGroupBox("Toggles")
        toggle_l = QHBoxLayout(toggle_group)
        toggle_l.setContentsMargins(4, 2, 4, 2); toggle_l.setSpacing(8)
        self.chk_edge_labels = QCheckBox("Edge Labels")
        self.chk_edge_labels.setChecked(True)
        self.chk_edge_labels.stateChanged.connect(self.refresh_scene)
        self.chk_best_path = QCheckBox("Best Path")
        self.chk_best_path.setChecked(False)
        self.chk_best_path.stateChanged.connect(self.refresh_scene)
        self.chk_theme = QCheckBox("🌙 Dark")
        self.chk_theme.setChecked(True)
        self.chk_theme.stateChanged.connect(self.toggle_theme)
        toggle_l.addWidget(self.chk_edge_labels)
        toggle_l.addWidget(self.chk_best_path)
        toggle_l.addWidget(self.chk_theme)
        toolbar.addWidget(toggle_group)

        toolbar.addWidget(QLabel("Depth:"))
        self.spin_display_depth = QSpinBox()
        self.spin_display_depth.setRange(0, 999)
        self.spin_display_depth.setSpecialValueText("∞")
        self.spin_display_depth.setValue(0)
        self.spin_display_depth.setFixedWidth(60)
        self.spin_display_depth.valueChanged.connect(self.refresh_scene)
        toolbar.addWidget(self.spin_display_depth)

        toolbar.addStretch()

        self.legend_btn = QPushButton("Legend")
        self.legend_btn.setFixedHeight(34)
        self.legend_btn.clicked.connect(self.show_legend_popup)
        toolbar.addWidget(self.legend_btn)

        gl.addLayout(toolbar)

        self.scene = QGraphicsScene(self)
        self.view = GraphView(self.scene)
        gl.addWidget(self.view)
        splitter.addWidget(graph_container)

        # ===== RIGHT: controls =====
        right = QWidget()
        right.setMinimumWidth(360)
        right.setMaximumWidth(600)
        rl = QVBoxLayout(right)
        splitter.addWidget(right)

        # --- Settings ---
        sg = QGroupBox("Environment Settings")
        sl = QVBoxLayout(sg)
        sl.addWidget(QLabel("Alphabet (comma-separated):"))
        self.input_alphabet = QLineEdit('p,r,i,n,t,(,",H,)')
        sl.addWidget(self.input_alphabet)
        
        len_layout = QHBoxLayout()
        len_layout.addWidget(QLabel("Min Length:"))
        self.input_min_n = QSpinBox()
        self.input_min_n.setRange(1, 100)
        self.input_min_n.setValue(11)
        len_layout.addWidget(self.input_min_n)
        
        len_layout.addWidget(QLabel("Max Length:"))
        self.input_max_n = QSpinBox()
        self.input_max_n.setRange(1, 100)
        self.input_max_n.setValue(11)
        len_layout.addWidget(self.input_max_n)
        sl.addLayout(len_layout)

        sl.addWidget(QLabel("Local Pruning (substrings, comma-separated):"))
        self.input_forbid = QLineEdit("((,))")
        sl.addWidget(self.input_forbid)

        iter_layout = QHBoxLayout()
        iter_layout.addWidget(QLabel("Max Iterations (0=∞):"))
        self.input_max_iters = QSpinBox()
        self.input_max_iters.setRange(0, 100_000_000)
        self.input_max_iters.setValue(0)
        iter_layout.addWidget(self.input_max_iters)
        sl.addLayout(iter_layout)

        self.chk_stop_first = QCheckBox("Stop search after finding first valid program")
        sl.addWidget(self.chk_stop_first)

        adv = QFormLayout()
        self.spin_explore = QDoubleSpinBox()
        self.spin_explore.setRange(0.0, 5.0); self.spin_explore.setSingleStep(0.1)
        self.spin_explore.setValue(1.414)
        self.spin_explore.valueChanged.connect(self.apply_dynamic_options)
        adv.addRow("Exploration (c):", self.spin_explore)
        
        self.spin_timeout = QDoubleSpinBox()
        self.spin_timeout.setRange(0.1, 10.0); self.spin_timeout.setSingleStep(0.1)
        self.spin_timeout.setValue(1.0); self.spin_timeout.setSuffix(" s")
        adv.addRow("Subprocess timeout:", self.spin_timeout)
        
        self.spin_max_tree = QSpinBox()
        self.spin_max_tree.setRange(100, 1_000_000)
        self.spin_max_tree.setSingleStep(1000); self.spin_max_tree.setValue(20000)
        adv.addRow("Max tree nodes:", self.spin_max_tree)
        
        self.spin_heuristic = QDoubleSpinBox()
        self.spin_heuristic.setRange(0.0, 1.0); self.spin_heuristic.setSingleStep(0.05)
        self.spin_heuristic.setValue(0.15)
        self.spin_heuristic.valueChanged.connect(self.apply_dynamic_options)
        adv.addRow("Heuristic ε (rollout):", self.spin_heuristic)
        sl.addLayout(adv)

        self.restart_btn = QPushButton("🔄 Restart MCTS Thread")
        self.restart_btn.clicked.connect(self.restart_mcts)
        sl.addWidget(self.restart_btn)
        rl.addWidget(sg)

        # --- Advanced Options ---
        og = QGroupBox("⚙ Advanced Options")
        ol = QVBoxLayout(og)
        
        dyn_form = QFormLayout()
        self.chk_dynamic_c = QCheckBox("Allow live changes to Exploration (c)")
        self.chk_dynamic_c.setChecked(True)
        self.chk_dynamic_c.stateChanged.connect(self.apply_dynamic_options)
        dyn_form.addRow("Dynamic c:", self.chk_dynamic_c)
        
        self.chk_dynamic_heur = QCheckBox("Allow live changes to Heuristic (ε)")
        self.chk_dynamic_heur.setChecked(True)
        self.chk_dynamic_heur.stateChanged.connect(self.apply_dynamic_options)
        dyn_form.addRow("Dynamic ε:", self.chk_dynamic_heur)
        ol.addLayout(dyn_form)

        interp_layout = QHBoxLayout()
        self.input_interp = QLineEdit(sys.executable)
        self.btn_browse_interp = QPushButton("...")
        self.btn_browse_interp.setFixedWidth(30)
        self.btn_browse_interp.clicked.connect(self.browse_interpreter)
        interp_layout.addWidget(self.input_interp)
        interp_layout.addWidget(self.btn_browse_interp)
        ol.addWidget(QLabel("Python Interpreter:"))
        ol.addLayout(interp_layout)
        
        vis_form = QFormLayout()
        self.combo_layout = QComboBox()
        self.combo_layout.addItems(["Horizontal (L→R)", "Vertical (T→B)"])
        self.combo_layout.currentIndexChanged.connect(self.refresh_scene)
        vis_form.addRow("Layout Mode:", self.combo_layout)
        
        self.combo_node_size = QComboBox()
        self.combo_node_size.addItems(["By Visits", "By Q-Value", "Fixed"])
        self.combo_node_size.currentIndexChanged.connect(self.refresh_scene)
        vis_form.addRow("Node Size:", self.combo_node_size)
        
        self.combo_node_color = QComboBox()
        self.combo_node_color.addItems(["By Status", "By Q-Value", "By Depth"])
        self.combo_node_color.currentIndexChanged.connect(self.refresh_scene)
        vis_form.addRow("Node Color:", self.combo_node_color)
        ol.addLayout(vis_form)
        rl.addWidget(og)

        # --- Telemetry ---
        tg = QGroupBox("📊 Search Telemetry")
        tf = QFormLayout(tg)
        tf.setSpacing(6)

        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setFormat("%p%  of search space explored")
        self.progress_bar.setStyleSheet("""
            QProgressBar { background-color: #313244; border: 1px solid #45475a; border-radius: 4px; text-align: center; color: #cdd6f4; height: 18px; }
            QProgressBar::chunk { background-color: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #89b4fa, stop:1 #a6e3a1); border-radius: 3px; }
        """)
        tf.addRow(self.progress_bar)

        stats_row = QHBoxLayout()
        stats_row.setSpacing(6)
        self.pill_iters = self._make_pill("🌀", "0", "#89b4fa")
        self.pill_found  = self._make_pill("✓", "0", "#a6e3a1")
        self.pill_failed = self._make_pill("✗", "0", "#f38ba8")
        self.pill_dups   = self._make_pill("≡", "0", "#fab387")
        for pill in (self.pill_iters, self.pill_found, self.pill_failed, self.pill_dups):
            stats_row.addWidget(pill)
        stats_wrap = QWidget(); stats_wrap.setLayout(stats_row)
        tf.addRow(stats_wrap)

        self.lbl_tree_size = QLabel("1")
        self.lbl_max_depth = QLabel("0")
        self.lbl_ips = QLabel("0.0 it/s")
        tf.addRow("🌳 Tree Nodes:", self.lbl_tree_size)
        tf.addRow("📏 Max Depth:", self.lbl_max_depth)
        tf.addRow("⚡ Speed:", self.lbl_ips)

        best_row = QHBoxLayout()
        self.lbl_best = QLabel("(none)")
        self.lbl_best.setStyleSheet("color:#a6e3a1; font-family: monospace; font-weight: bold;")
        self.lbl_best.setWordWrap(True)
        self.copy_best_btn = QPushButton("📋")
        self.copy_best_btn.setFixedSize(28, 28)
        self.copy_best_btn.setToolTip("Copy best program")
        self.copy_best_btn.clicked.connect(self.copy_best_program)
        best_row.addWidget(self.lbl_best, 1)
        best_row.addWidget(self.copy_best_btn, 0)
        tf.addRow("🏆 Best:", best_row)
        rl.addWidget(tg)

        # --- Node inspector ---
        ng = QGroupBox("Node Inspector (Click or Hover a Node)")
        nf = QFormLayout(ng)
        self.lbl_state = QLabel("N/A")
        self.lbl_depth = QLabel("0")
        self.lbl_visits = QLabel("0")
        self.lbl_reward = QLabel("0.0")
        self.lbl_qvalue = QLabel("0.0")
        self.lbl_status = QLabel("N/A")
        self.lbl_children = QLabel("0")
        self.lbl_untried = QLabel("N/A")
        nf.addRow("String State:", self.lbl_state)
        nf.addRow("Depth:", self.lbl_depth)
        nf.addRow("Visits:", self.lbl_visits)
        nf.addRow("Total Reward:", self.lbl_reward)
        nf.addRow("Avg Reward (Q):", self.lbl_qvalue)
        nf.addRow("Compile/Run Status:", self.lbl_status)
        nf.addRow("Children:", self.lbl_children)
        nf.addRow("Untried Actions:", self.lbl_untried)
        rl.addWidget(ng)

        # --- Discovered programs ---
        pg = QGroupBox("Discovered Valid Programs")
        pl = QVBoxLayout(pg)
        search_layout_p = QHBoxLayout()
        search_layout_p.addWidget(QLabel("Filter:"))
        self.input_filter = QLineEdit()
        self.input_filter.setPlaceholderText("substring filter...")
        self.input_filter.textChanged.connect(self.filter_programs)
        search_layout_p.addWidget(self.input_filter)
        pl.addLayout(search_layout_p)
        self.list_programs = QListWidget()
        self.list_programs.setContextMenuPolicy(Qt.CustomContextMenu)
        self.list_programs.customContextMenuRequested.connect(self.show_program_menu)
        self.list_programs.itemClicked.connect(self.on_program_clicked)
        pl.addWidget(self.list_programs)
        rl.addWidget(pg)

        # --- Log ---
        lg = QGroupBox("📜 Subprocess Output Log")
        ll = QVBoxLayout(lg)
        
        self.log_console = QPlainTextEdit()
        self.log_console.setMaximumBlockCount(self.MAX_LOG_LINES)
        self.log_console.setReadOnly(True)
        self.log_console.setMinimumHeight(140)

        log_toolbar = QHBoxLayout()
        log_toolbar.addWidget(QLabel("Filter:"))
        self.input_log_filter = QLineEdit()
        self.input_log_filter.setPlaceholderText("e.g. valid, error, duplicate...")
        log_toolbar.addWidget(self.input_log_filter)
        log_toolbar.addStretch()
        self.chk_autoscroll = QCheckBox("Auto-scroll")
        self.chk_autoscroll.setChecked(True)
        log_toolbar.addWidget(self.chk_autoscroll)
        self.btn_clear_log = QPushButton("Clear")
        self.btn_clear_log.setFixedHeight(24)
        self.btn_clear_log.clicked.connect(self.log_console.clear)
        log_toolbar.addWidget(self.btn_clear_log)
        
        ll.addLayout(log_toolbar)
        ll.addWidget(self.log_console)
        rl.addWidget(lg)
        rl.addStretch()

    def _make_pill(self, icon, value, color):
        w = QWidget()
        h = QHBoxLayout(w); h.setContentsMargins(6, 4, 6, 4); h.setSpacing(4)
        w.setStyleSheet(f"background-color: {color}22; border: 1px solid {color}; border-radius: 12px;")
        icon_lbl = QLabel(icon)
        val_lbl = QLabel(value)
        val_lbl.setStyleSheet(f"color: {color}; font-weight: bold; font-family: monospace;")
        val_lbl.setObjectName("value")
        h.addWidget(icon_lbl); h.addWidget(val_lbl)
        w.value_label = val_lbl
        return w

    def setup_shortcuts(self):
        for key, slot in [
            ("Space",   self.toggle_timer),
            ("R",       self.restart_mcts),
            ("F",       self.fit_view),
            ("Escape",  self.clear_highlight),
            ("Ctrl+S",  self.save_programs),
            ("Ctrl+H",  self.show_about),
            ("Ctrl+E",  self.export_image),
        ]:
            sc = QShortcut(QKeySequence(key), self)
            sc.activated.connect(slot)

    def load_settings(self):
        self.input_alphabet.setText(self.settings.value("alphabet", 'p,r,i,n,t,(,",H,)'))
        self.input_min_n.setValue(int(self.settings.value("min_n", 11)))
        self.input_max_n.setValue(int(self.settings.value("max_n", 11)))
        self.input_forbid.setText(self.settings.value("forbids", "((,))"))
        self.input_interp.setText(self.settings.value("interpreter", sys.executable))
        self.spin_explore.setValue(float(self.settings.value("explore", 1.414)))
        self.spin_timeout.setValue(float(self.settings.value("timeout", 1.0)))
        self.spin_max_tree.setValue(int(self.settings.value("max_tree", 20000)))
        self.spin_heuristic.setValue(float(self.settings.value("heuristic", 0.15)))
        self.input_max_iters.setValue(int(self.settings.value("max_iters", 0)))
        self.chk_stop_first.setChecked(self.settings.value("stop_first", False, type=bool))
        
        is_dark = self.settings.value("dark_mode", True, type=bool)
        self.chk_theme.setChecked(is_dark)
        self.toggle_theme()

    def save_settings(self):
        self.settings.setValue("alphabet", self.input_alphabet.text())
        self.settings.setValue("min_n", self.input_min_n.value())
        self.settings.setValue("max_n", self.input_max_n.value())
        self.settings.setValue("forbids", self.input_forbid.text())
        self.settings.setValue("interpreter", self.input_interp.text())
        self.settings.setValue("explore", self.spin_explore.value())
        self.settings.setValue("timeout", self.spin_timeout.value())
        self.settings.setValue("max_tree", self.spin_max_tree.value())
        self.settings.setValue("heuristic", self.spin_heuristic.value())
        self.settings.setValue("max_iters", self.input_max_iters.value())
        self.settings.setValue("stop_first", self.chk_stop_first.isChecked())
        self.settings.setValue("dark_mode", self.chk_theme.isChecked())

    def browse_interpreter(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Python Interpreter", "", "Python Executable (python*.exe);;All Files (*)")
        if path:
            self.input_interp.setText(path)

    def apply_dynamic_options(self):
        if not self.worker: return
        if self.chk_dynamic_c.isChecked():
            self.worker.exploration = self.spin_explore.value()
        if self.chk_dynamic_heur.isChecked():
            self.worker.heuristic_epsilon = self.spin_heuristic.value()

    def toggle_theme(self):
        if self.chk_theme.isChecked():
            QApplication.instance().setStyleSheet(DARK_QSS)
            self.chk_theme.setText("🌙 Dark")
        else:
            QApplication.instance().setStyleSheet(LIGHT_QSS)
            self.chk_theme.setText("☀️ Light")

    def center_on_root(self):
        if self.worker:
            self.view.centerOn(self.worker.root.layout_x, self.worker.root.layout_y)
            self.view.scale(1.5, 1.5)

    def export_image(self):
        if not self.scene.items():
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export Tree Image", "tree.png", "PNG (*.png)")
        if not path:
            return
        rect = self.scene.itemsBoundingRect().adjusted(-20, -20, 20, 20)
        img = QImage(int(rect.width()), int(rect.height()), QImage.Format_ARGB32)
        img.fill(Qt.white)
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing)
        self.scene.render(p, QRectF(img.rect()), rect)
        p.end()
        img.save(path)
        self.statusBar().showMessage(f"Image saved: {path}", 3000)

    def export_tree_json(self):
        if not self.worker: return
        path, _ = QFileDialog.getSaveFileName(self, "Export Tree JSON", "tree.json", "JSON (*.json)")
        if not path: return
        self.worker.tree_mutex.lock()
        try:
            def serialize(node):
                return {
                    "state": node.state,
                    "visits": node.visits,
                    "reward": node.reward,
                    "status": node.compile_status,
                    "children": [serialize(c) for c in node.children.values()]
                }
            data = serialize(self.worker.root)
            with open(path, 'w') as f:
                json.dump(data, f, indent=2)
            self.statusBar().showMessage(f"Tree JSON exported: {path}", 3000)
        finally:
            self.worker.tree_mutex.unlock()

    def show_legend_popup(self):
        QMessageBox.information(self, "Legend", (
            "<table cellpadding=4>"
            "<tr><td><b>⌂ ROOT</b></td><td>Start state (empty string)</td></tr>"
            "<tr><td bgcolor=#7BE495>● Valid</td><td>Program compiled & ran successfully</td></tr>"
            "<tr><td bgcolor=#FFA500>● Duplicate</td><td>Already discovered</td></tr>"
            "<tr><td bgcolor=#FF6B6B>● Invalid</td><td>Failed to compile</td></tr>"
            "<tr><td bgcolor=#FFD700>● Active</td><td>Currently being explored</td></tr>"
            "<tr><td bgcolor=#9D4EDD>● Best</td><td>On best-Q path</td></tr>"
            "<tr><td bgcolor=#89b4fa>● Frontier</td><td>Not yet expanded</td></tr>"
            "</table><br>"
            "<b>Edge colors:</b><br>"
            "Green = high Q, Orange = mid Q, Red = low Q, Gold = active, Purple = best path"
        ))

    def search_graph(self):
        if not self.worker: return
        target = self.search_input.text().strip()
        if not target: return
        
        self.worker.tree_mutex.lock()
        try:
            best_node = None
            # 1. Exact prefix match
            for i in range(len(target), 0, -1):
                node = self.worker.state_to_node.get(target[:i])
                if node:
                    best_node = node
                    break
            # 2. Fallback to substring search across all known tree states
            if not best_node:
                for state, node in self.worker.state_to_node.items():
                    if target in state:
                        best_node = node
                        break
            if not best_node:
                self.statusBar().showMessage(f"No node containing '{target}'", 3000)
                return
                
            self.highlighted_path = []
            curr = best_node
            while curr:
                self.highlighted_path.insert(0, curr)
                curr = curr.parent
                
            self.view.centerOn(best_node.layout_x, best_node.layout_y)
            self.view.resetTransform()
            self.view.scale(1.2, 1.2)
        finally:
            self.worker.tree_mutex.unlock()
        self.refresh_scene()

    # ---------- worker lifecycle ----------
    def restart_mcts(self):
        if self.worker and self.worker.isRunning():
            self.worker.running = False
            self.worker.resume()
            self.worker.wait(2000)

        alphabet = [a.strip() for a in self.input_alphabet.text().split(",") if a.strip()]
        min_n = self.input_min_n.value()
        max_n = self.input_max_n.value()
        if min_n > max_n: 
            min_n, max_n = max_n, min_n
            
        max_iters = self.input_max_iters.value()
        forbids = [f.strip() for f in self.input_forbid.text().split(",") if f.strip()]
        
        self.worker = MCTSWorker(
            alphabet, min_n, max_n, forbids,
            exploration=self.spin_explore.value(),
            timeout=self.spin_timeout.value(),
            max_tree_size=self.spin_max_tree.value(),
            heuristic_epsilon=self.spin_heuristic.value(),
            interpreter_path=self.input_interp.text().strip() or None,
            max_iterations=max_iters,
            stop_on_first=self.chk_stop_first.isChecked()
        )
        self.worker.update_tree.connect(self.on_update_tree)
        self.worker.update_stats.connect(self.on_update_stats)
        self.worker.program_found.connect(self.on_program_found)
        self.worker.log_output.connect(self.on_log_output)

        self.list_programs.clear()
        self.log_console.clear()
        self.active_path_nodes = []
        self.highlighted_path = []
        self.best_path = []

        for item in self.node_items.values():
            self.scene.removeItem(item)
        self.node_items.clear()
        for item in self.edge_items.values():
            self.scene.removeItem(item)
        self.edge_items.clear()
        for item in self.edge_labels.values():
            self.scene.removeItem(item)
        self.edge_labels.clear()

        self.update_scene(self.worker.root, [])
        self.fit_view()
        self.worker.start()
        self.pause_btn.setChecked(False)
        self.pause_btn.setText("⏸")

    def toggle_timer(self):
        if not self.worker:
            return
        if self.worker.isRunning() and not self.worker.is_paused():
            self.worker.pause()
            self.pause_btn.setChecked(True)
            self.pause_btn.setText("▶")
        else:
            self.worker.running = True
            self.worker.resume()
            if not self.worker.isRunning():
                self.worker.start()
            self.pause_btn.setChecked(False)
            self.pause_btn.setText("⏸")

    def clear_highlight(self):
        self.highlighted_path = []
        self.refresh_scene()

    def refresh_scene(self):
        if self.worker:
            self.update_scene(self.worker.root, self.active_path_nodes)

    # ---------- signal handlers ----------
    def on_update_tree(self, root, path):
        self.active_path_nodes = path or []
        self.update_scene(root, self.active_path_nodes)

    def on_update_stats(self, iters, found, dups, progress, tree_size, max_depth, ips, failed):
        self.pill_iters.value_label.setText(str(iters))
        self.pill_found.value_label.setText(str(found))
        self.pill_failed.value_label.setText(str(failed))
        self.pill_dups.value_label.setText(str(dups))
        
        if self.worker and self.worker.total_programs > 1_000_000:
            self.progress_bar.setFormat(f"{found} programs found")
            self.progress_bar.setValue(min(100, found))
        else:
            self.progress_bar.setFormat("%p% of search space")
            self.progress_bar.setValue(int(progress))
            
        self.lbl_tree_size.setText(str(tree_size))
        self.lbl_max_depth.setText(str(max_depth))
        self.lbl_ips.setText(f"{ips:.1f} it/s")
        if self.worker and self.worker.best_program:
            self.lbl_best.setText(f'"{self.worker.best_program}"')

    def on_program_found(self, program, stdout):
        item = QListWidgetItem(program)
        if stdout:
            item.setToolTip(f"stdout: {stdout}")
        self.list_programs.addItem(item)
        if self.chk_autoscroll.isChecked():
            self.list_programs.scrollToBottom()
            
        if self.worker:
            node = self.worker.state_to_node.get(program)
            if node:
                item_nid = id(node)
                if item_nid in self.node_items:
                    self.node_items[item_nid].trigger_pulse()

    def on_log_output(self, program, message):
        if "OK" in message or "Still running" in message:
            color = "#7BE495"
        elif "duplicate" in message.lower():
            color = "#FFA500"
        elif "invalid" in message.lower() or "Error" in message or "Timeout" in message:
            color = "#FF6B6B"
        else:
            color = "#97C2FC"
        self.log_console.appendHtml(
            f'<span style="color:{color}"><b>{program}</b> → <i>{message}</i></span>'
        )

    # ---------- scene rendering (cached) ----------
    def update_scene(self, root, active_path):
        if not self.worker:
            return
        show_edges = self.chk_edge_labels.isChecked()
        max_display_depth = self.spin_display_depth.value()
        show_best = self.chk_best_path.isChecked()

        self.worker.tree_mutex.lock()
        try:
            layout_mode = "h" if self.combo_layout.currentText().startswith("Horizontal") else "v"
            size_mode = self.combo_node_size.currentText()
            color_mode = self.combo_node_color.currentText()

            calculate_layout(root, max_depth=max_display_depth or None, layout_mode=layout_mode)

            if show_best:
                self.best_path = compute_best_path(root)
            else:
                self.best_path = []

            highlight_set = set(id(n) for n in self.highlighted_path)
            active_set = set(id(n) for n in active_path)
            best_set = set(id(n) for n in self.best_path)
            best_program = self.worker.best_program

            visible_edge_keys = set()

            q = deque([root])
            while q:
                parent = q.popleft()
                if max_display_depth and len(parent.state) >= max_display_depth:
                    continue
                for action, child in parent.children.items():
                    edge_key = (id(parent), id(child))
                    visible_edge_keys.add(edge_key)

                    thickness = 1 + min(6, child.visits * 0.05)
                    color = QColor(180, 180, 180)
                    if id(child) in active_set:
                        color = QColor(255, 215, 0); thickness = 4
                    elif id(child) in highlight_set:
                        color = QColor(0, 229, 255); thickness = 3
                    elif id(child) in best_set:
                        color = QColor(157, 78, 221); thickness = 3
                    elif child.visits > 0:
                        qv = child.reward / child.visits
                        if   qv >= 1.0: color = QColor(123, 228, 149)
                        elif qv >= 0.5: color = QColor(255, 165,   0)
                        elif qv >  0.0: color = QColor(255, 200, 100)
                        else:           color = QColor(255, 107, 107)

                    if edge_key in self.edge_items:
                        edge = self.edge_items[edge_key]
                        edge.color = color
                        edge.thickness = thickness
                        edge.is_active = id(child) in active_set
                        edge.is_best = id(child) in best_set
                        edge.is_highlighted = id(child) in highlight_set
                        edge.update()
                    else:
                        edge = EdgeItem(parent, child, action)
                        edge.color = color
                        edge.thickness = thickness
                        edge.is_active = id(child) in active_set
                        edge.is_best = id(child) in best_set
                        edge.is_highlighted = id(child) in highlight_set
                        self.scene.addItem(edge)
                        self.edge_items[edge_key] = edge

                    mx = (parent.layout_x + child.layout_x) / 2
                    my = (parent.layout_y + child.layout_y) / 2
                    if show_edges:
                        if edge_key in self.edge_labels:
                            lbl = self.edge_labels[edge_key]
                            lbl.setPos(mx, my)
                            lbl.setVisible(True)
                        else:
                            lbl = EdgeLabel(action, mx, my)
                            self.scene.addItem(lbl)
                            self.edge_labels[edge_key] = lbl
                    elif edge_key in self.edge_labels:
                        self.edge_labels[edge_key].setVisible(False)

                    q.append(child)

            stale_edges = set(self.edge_items.keys()) - visible_edge_keys
            for key in stale_edges:
                self.scene.removeItem(self.edge_items.pop(key))
                if key in self.edge_labels:
                    self.scene.removeItem(self.edge_labels.pop(key))

            visible_ids = set()
            q = deque([root])
            while q:
                node = q.popleft()
                nid = id(node)
                visible_ids.add(nid)
                is_active = nid in active_set
                is_high = nid in highlight_set
                is_best = (best_program is not None and node.state == best_program
                           or nid in best_set)

                if nid in self.node_items:
                    item = self.node_items[nid]
                    item.set_visual_flags(is_active, is_high, is_best)
                    item.set_visual_config(size_mode, color_mode)
                    item._recompute()
                else:
                    item = NodeItem(node)
                    item.set_visual_flags(is_active, is_high, is_best)
                    item.set_visual_config(size_mode, color_mode)
                    item.node_clicked.connect(self.on_node_clicked)
                    item.run_requested.connect(self.manual_run_program)
                    self.scene.addItem(item)
                    self.node_items[nid] = item

                if not (max_display_depth and len(node.state) >= max_display_depth):
                    for child in node.children.values():
                        q.append(child)

            stale = set(self.node_items.keys()) - visible_ids
            for nid in stale:
                item = self.node_items.pop(nid)
                self.scene.removeItem(item)
        finally:
            self.worker.tree_mutex.unlock()

    def on_node_clicked(self, mcts_node):
        if not self.worker:
            return
        self.worker.tree_mutex.lock()
        try:
            state = mcts_node.state
            self.lbl_state.setText(f"'{state}'" if state else "ROOT (Empty)")
            self.lbl_depth.setText(str(len(state)))
            self.lbl_visits.setText(str(mcts_node.visits))
            self.lbl_reward.setText(f"{mcts_node.reward:.2f}")
            q = mcts_node.reward / mcts_node.visits if mcts_node.visits > 0 else 0.0
            self.lbl_qvalue.setText(f"{q:.3f}")
            self.lbl_status.setText(mcts_node.status_msg)
            self.lbl_children.setText(str(len(mcts_node.children)))
            untried = mcts_node.untried_actions
            self.lbl_untried.setText(", ".join(untried) if untried else "None")

            self.highlighted_path = []
            curr = mcts_node
            while curr:
                self.highlighted_path.insert(0, curr)
                curr = curr.parent
        finally:
            self.worker.tree_mutex.unlock()
        self.update_scene(self.worker.root, self.active_path_nodes)

    def on_program_clicked(self, item):
        if not self.worker:
            return
        target_str = item.text()
        self.worker.tree_mutex.lock()
        try:
            self.highlighted_path = []
            node = None
            for i in range(len(target_str), 0, -1):
                node = self.worker.state_to_node.get(target_str[:i])
                if node:
                    break
            if not node:
                node = self.worker.root
            curr = node
            while curr:
                self.highlighted_path.insert(0, curr)
                curr = curr.parent
        finally:
            self.worker.tree_mutex.unlock()
        self.update_scene(self.worker.root, self.active_path_nodes)

    def manual_run_program(self, program):
        if not program: return
        is_valid, msg, stdout = execute_and_check_compile(program, self.input_interp.text().strip(), 3.0)
        self.on_log_output(program, f"Manual run: {msg}")
        if stdout:
            self.on_log_output(program, f"stdout: {stdout}")
        QMessageBox.information(self, "Manual Run Result", f"Program:\n{program}\n\nResult: {msg}\n\nStdout:\n{stdout}")

    # ---------- program list helpers ----------
    def filter_programs(self, text):
        for i in range(self.list_programs.count()):
            item = self.list_programs.item(i)
            item.setHidden(text.lower() not in item.text().lower())

    def show_program_menu(self, pos):
        item = self.list_programs.itemAt(pos)
        if not item:
            return
        menu = QMenu(self)
        act_copy = menu.addAction("📋 Copy Program")
        act_run = menu.addAction("▶ Run in Terminal (log)")
        action = menu.exec(self.list_programs.mapToGlobal(pos))
        if action == act_copy:
            QApplication.clipboard().setText(item.text())
            self.statusBar().showMessage(f"Copied: {item.text()}", 2000)
        elif action == act_run:
            prog = item.text()
            is_valid, msg, stdout = execute_and_check_compile(prog, self.input_interp.text().strip(), 3.0)
            self.on_log_output(prog, f"Manual run: {msg}")
            if stdout:
                self.on_log_output(prog, f"stdout: {stdout}")

    def copy_best_program(self):
        if self.worker and self.worker.best_program:
            QApplication.clipboard().setText(self.worker.best_program)
            self.statusBar().showMessage("Copied best program to clipboard", 2000)

    # ---------- misc ----------
    def save_programs(self):
        if not self.worker or not self.worker.discovered_programs:
            return
        path, _ = QFileDialog.getSaveFileName(
            self, "Save Programs", "programs.txt", "Text Files (*.txt)")
        if not path:
            return
        try:
            with open(path, 'w') as f:
                for p in sorted(self.worker.discovered_programs.keys()):
                    stdout = self.worker.discovered_programs.get(p, "")
                    f.write(p)
                    if stdout:
                        f.write(f"  # → {stdout}")
                    f.write("\n")
        except Exception as e:
            self.on_log_output("SAVE", f"Save failed: {e}")

    def show_about(self):
        QMessageBox.information(self, "About", (
            "<h3>MCTS Subprocess Compiler Visualizer</h3>"
            "<p>Monte Carlo Tree Search that explores random programs and "
            "validates them by running <code>sys.executable</code> as a subprocess.</p>"
            "<p><b>Shortcuts:</b></p>"
            "<ul>"
            "<li><b>Space</b> — Pause / Resume the search</li>"
            "<li><b>R</b> — Restart with current settings</li>"
            "<li><b>F</b> — Fit view to tree</li>"
            "<li><b>Esc</b> — Clear highlight</li>"
            "<li><b>Ctrl+S</b> — Save discovered programs</li>"
            "<li><b>Ctrl+E</b> — Export tree as image</li>"
            "<li><b>Ctrl+H</b> — This help</li>"
            "</ul>"
            "<p><b>Interactions:</b></p>"
            "<ul>"
            "<li>Click a node → inspect &amp; highlight root→node path</li>"
            "<li>Right-click a node → copy or manually re-run</li>"
            "<li>Click a discovered program → highlight longest tree prefix</li>"
            "<li>Mouse wheel → zoom (anchored at cursor)</li>"
            "<li>Middle-drag / Left-drag → pan</li>"
            "</ul>"
        ))

    def fit_view(self):
        rect = self.scene.itemsBoundingRect()
        if not rect.isNull():
            self.view.fitInView(rect, Qt.KeepAspectRatio)

    def closeEvent(self, event):
        self.save_settings()
        if self.worker:
            self.worker.running = False
            self.worker.resume()  # Wake up if paused
            if self.worker.isRunning():
                if not self.worker.wait(3000):
                    self.worker.terminate()
                    self.worker.wait(1000)
        event.accept()


# ==========================================
# 6. Execution
# ==========================================
if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(DARK_QSS)
    w = MainWindow()
    w.show()
    sys.exit(app.exec())