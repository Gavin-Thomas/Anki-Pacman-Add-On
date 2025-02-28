# __init__.py - Main file for the Anki-Pacman add-on

import os
import random
import time
import math
import json
from typing import List, Tuple, Optional, Dict, Any, Callable

from aqt import mw
from aqt.utils import showInfo, qconnect, tooltip
from aqt.qt import *
from anki.cards import Card

# Constants for the game
CELL_SIZE = 30
GRID_WIDTH = 19
GRID_HEIGHT = 22
GAME_WIDTH = CELL_SIZE * GRID_WIDTH
GAME_HEIGHT = CELL_SIZE * GRID_HEIGHT

# Directions
UP = (0, -1)
DOWN = (0, 1)
LEFT = (-1, 0)
RIGHT = (1, 0)

# Game state constants
GAME_STOPPED = 0
GAME_RUNNING = 1
GAME_PAUSED = 2
GAME_OVER = 3

# Colors
WALL_COLOR = QColor(0, 0, 139)  # Deep blue for walls
BACKGROUND_COLOR = QColor(0, 0, 0)  # Black background
PACMAN_COLOR = QColor(255, 255, 0)  # Yellow for Pacman
DOT_COLOR = QColor(255, 255, 255)  # White for dots
TEXT_COLOR = QColor(255, 255, 255)  # White for text
POWER_PELLET_COLOR = QColor(255, 255, 255)  # White for power pellets
GHOST_COLORS = [
    QColor(255, 0, 0),      # Red (Blinky)
    QColor(255, 184, 255),  # Pink (Pinky) 
    QColor(0, 255, 255),    # Cyan (Inky)
    QColor(255, 184, 82)    # Orange (Clyde)
]
GHOST_FRIGHTENED_COLOR = QColor(0, 0, 255)  # Blue for frightened ghosts
GHOST_EYES_COLOR = QColor(255, 255, 255)  # White for ghost eyes
GHOST_PUPILS_COLOR = QColor(0, 0, 255)    # Blue for ghost pupils

# Quota and game settings
# Store in user_files folder to persist across add-on updates
ADDON_DIR = os.path.dirname(__file__)
USER_FILES_DIR = os.path.join(ADDON_DIR, "user_files")
SETTINGS_FILE = os.path.join(USER_FILES_DIR, "pacman_settings.json")

# Create user_files folder if it doesn't exist
if not os.path.exists(USER_FILES_DIR):
    os.makedirs(USER_FILES_DIR)

# Default settings
DEFAULT_SETTINGS = {
    "high_score": 0,
    "cards_quota": 0,
    "cards_completed": 0,
    "last_game_score": 0,
    "can_play": True,
    "selected_deck_id": None
}

# Global reference to the main dialog to prevent it from being garbage collected
pacman_dialog = None

# Pacman game class
class PacmanGame(QWidget):
    def __init__(self, parent=None, on_game_over=None):
        super().__init__(parent)
        self.setFixedSize(GAME_WIDTH, GAME_HEIGHT)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        
        # Set up double buffering for smoother graphics
        self.setAutoFillBackground(False)
        
        # Load the maze layout
        self.maze = self._create_maze()
        
        # Load settings
        self.settings = self._load_settings()
        
        # Game state
        self.state = GAME_STOPPED
        self.score = 0
        self.high_score = self.settings["high_score"]
        self.lives = 3
        self.dots_left = self._count_dots()
        self.fps = 45  # Reduced FPS for more manageable game speed (was 60)
        
        # Initialize Pacman position and direction
        self.pacman_pos = (9, 15)  # Starting position
        self.pacman_prev_pos = (9, 15)  # Track previous position for collision detection
        self.pacman_dir = LEFT
        self.pacman_next_dir = LEFT
        self.pacman_anim_frame = 0
        
        # Animation timing
        self.anim_counter = 0
        self.anim_speed = 0.5  # Speed multiplier
        
        # Power pellet state
        self.power_pellet_active = False
        self.power_pellet_timer = 0
        self.power_pellet_duration = 30  # Frames power pellet lasts for
        self.power_pellet_flash = False
        self.power_pellet_flash_timer = 0
        
        # Initialize ghosts
        self.ghosts = [
            {
                "pos": (9, 9),          # Starting position
                "prev_pos": (9, 9),     # Track previous position for collision detection
                "dir": LEFT,            # Starting direction
                "color": GHOST_COLORS[0],  # Ghost color
                "frightened": False,    # Is ghost frightened?
                "eaten": False,         # Is ghost eaten?
                "return_path": []       # Path to return to ghost house when eaten
            },
            {
                "pos": (10, 9),
                "prev_pos": (10, 9),
                "dir": UP,
                "color": GHOST_COLORS[1],
                "frightened": False,
                "eaten": False,
                "return_path": []
            },
            {
                "pos": (8, 9),
                "prev_pos": (8, 9),
                "dir": DOWN,
                "color": GHOST_COLORS[2],
                "frightened": False,
                "eaten": False,
                "return_path": []
            },
            {
                "pos": (11, 9),
                "prev_pos": (11, 9),
                "dir": RIGHT,
                "color": GHOST_COLORS[3],
                "frightened": False,
                "eaten": False,
                "return_path": []
            }
        ]
        
        # Ghost house coordinates for returning eaten ghosts
        self.ghost_house_pos = (9, 9)
        
        # Timer for game updates - higher framerate for smoother animation
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.update_game)
        
        # Game speed (milliseconds per frame) - lower for smoother gameplay
        self.base_speed = 1000 // self.fps  # ~22.2ms for 45 FPS
        self.speed = self.base_speed
        
        # Animation variables
        self.blink_timer = 0
        self.blink_state = False
        
        # Game movement control
        self.move_counter = 0
        self.move_delay = 8  # Increased from 5 to 8 for slower movement
        
        # FPS Monitoring (for debugging)
        self.last_update_time = time.time()
        self.frame_times = []
        
        # Callback for game over
        self.on_game_over = on_game_over
        
        # Check if player is allowed to play (based on quota)
        self.can_play = self.settings["can_play"]
        
    def _load_settings(self):
        """Load game settings from file"""
        if os.path.exists(SETTINGS_FILE):
            try:
                with open(SETTINGS_FILE, 'r') as f:
                    settings = json.load(f)
                
                # Make sure all keys exist
                for key in DEFAULT_SETTINGS:
                    if key not in settings:
                        settings[key] = DEFAULT_SETTINGS[key]
                
                # IMPORTANT FIX: Always ensure the first game is playable
                # Check if this appears to be the first run (no high score)
                if settings["high_score"] == 0 and settings["last_game_score"] == 0:
                    settings["can_play"] = True
                    settings["cards_quota"] = 0
                    settings["cards_completed"] = 0
                
                return settings
            except:
                # If error loading, use defaults with can_play=True
                default_settings = DEFAULT_SETTINGS.copy()
                default_settings["can_play"] = True
                return default_settings
        else:
            # Create default settings with can_play=True
            default_settings = DEFAULT_SETTINGS.copy()
            default_settings["can_play"] = True
            return default_settings
    
    def _save_settings(self):
        """Save game settings to file"""
        try:
            with open(SETTINGS_FILE, 'w') as f:
                json.dump(self.settings, f)
        except Exception as e:
            tooltip(f"Error saving settings: {str(e)}")
    
    def _update_high_score(self, score):
        """Update high score if needed"""
        if score > self.settings["high_score"]:
            self.settings["high_score"] = score
            self.high_score = score
            self._save_settings()
    
    def _create_maze(self) -> List[List[int]]:
        """Create the maze layout - 0 is wall, 1 is path with dot, 2 is empty path, 3 is power pellet"""
        # More authentic Pacman-style maze
        maze = [
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0],
            [0, 3, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 3, 0],
            [0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0],
            [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0],
            [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0],
            [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0],
            [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0],
            [0, 0, 0, 0, 1, 0, 2, 2, 2, 2, 2, 2, 2, 0, 1, 0, 0, 0, 0],
            [0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0],
            [2, 2, 2, 2, 1, 2, 2, 0, 2, 2, 2, 0, 2, 2, 1, 2, 2, 2, 2],
            [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0],
            [0, 0, 0, 0, 1, 0, 2, 2, 2, 2, 2, 2, 2, 0, 1, 0, 0, 0, 0],
            [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0],
            [0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0],
            [0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0],
            [0, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 3, 0],
            [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
            [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0],
            [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
            [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        ]
        return maze
    
    def _count_dots(self) -> int:
        """Count the number of dots in the maze"""
        count = 0
        for row in self.maze:
            for cell in row:
                if cell == 1 or cell == 3:  # Dots and power pellets
                    count += 1
        return count
    
    def start_game(self):
        """Start or restart the game"""
        # Check if player is allowed to play
        if not self.can_play:
            cards_to_go = self.settings["cards_quota"] - self.settings["cards_completed"]
            showInfo(f"You need to complete {cards_to_go} more card(s) before playing again.")
            return
        
        # Reset game state
        self.state = GAME_RUNNING
        self.score = 0
        self.lives = 3
        self.maze = self._create_maze()
        self.dots_left = self._count_dots()
        self.power_pellet_active = False
        self.power_pellet_timer = 0
        
        # Reset Pacman position
        self.pacman_pos = (9, 15)
        self.pacman_prev_pos = (9, 15)  # Track previous position
        self.pacman_dir = LEFT
        self.pacman_next_dir = LEFT
        
        # Reset ghosts
        self.ghosts = [
            {
                "pos": (9, 9),
                "prev_pos": (9, 9),  # Track previous position
                "dir": LEFT,
                "color": GHOST_COLORS[0],
                "frightened": False,
                "eaten": False,
                "return_path": []
            },
            {
                "pos": (10, 9),
                "prev_pos": (10, 9),  # Track previous position
                "dir": UP,
                "color": GHOST_COLORS[1],
                "frightened": False,
                "eaten": False,
                "return_path": []
            },
            {
                "pos": (8, 9),
                "prev_pos": (8, 9),  # Track previous position
                "dir": DOWN,
                "color": GHOST_COLORS[2],
                "frightened": False,
                "eaten": False,
                "return_path": []
            },
            {
                "pos": (11, 9),
                "prev_pos": (11, 9),  # Track previous position
                "dir": RIGHT,
                "color": GHOST_COLORS[3],
                "frightened": False,
                "eaten": False,
                "return_path": []
            }
        ]
        
        # Start the timer with a faster rate for smoother animation
        self.timer.start(self.speed)
        self.setFocus()
        
        # Reset timing variables
        self.last_update_time = time.time()
        self.frame_times = []
        self.move_counter = 0
    
    def pause_game(self):
        """Pause the game"""
        if self.state == GAME_RUNNING:
            self.state = GAME_PAUSED
            self.timer.stop()
        elif self.state == GAME_PAUSED:
            self.state = GAME_RUNNING
            self.timer.start(self.speed)
    
    def stop_game(self):
        """Stop the game"""
        self.state = GAME_STOPPED
        self.timer.stop()
    
    def update_game(self):
        """Update game state for one frame"""
        if self.state != GAME_RUNNING:
            return
        
        # Calculate FPS for monitoring
        current_time = time.time()
        dt = current_time - self.last_update_time
        self.last_update_time = current_time
        
        if len(self.frame_times) > 10:
            self.frame_times.pop(0)
        self.frame_times.append(dt)
        
        # Update animation counter
        self.anim_counter += 1
        
        # Update power pellet timer if active
        if self.power_pellet_active:
            self.power_pellet_timer -= 1
            if self.power_pellet_timer <= 0:
                self.power_pellet_active = False
                for ghost in self.ghosts:
                    ghost["frightened"] = False
            
            # Make ghosts flash when power pellet is about to expire
            if self.power_pellet_timer < 10:
                self.power_pellet_flash_timer += 1
                if self.power_pellet_flash_timer >= 5:
                    self.power_pellet_flash = not self.power_pellet_flash
                    self.power_pellet_flash_timer = 0
        
        # Only move every few frames for consistent speed
        self.move_counter += 1
        if self.move_counter >= self.move_delay:
            self.move_counter = 0
            
            # Move Pacman
            self._move_pacman()
            
            # Check if Pacman eats a dot
            x, y = self.pacman_pos
            if self.maze[y][x] == 1:  # Regular dot
                self.maze[y][x] = 2  # Empty path now
                self.score += 10
                self.dots_left -= 1
            elif self.maze[y][x] == 3:  # Power pellet
                self.maze[y][x] = 2  # Empty path now
                self.score += 50
                self.dots_left -= 1
                self.power_pellet_active = True
                self.power_pellet_timer = self.power_pellet_duration
                self.power_pellet_flash = False
                # Make all ghosts frightened
                for ghost in self.ghosts:
                    if not ghost["eaten"]:  # Only if not already eaten
                        ghost["frightened"] = True
            
            # Move ghosts
            for ghost in self.ghosts:
                self._move_ghost(ghost)
                
                # Check if ghost catches Pacman or Pacman eats ghost
                # Enhanced collision detection to check both exact position matches and pass-through scenarios
                if (ghost["pos"] == self.pacman_pos) or (ghost["prev_pos"] == self.pacman_pos and self.pacman_prev_pos == ghost["pos"]):
                    if ghost["frightened"]:
                        # Pacman eats ghost
                        ghost["frightened"] = False
                        ghost["eaten"] = True
                        self.score += 200
                    elif not ghost["eaten"]:
                        # Ghost catches Pacman
                        self._lose_life()
                        break
            
            # Check if all dots are eaten
            if self.dots_left == 0:
                self._win_game()
        
        # Increment animation frame at a smoother rate
        if self.anim_counter % 8 == 0:  # Change frame every 8 game updates
            self.pacman_anim_frame = (self.pacman_anim_frame + 1) % 4
        
        # Update blink state for power pellets and other blinking elements
        self.blink_timer += 1
        if self.blink_timer >= 15:  # Change blink state every 15 frames
            self.blink_state = not self.blink_state
            self.blink_timer = 0
        
        # Update display using Qt's update method
        self.update()
    
    def _move_pacman(self):
        """Move Pacman according to its direction"""
        # Store previous position before moving
        self.pacman_prev_pos = self.pacman_pos
        
        # Try to change direction if requested
        if self.pacman_next_dir != self.pacman_dir:
            next_x = self.pacman_pos[0] + self.pacman_next_dir[0]
            next_y = self.pacman_pos[1] + self.pacman_next_dir[1]
            
            # Check if the direction change is valid
            if 0 <= next_x < GRID_WIDTH and 0 <= next_y < GRID_HEIGHT and self.maze[next_y][next_x] != 0:
                self.pacman_dir = self.pacman_next_dir
        
        # Move Pacman in current direction
        next_x = self.pacman_pos[0] + self.pacman_dir[0]
        next_y = self.pacman_pos[1] + self.pacman_dir[1]
        
        # Check if movement is valid
        if 0 <= next_x < GRID_WIDTH and 0 <= next_y < GRID_HEIGHT and self.maze[next_y][next_x] != 0:
            self.pacman_pos = (next_x, next_y)
        # Handle tunnel warping
        elif next_x < 0 and self.pacman_pos[1] == 10:  # Left tunnel
            self.pacman_pos = (GRID_WIDTH - 1, 10)
        elif next_x >= GRID_WIDTH and self.pacman_pos[1] == 10:  # Right tunnel
            self.pacman_pos = (0, 10)
    
    def _move_ghost(self, ghost):
        """Move a ghost according to AI rules"""
        # Store previous position before moving
        ghost["prev_pos"] = ghost["pos"]
        
        # If ghost is eaten, move it back to ghost house
        if ghost["eaten"]:
            # If we have a return path, follow it
            if ghost["return_path"]:
                ghost["pos"] = ghost["return_path"].pop(0)
                # If the ghost reached the ghost house, it's no longer eaten
                if ghost["pos"] == self.ghost_house_pos:
                    ghost["eaten"] = False
                return
            else:
                # Calculate a direct path to the ghost house
                ghost["return_path"] = self._calculate_path_to_ghost_house(ghost["pos"])
                return
        
        # Ghost AI - smarter movement
        possible_dirs = [UP, DOWN, LEFT, RIGHT]
        valid_dirs = []
        
        # Current position and direction
        x, y = ghost["pos"]
        curr_dir = ghost["dir"]
        
        # Ghosts never reverse direction (except when frightened)
        reverse_dir = (-curr_dir[0], -curr_dir[1])
        
        for direction in possible_dirs:
            # Skip reverse direction unless frightened
            if direction == reverse_dir and not ghost["frightened"]:
                continue
                
            next_x = x + direction[0]
            next_y = y + direction[1]
            
            # Check if direction is valid (not a wall)
            if (0 <= next_x < GRID_WIDTH and 0 <= next_y < GRID_HEIGHT and 
                self.maze[next_y][next_x] != 0):
                valid_dirs.append(direction)
        
        # If there are valid directions, choose one based on ghost behavior
        if valid_dirs:
            if ghost["frightened"]:
                # When frightened, move randomly
                ghost["dir"] = random.choice(valid_dirs)
            else:
                # When normal, use targeting behavior
                # For simplicity, we'll just make ghosts slightly smarter by
                # having a chance to move toward Pacman rather than randomly
                if random.random() < 0.4:  # 40% chance to target Pacman
                    # Find direction that gets closest to Pacman
                    best_dir = None
                    best_dist = float('inf')
                    
                    for direction in valid_dirs:
                        next_x = x + direction[0]
                        next_y = y + direction[1]
                        
                        # Calculate distance to Pacman
                        dist = self._manhattan_distance((next_x, next_y), self.pacman_pos)
                        
                        # Choose direction that minimizes distance
                        if dist < best_dist:
                            best_dist = dist
                            best_dir = direction
                    
                    ghost["dir"] = best_dir
                else:
                    # Otherwise move randomly from valid directions
                    ghost["dir"] = random.choice(valid_dirs)
        
        # Move ghost in the chosen direction
        next_x = ghost["pos"][0] + ghost["dir"][0]
        next_y = ghost["pos"][1] + ghost["dir"][1]
        
        # Check if movement is valid
        if 0 <= next_x < GRID_WIDTH and 0 <= next_y < GRID_HEIGHT and self.maze[next_y][next_x] != 0:
            ghost["pos"] = (next_x, next_y)
        # Handle tunnel warping
        elif next_x < 0 and ghost["pos"][1] == 10:  # Left tunnel
            ghost["pos"] = (GRID_WIDTH - 1, 10)
        elif next_x >= GRID_WIDTH and ghost["pos"][1] == 10:  # Right tunnel
            ghost["pos"] = (0, 10)
        else:
            # If movement is invalid, choose a new random direction
            ghost["dir"] = random.choice([UP, DOWN, LEFT, RIGHT])
    
    def _manhattan_distance(self, pos1, pos2):
        """Calculate the Manhattan distance between two positions"""
        return abs(pos1[0] - pos2[0]) + abs(pos1[1] - pos2[1])
    
    def _calculate_path_to_ghost_house(self, start_pos):
        """Calculate a path from a position to the ghost house"""
        # Simplified - just move directly toward the ghost house
        path = []
        curr_pos = start_pos
        
        while curr_pos != self.ghost_house_pos:
            x, y = curr_pos
            ghost_x, ghost_y = self.ghost_house_pos
            
            # Determine which direction to move
            if x < ghost_x:
                next_pos = (x + 1, y)
            elif x > ghost_x:
                next_pos = (x - 1, y)
            elif y < ghost_y:
                next_pos = (x, y + 1)
            else:
                next_pos = (x, y - 1)
            
            # Ensure we don't go through walls
            nx, ny = next_pos
            if 0 <= nx < GRID_WIDTH and 0 <= ny < GRID_HEIGHT and self.maze[ny][nx] != 0:
                path.append(next_pos)
                curr_pos = next_pos
            else:
                # If blocked by wall, try alternate directions
                for dir in [UP, DOWN, LEFT, RIGHT]:
                    alt_x = x + dir[0]
                    alt_y = y + dir[1]
                    if (0 <= alt_x < GRID_WIDTH and 0 <= alt_y < GRID_HEIGHT and 
                        self.maze[alt_y][alt_x] != 0):
                        path.append((alt_x, alt_y))
                        curr_pos = (alt_x, alt_y)
                        break
            
            # Safety limit to prevent infinite loops
            if len(path) > 100:
                break
        
        return path
    
    def _lose_life(self):
        """Handle Pacman losing a life"""
        self.lives -= 1
        
        if self.lives <= 0:
            self._game_over()
        else:
            # Reset positions
            self.pacman_pos = (9, 15)
            self.pacman_prev_pos = (9, 15)  # Reset previous position tracking
            self.pacman_dir = LEFT
            self.pacman_next_dir = LEFT
            
            # Reset ghosts
            self.ghosts = [
                {
                    "pos": (9, 9),
                    "prev_pos": (9, 9),  # Reset previous position tracking
                    "dir": LEFT,
                    "color": GHOST_COLORS[0],
                    "frightened": False,
                    "eaten": False,
                    "return_path": []
                },
                {
                    "pos": (10, 9),
                    "prev_pos": (10, 9),  # Reset previous position tracking
                    "dir": UP,
                    "color": GHOST_COLORS[1],
                    "frightened": False,
                    "eaten": False,
                    "return_path": []
                },
                {
                    "pos": (8, 9),
                    "prev_pos": (8, 9),  # Reset previous position tracking
                    "dir": DOWN,
                    "color": GHOST_COLORS[2],
                    "frightened": False,
                    "eaten": False,
                    "return_path": []
                },
                {
                    "pos": (11, 9),
                    "prev_pos": (11, 9),  # Reset previous position tracking
                    "dir": RIGHT,
                    "color": GHOST_COLORS[3],
                    "frightened": False,
                    "eaten": False,
                    "return_path": []
                }
            ]
            
            # Reset power pellet state
            self.power_pellet_active = False
            self.power_pellet_timer = 0
            
            # Pause briefly
            self.timer.stop()
            QTimer.singleShot(1000, lambda: self.timer.start(self.speed))
    
    def _win_game(self):
        """Handle winning the game"""
        self.state = GAME_STOPPED
        self.timer.stop()
        
        # Update high score
        if self.score > self.high_score:
            self.high_score = self.score
            self._update_high_score(self.score)
        
        # Set quota to 0 (no reviews needed for winning)
        self.settings["last_game_score"] = self.score
        self.settings["cards_quota"] = 0
        self.settings["cards_completed"] = 0
        self.settings["can_play"] = True
        self._save_settings()
            
        showInfo(f"You won! Score: {self.score}")
    
    def _game_over(self):
        """Handle game over"""
        self.state = GAME_OVER
        self.timer.stop()
        
        # Update high score
        if self.score > self.high_score:
            self.high_score = self.score
            self._update_high_score(self.score)
        
        # Calculate quota based on score
        if self.score < 500:
            quota = 20
        elif self.score < 1000:
            quota = 30
        elif self.score < 1500:
            quota = 40
        else:
            quota = 40
        
        # Save game state
        self.settings["last_game_score"] = self.score
        self.settings["cards_quota"] = quota
        self.settings["cards_completed"] = 0
        self.settings["can_play"] = False
        self._save_settings()
        
        # Call game over callback
        if self.on_game_over:
            self.on_game_over(self.score, quota)
    
    def update_card_completion(self, count):
        """Update the number of cards completed toward quota"""
        self.settings["cards_completed"] += count
        
        # Check if quota is met
        if self.settings["cards_completed"] >= self.settings["cards_quota"]:
            self.settings["can_play"] = True
            tooltip(f"Quota met! You can play Pacman again.")
        
        # Save settings
        self._save_settings()
        
        # Update local variables
        self.can_play = self.settings["can_play"]
    
    def reset_after_review(self):
        """Reset the game state after returning from a review"""
        # Update the game state and visuals
        self.setFocus()
        self.update()
    
    def keyPressEvent(self, event):
        """Handle key press events"""
        key = event.key()
        
        if self.state == GAME_RUNNING:
            if key == Qt.Key.Key_Up:
                self.pacman_next_dir = UP
            elif key == Qt.Key.Key_Down:
                self.pacman_next_dir = DOWN
            elif key == Qt.Key.Key_Left:
                self.pacman_next_dir = LEFT
            elif key == Qt.Key.Key_Right:
                self.pacman_next_dir = RIGHT
            elif key == Qt.Key.Key_P:
                self.pause_game()
        elif self.state == GAME_PAUSED and key == Qt.Key.Key_P:
            self.pause_game()
        elif (self.state == GAME_STOPPED or self.state == GAME_OVER) and key == Qt.Key.Key_Space:
            self.start_game()
    
    def paintEvent(self, event):
        """Draw the game"""
        # Use a painter with a pixmap for double buffering
        pixmap = QPixmap(GAME_WIDTH, GAME_HEIGHT)
        pixmap.fill(Qt.GlobalColor.transparent)
        
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)  # Enable anti-aliasing for smoother graphics
        
        # Fill background
        painter.fillRect(0, 0, GAME_WIDTH, GAME_HEIGHT, BACKGROUND_COLOR)
        
        # Draw maze
        self._draw_maze(painter)
        
        # Draw Pacman
        self._draw_pacman(painter)
        
        # Draw ghosts
        for ghost in self.ghosts:
            self._draw_ghost(painter, ghost)
        
        # Draw score and lives
        self._draw_ui(painter)
        
        # Draw game state messages
        self._draw_game_state(painter)
        
        # End painter on pixmap
        painter.end()
        
        # Draw the pixmap to the widget
        screen_painter = QPainter(self)
        screen_painter.drawPixmap(0, 0, pixmap)
        screen_painter.end()
    
    def _draw_maze(self, painter):
        """Draw the maze layout"""
        for y in range(GRID_HEIGHT):
            for x in range(GRID_WIDTH):
                cell_value = self.maze[y][x]
                
                if cell_value == 0:  # Wall
                    # Draw a rounded wall cell
                    path = QPainterPath()
                    path.addRoundedRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE, 3, 3)
                    painter.fillPath(path, WALL_COLOR)
                elif cell_value == 1:  # Dot
                    # Draw a dot in the center of the cell
                    painter.setBrush(DOT_COLOR)
                    painter.setPen(Qt.PenStyle.NoPen)
                    painter.drawEllipse(x * CELL_SIZE + CELL_SIZE//2 - 2, 
                                       y * CELL_SIZE + CELL_SIZE//2 - 2, 
                                       4, 4)
                elif cell_value == 3:  # Power pellet
                    # Draw a pulsating power pellet
                    painter.setBrush(POWER_PELLET_COLOR)
                    painter.setPen(Qt.PenStyle.NoPen)
                    
                    # Make power pellets pulsate
                    size = 10 if self.blink_state else 8
                    
                    painter.drawEllipse(x * CELL_SIZE + CELL_SIZE//2 - size//2, 
                                       y * CELL_SIZE + CELL_SIZE//2 - size//2, 
                                       size, size)
    
    def _draw_pacman(self, painter):
        """Draw Pacman with animation"""
        x, y = self.pacman_pos
        painter.setBrush(PACMAN_COLOR)
        painter.setPen(Qt.PenStyle.NoPen)
        
        # Determine Pacman's mouth angle based on direction and animation frame
        start_angle = 0
        if self.pacman_dir == RIGHT:
            start_angle = 0
        elif self.pacman_dir == DOWN:
            start_angle = 90
        elif self.pacman_dir == LEFT:
            start_angle = 180
        elif self.pacman_dir == UP:
            start_angle = 270
        
        # Animation - mouth opens and closes
        mouth_angle = 45 - (self.pacman_anim_frame * 15)
        if mouth_angle < 0:
            mouth_angle = -mouth_angle
        
        # Draw Pacman with animated mouth
        painter.drawPie(x * CELL_SIZE + 2, y * CELL_SIZE + 2, 
                       CELL_SIZE - 4, CELL_SIZE - 4, 
                       (start_angle + mouth_angle) * 16, (360 - 2 * mouth_angle) * 16)
    
    def _draw_ghost(self, painter, ghost):
        """Draw a ghost with eyes and animation"""
        x, y = ghost["pos"]
        
        # Determine ghost color based on state
        if ghost["eaten"]:
            # Just eyes for eaten ghosts
            self._draw_ghost_eyes(painter, x, y, ghost["dir"])
            return
        elif ghost["frightened"]:
            if self.power_pellet_timer < 10 and self.power_pellet_flash:
                ghost_color = GHOST_COLORS[ghost["color"] == GHOST_COLORS[0]]  # Flash between blue and white
            else:
                ghost_color = GHOST_FRIGHTENED_COLOR
        else:
            ghost_color = ghost["color"]
        
        # Draw ghost body (rounded rectangle with wavy bottom)
        path = QPainterPath()
        
        # Top half is a semi-circle
        path.addEllipse(x * CELL_SIZE + 2, y * CELL_SIZE + 2, CELL_SIZE - 4, (CELL_SIZE - 4) / 2)
        
        # Bottom half with wavy edge
        bottom_y = y * CELL_SIZE + 2 + (CELL_SIZE - 4) / 2
        
        # Base rectangle for bottom half
        path.addRect(x * CELL_SIZE + 2, bottom_y, CELL_SIZE - 4, (CELL_SIZE - 4) / 2)
        
        # Draw the ghost
        painter.fillPath(path, ghost_color)
        
        # Draw the wavy bottom using small ellipses
        wave_count = 4
        wave_width = (CELL_SIZE - 4) / wave_count
        
        painter.setBrush(BACKGROUND_COLOR)
        for i in range(wave_count):
            wave_x = x * CELL_SIZE + 2 + i * wave_width
            wave_y = y * CELL_SIZE + CELL_SIZE - 4
            painter.drawEllipse(wave_x, wave_y, wave_width, 4)
        
        # Draw eyes
        self._draw_ghost_eyes(painter, x, y, ghost["dir"])
    
    def _draw_ghost_eyes(self, painter, x, y, direction):
        """Draw ghost eyes looking in the direction of movement"""
        # Draw eye whites
        painter.setBrush(GHOST_EYES_COLOR)
        painter.setPen(Qt.PenStyle.NoPen)
        
        # Left eye
        left_eye_x = x * CELL_SIZE + CELL_SIZE//3 - 2
        left_eye_y = y * CELL_SIZE + CELL_SIZE//3 - 2
        painter.drawEllipse(left_eye_x, left_eye_y, 6, 6)
        
        # Right eye
        right_eye_x = x * CELL_SIZE + 2*CELL_SIZE//3 - 2
        right_eye_y = y * CELL_SIZE + CELL_SIZE//3 - 2
        painter.drawEllipse(right_eye_x, right_eye_y, 6, 6)
        
        # Draw pupils that look in the direction of movement
        painter.setBrush(GHOST_PUPILS_COLOR)
        
        # Calculate pupil offset based on direction
        pupil_offset_x = 0
        pupil_offset_y = 0
        
        if direction == RIGHT:
            pupil_offset_x = 1
        elif direction == LEFT:
            pupil_offset_x = -1
        elif direction == DOWN:
            pupil_offset_y = 1
        elif direction == UP:
            pupil_offset_y = -1
        
        # Left pupil
        painter.drawEllipse(left_eye_x + 2 + pupil_offset_x, left_eye_y + 2 + pupil_offset_y, 3, 3)
        
        # Right pupil
        painter.drawEllipse(right_eye_x + 2 + pupil_offset_x, right_eye_y + 2 + pupil_offset_y, 3, 3)
    
    def _draw_ui(self, painter):
        """Draw score, high score, and lives"""
        # Draw score
        painter.setPen(TEXT_COLOR)
        painter.setFont(QFont("Arial", 10, QFont.Weight.Bold))
        painter.drawText(10, 20, f"Score: {self.score}")
        
        # Draw high score
        painter.drawText(GAME_WIDTH//2 - 50, 20, f"High: {self.high_score}")
        
        # Draw lives in the top right
        lives_text = f"Lives: {self.lives}"
        text_width = painter.fontMetrics().horizontalAdvance(lives_text)
        
        painter.drawText(GAME_WIDTH - text_width - 10, 20, lives_text)
        
        # If quota is active, show it
        if not self.can_play:
            cards_left = self.settings["cards_quota"] - self.settings["cards_completed"]
            quota_text = f"Cards to Review: {cards_left}"
            painter.setPen(QColor(255, 165, 0))  # Orange
            painter.drawText(10, GAME_HEIGHT - 10, quota_text)
    
    def _draw_game_state(self, painter):
        """Draw messages for different game states"""
        if self.state == GAME_PAUSED:
            # Semi-transparent overlay
            overlay = QColor(0, 0, 0, 150)
            painter.fillRect(0, 0, GAME_WIDTH, GAME_HEIGHT, overlay)
            
            # Pause message
            painter.setPen(TEXT_COLOR)
            painter.setFont(QFont("Arial", 20, QFont.Weight.Bold))
            painter.drawText(GAME_WIDTH//2 - 50, GAME_HEIGHT//2, "PAUSED")
            painter.setFont(QFont("Arial", 12))
            painter.drawText(GAME_WIDTH//2 - 90, GAME_HEIGHT//2 + 30, "Press P to resume")
            
        elif self.state == GAME_STOPPED:
            # Title screen
            # Semi-transparent overlay
            overlay = QColor(0, 0, 0, 180)
            painter.fillRect(0, 0, GAME_WIDTH, GAME_HEIGHT, overlay)
            
            # Title
            painter.setPen(PACMAN_COLOR)
            painter.setFont(QFont("Arial", 26, QFont.Weight.Bold))
            painter.drawText(GAME_WIDTH//2 - 140, GAME_HEIGHT//2 - 40, "ANKI PACMAN")
            
            # Instructions
            painter.setPen(TEXT_COLOR)
            painter.setFont(QFont("Arial", 12))
            
            if not self.can_play:
                cards_left = self.settings["cards_quota"] - self.settings["cards_completed"]
                painter.drawText(GAME_WIDTH//2 - 170, GAME_HEIGHT//2 + 10, 
                                f"You need to review {cards_left} more card(s) to play")
            else:
                painter.drawText(GAME_WIDTH//2 - 120, GAME_HEIGHT//2 + 10, "Press SPACE to start")
                
            painter.drawText(GAME_WIDTH//2 - 150, GAME_HEIGHT//2 + 40, "Use Arrow Keys to move")
            painter.drawText(GAME_WIDTH//2 - 90, GAME_HEIGHT//2 + 70, "Press P to pause")
            
        elif self.state == GAME_OVER:
            # Game over screen
            # Semi-transparent overlay
            overlay = QColor(0, 0, 0, 180)
            painter.fillRect(0, 0, GAME_WIDTH, GAME_HEIGHT, overlay)
            
            # Game over message
            painter.setPen(QColor(255, 0, 0))  # Red for game over
            painter.setFont(QFont("Arial", 24, QFont.Weight.Bold))
            painter.drawText(GAME_WIDTH//2 - 100, GAME_HEIGHT//2 - 40, "GAME OVER")
            
            # Final score
            painter.setPen(TEXT_COLOR)
            painter.setFont(QFont("Arial", 16))
            painter.drawText(GAME_WIDTH//2 - 80, GAME_HEIGHT//2, f"Score: {self.score}")
            
            if self.score == self.high_score and self.score > 0:
                painter.setPen(QColor(255, 215, 0))  # Gold for high score
                painter.drawText(GAME_WIDTH//2 - 100, GAME_HEIGHT//2 + 30, "NEW HIGH SCORE!")
            
            # Review message
            painter.setPen(TEXT_COLOR)
            painter.setFont(QFont("Arial", 14))
            
            quota = self.settings["cards_quota"]
            painter.drawText(GAME_WIDTH//2 - 160, GAME_HEIGHT//2 + 70, 
                            f"Time to review {quota} flashcards!")


# Get all available decks from Anki
def get_all_decks():
    """Get all available decks from Anki collection"""
    decks = {}
    for deck in mw.col.decks.all_names_and_ids():
        # In newer Anki versions, all_names_and_ids returns DeckNameId objects
        decks[deck.id] = deck.name
    return decks


# Main dialog for the game
class PacmanDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Anki Pacman")
        self.setMinimumSize(GAME_WIDTH + 20, GAME_HEIGHT + 80)
        
        # Create layout
        layout = QVBoxLayout(self)
        
        # Add game widget
        self.game = PacmanGame(self, self.on_game_over)
        layout.addWidget(self.game)
        
        # Add buttons
        button_layout = QHBoxLayout()
        
        self.start_button = QPushButton("Start")
        self.pause_button = QPushButton("Pause")
        self.quit_button = QPushButton("Quit")
        
        # If quota is active, add a review button
        if not self.game.can_play:
            self.review_button = QPushButton("Review Now")
            qconnect(self.review_button.clicked, self.start_review_now)
            button_layout.addWidget(self.review_button)
        
        qconnect(self.start_button.clicked, self.game.start_game)
        qconnect(self.pause_button.clicked, self.game.pause_game)
        qconnect(self.quit_button.clicked, self.close)
        
        button_layout.addWidget(self.start_button)
        button_layout.addWidget(self.pause_button)
        button_layout.addWidget(self.quit_button)
        
        layout.addLayout(button_layout)
        
        # Add keyboard shortcut info
        shortcut_label = QLabel("Keyboard: Arrow keys to move, P to pause, Space to start")
        shortcut_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(shortcut_label)
        
        # Initialize dialog
        self.setLayout(layout)
        
        # To prevent garbage collection
        global pacman_dialog
        pacman_dialog = self
    
    def start_review_now(self):
        """Start reviews without waiting for game over"""
        # Calculate remaining quota
        quota_remaining = self.game.settings["cards_quota"] - self.game.settings["cards_completed"]
        if quota_remaining <= 0:
            showInfo("You've already completed your review quota!")
            return
        
        # Show card selection dialog with the remaining quota
        self.show_card_selection(quota_remaining)
    
    def on_game_over(self, score, quota):
        """Handle game over - show message and start flashcard reviews"""
        # Store the score and quota for later use
        self.final_score = score
        self.quota = quota
        
        # Create a message box to inform the user
        msg_box = QMessageBox(self)
        msg_box.setWindowTitle("Game Over")
        msg_box.setText(f"Game Over! Your score: {score}\n\nYou need to complete {quota} flashcard reviews before playing again.")
        msg_box.setStandardButtons(QMessageBox.StandardButton.Ok)
        msg_box.exec()
        
        # Show card selection dialog
        self.show_card_selection(quota)
    
    def show_card_selection(self, quota):
        """Show a dialog to select which cards to review"""
        # Create the dialog
        dialog = QDialog(self)
        dialog.setWindowTitle("Select Cards to Review")
        dialog.setMinimumWidth(350)
        
        # Create layout
        layout = QVBoxLayout()
        
        # Add label
        label = QLabel(f"You need to review {quota} cards before playing again.\nSelect options for your review:")
        layout.addWidget(label)
        
        # Add deck selection
        deck_layout = QHBoxLayout()
        deck_label = QLabel("Deck:")
        self.deck_combo = QComboBox()
        
        # Get all decks
        decks = get_all_decks()
        selected_deck_id = self.game.settings.get("selected_deck_id", None)
        
        # Add "All Decks" option
        self.deck_combo.addItem("All Decks", None)
        
        # Add all available decks
        for deck_id, deck_name in decks.items():
            self.deck_combo.addItem(deck_name, deck_id)
            
            # Select previously used deck if available
            if selected_deck_id and deck_id == selected_deck_id:
                self.deck_combo.setCurrentIndex(self.deck_combo.count() - 1)
        
        deck_layout.addWidget(deck_label)
        deck_layout.addWidget(self.deck_combo)
        layout.addLayout(deck_layout)
        
        # Add card type selection
        card_type_label = QLabel("Card Type:")
        layout.addWidget(card_type_label)
        
        # Add radio buttons for card type
        self.new_cards_radio = QRadioButton("New Cards")
        self.review_cards_radio = QRadioButton("Review Cards")
        self.both_cards_radio = QRadioButton("Both New and Review Cards")
        
        # Set review cards as default
        self.review_cards_radio.setChecked(True)
        
        layout.addWidget(self.new_cards_radio)
        layout.addWidget(self.review_cards_radio)
        layout.addWidget(self.both_cards_radio)
        
        # Add buttons
        button_box = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        qconnect(button_box.accepted, dialog.accept)
        qconnect(button_box.rejected, dialog.reject)
        layout.addWidget(button_box)
        
        dialog.setLayout(layout)
        
        # Show the dialog
        result = dialog.exec()
        
        if result == QDialog.DialogCode.Accepted:
            # Save selected deck
            selected_deck_id = self.deck_combo.currentData()
            self.game.settings["selected_deck_id"] = selected_deck_id
            self.game.settings["can_play"] = False  # Ensure can't play until finished
            self.game._save_settings()
            
            # Start reviews based on selection
            self.start_reviews(quota, selected_deck_id)
    
    def start_reviews(self, quota, deck_id=None):
        """Start the flashcard review process"""
        # Determine card type based on selection
        if self.new_cards_radio.isChecked():
            card_type = "new"
        elif self.review_cards_radio.isChecked():
            card_type = "review"
        else:  # Both
            card_type = "both"
        
        # Hide the dialog temporarily but don't close it
        self.hide()
        
        # Start the reviews
        review_flashcards(quota, card_type, self.game, deck_id, self)
        
        # Dialog will be shown again when reviews are finished
    
    def reviews_completed(self):
        """Called when reviews are completed"""
        # Show the dialog again and update the UI
        self.show()
        self.activateWindow()  # Ensure window is brought to the front
        self.raise_()  # Raise window to the top of the stack
        self.game.reset_after_review()
        
        # Refresh the UI - show review button if still needed
        if not self.game.can_play:
            # Check if we already have a review button
            has_review_button = hasattr(self, 'review_button')
            
            if not has_review_button:
                self.review_button = QPushButton("Review Now")
                qconnect(self.review_button.clicked, self.start_review_now)
                self.layout().itemAt(1).layout().insertWidget(0, self.review_button)


# Function to review flashcards
def review_flashcards(num_reviews: int, card_type: str, game: PacmanGame, deck_id=None, parent_dialog=None):
    """Present a number of flashcards for review"""
    # Check if collection is available
    if not mw or not mw.col:
        showInfo("No collection loaded. Please open a deck first.")
        if parent_dialog:
            parent_dialog.reviews_completed()
        return
    
    # Get due cards
    due_cards = get_due_cards(num_reviews, card_type, deck_id)
    
    if not due_cards:
        # If no cards available, offer an option to skip the quota
        msg = QMessageBox()
        msg.setWindowTitle("No Cards Available")
        msg.setText(f"No {card_type} cards available in the selected deck.")
        msg.setInformativeText("Would you like to waive the review requirement and play Pacman anyway?")
        msg.setStandardButtons(QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
        msg.setDefaultButton(QMessageBox.StandardButton.No)
        
        if msg.exec() == QMessageBox.StandardButton.Yes:
            # User chose to skip - set quota as complete
            game.settings["cards_completed"] = game.settings["cards_quota"]
            game.settings["can_play"] = True
            game._save_settings()
            tooltip("Review requirement waived. You can now play Pacman!")
        else:
            # User chose not to skip - suggest trying another deck
            showInfo("Try selecting a different deck or card type.")
            
        if parent_dialog:
            parent_dialog.reviews_completed()
        return
    
    # Create a dialog for reviewing
    review_dialog = FlashcardReviewDialog(due_cards, num_reviews, game, parent_dialog)
    review_dialog.exec()


# Function to get due cards
def get_due_cards(num_cards: int, card_type: str, deck_id=None) -> List[Card]:
    """Get a list of due cards from the collection"""
    cards = []
    
    # Build the search query
    deck_query = ""
    if deck_id:
        deck_name = mw.col.decks.name(deck_id)
        deck_query = f"deck:\"{deck_name}\" "
    
    # Try to get cards of the requested type first
    if card_type == "new":
        card_ids = mw.col.find_cards(f"{deck_query}is:new")
    elif card_type == "review":
        card_ids = mw.col.find_cards(f"{deck_query}is:due")
    else:  # Both
        card_ids = mw.col.find_cards(f"{deck_query}is:due")
        new_ids = mw.col.find_cards(f"{deck_query}is:new")
        card_ids.extend(new_ids)
    
    # If no cards of the requested type, try the other type
    if not card_ids and card_type == "review":
        # No review cards, try new cards
        card_ids = mw.col.find_cards(f"{deck_query}is:new")
    elif not card_ids and card_type == "new":
        # No new cards, try review cards
        card_ids = mw.col.find_cards(f"{deck_query}is:due")
    
    # Get the cards
    for card_id in card_ids[:num_cards]:
        card = mw.col.get_card(card_id)
        cards.append(card)
    
    return cards


# Dialog for reviewing flashcards
class FlashcardReviewDialog(QDialog):
    def __init__(self, cards: List[Card], quota: int, game: PacmanGame, parent_dialog=None, parent=None):
        super().__init__(mw if parent is None else parent)  # Use main window as parent
        self.setWindowTitle("Pacman Review")
        self.setMinimumSize(600, 400)
        
        # Store cards and initialize current index
        self.cards = cards
        self.current_index = 0
        self.num_correct = 0
        self.answer_shown = False
        self.quota = quota
        self.game = game
        self.cards_reviewed = 0
        self.parent_dialog = parent_dialog
        
        # Create layout
        layout = QVBoxLayout(self)
        
        # Add progress bar
        progress_layout = QHBoxLayout()
        
        # Progress bar for total quota
        self.quota_label = QLabel(f"Progress: 0/{quota}")
        progress_layout.addWidget(self.quota_label)
        
        self.progress_bar = QProgressBar(self)
        self.progress_bar.setRange(0, quota)
        self.progress_bar.setValue(0)
        progress_layout.addWidget(self.progress_bar)
        
        layout.addLayout(progress_layout)
        
        # Add card content
        self.card_content = QWebEngineView(self)
        self.card_content.setMinimumHeight(200)
        layout.addWidget(self.card_content)
        
        # Add answer buttons
        button_layout = QHBoxLayout()
        
        self.again_button = QPushButton("Again (1)")
        self.hard_button = QPushButton("Hard (2)")
        self.good_button = QPushButton("Good (3)")
        self.easy_button = QPushButton("Easy (4)")
        
        qconnect(self.again_button.clicked, lambda: self.answer_card(1))
        qconnect(self.hard_button.clicked, lambda: self.answer_card(2))
        qconnect(self.good_button.clicked, lambda: self.answer_card(3))
        qconnect(self.easy_button.clicked, lambda: self.answer_card(4))
        
        button_layout.addWidget(self.again_button)
        button_layout.addWidget(self.hard_button)
        button_layout.addWidget(self.good_button)
        button_layout.addWidget(self.easy_button)
        
        # Initially hide answer buttons
        self.again_button.hide()
        self.hard_button.hide()
        self.good_button.hide()
        self.easy_button.hide()
        
        layout.addLayout(button_layout)
        
        # Add show answer button
        self.show_answer_button = QPushButton("Show Answer (Space)")
        qconnect(self.show_answer_button.clicked, self.show_answer)
        layout.addWidget(self.show_answer_button)
        
        # Add keyboard shortcut info
        keyboard_info = QLabel("Keyboard shortcuts: Space = Show Answer, 1-4 = Select Answer")
        keyboard_info.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(keyboard_info)
        
        # Add exit button (will save progress and go back to Pacman)
        exit_button = QPushButton("Return to Pacman (Progress will be saved)")
        qconnect(exit_button.clicked, self.return_to_pacman)
        layout.addWidget(exit_button)
        
        # Initialize dialog
        self.setLayout(layout)
        
        # Set focus to enable keyboard shortcuts
        self.setFocus()
        
        # Show first card
        self.show_question()
    
    def closeEvent(self, event):
        """Handle close event to save progress"""
        # Update the game's card completion count
        self.game.update_card_completion(self.cards_reviewed)
        
        # Show the parent dialog if it exists
        if self.parent_dialog:
            self.parent_dialog.reviews_completed()
        
        # Accept the close event
        event.accept()
    
    def return_to_pacman(self):
        """Save progress and return to the Pacman game"""
        # Update the game's card completion count
        self.game.update_card_completion(self.cards_reviewed)
        
        # Show tooltip about progress
        if self.cards_reviewed > 0:
            tooltip(f"Progress saved: {self.cards_reviewed}/{self.quota} cards reviewed.")
        
        # Close the review dialog and return to Pacman
        self.accept()
    
    def show_question(self):
        """Show the question side of the current card"""
        if self.current_index >= len(self.cards):
            self.finish_review()
            return
        
        # Update progress
        self.progress_bar.setValue(self.cards_reviewed)
        self.quota_label.setText(f"Progress: {self.cards_reviewed}/{self.quota}")
        
        # Get current card
        card = self.cards[self.current_index]
        
        # Initialize card timers to fix the timing issue
        try:
            card.startTimer()
        except:
            pass  # Ignore errors
        
        # Show question
        self.card_content.setHtml(card.question())
        
        # Reset answer shown flag
        self.answer_shown = False
        
        # Show/hide buttons
        self.show_answer_button.show()
        self.again_button.hide()
        self.hard_button.hide()
        self.good_button.hide()
        self.easy_button.hide()
        
        # Set focus to enable keyboard shortcuts
        self.setFocus()
    
    def show_answer(self):
        """Show the answer side of the current card"""
        if self.current_index >= len(self.cards):
            return
        
        # Get current card
        card = self.cards[self.current_index]
        
        # Show answer
        self.card_content.setHtml(card.answer())
        
        # Set answer shown flag
        self.answer_shown = True
        
        # Show/hide buttons
        self.show_answer_button.hide()
        self.again_button.show()
        self.hard_button.show()
        self.good_button.show()
        self.easy_button.show()
        
        # Set focus to enable keyboard shortcuts
        self.setFocus()
    
    def answer_card(self, ease: int):
        """Answer the current card and move to next"""
        if self.current_index >= len(self.cards):
            return
        
        # Get current card
        card = self.cards[self.current_index]
        
        try:
            # Answer the card in Anki
            mw.col.sched.answerCard(card, ease)
            
            # Increment the count of cards reviewed
            self.cards_reviewed += 1
            
            # Update the game's progress immediately
            self.game.update_card_completion(1)
            
        except Exception as e:
            # If there's an error, show a message and continue
            tooltip(f"Error recording answer: {str(e)}")
        
        # Track correct answers (good or easy)
        if ease >= 3:
            self.num_correct += 1
        
        # Move to next card
        self.current_index += 1
        self.show_question()
    
    def keyPressEvent(self, event):
        """Handle keyboard shortcuts for reviewing"""
        key = event.key()
        
        if key == Qt.Key.Key_Space:
            # Space shows answer if question is showing
            if not self.answer_shown:
                self.show_answer()
        elif self.answer_shown:  # Only process number keys if answer is shown
            if key == Qt.Key.Key_1:
                self.answer_card(1)  # Again
            elif key == Qt.Key.Key_2:
                self.answer_card(2)  # Hard
            elif key == Qt.Key.Key_3:
                self.answer_card(3)  # Good
            elif key == Qt.Key.Key_4:
                self.answer_card(4)  # Easy
    
    def finish_review(self):
        """Handle finishing all reviews"""
        # Update game progress one last time (should already be updated, but just in case)
        self.game.update_card_completion(0)
        
        # Update UI
        self.progress_bar.setValue(self.cards_reviewed)
        self.quota_label.setText(f"Progress: {self.cards_reviewed}/{self.quota}")
        
        # Show completion message
        if self.cards_reviewed >= self.quota:
            # User has completed the quota
            result = QMessageBox.information(
                self, 
                "Review Completed", 
                f"Review completed! You got {self.num_correct} out of {self.cards_reviewed} correct.\n\nYou've met your quota and can play Pacman again.",
                QMessageBox.StandardButton.Ok
            )
        else:
            # User still has cards to review
            cards_left = self.quota - self.cards_reviewed
            result = QMessageBox.information(
                self, 
                "Review Session Finished", 
                f"Review session finished! You got {self.num_correct} out of {self.cards_reviewed} correct.\n\nYou still need to review {cards_left} more cards before playing Pacman again.",
                QMessageBox.StandardButton.Ok
            )
        
        # Close dialog and return to main game
        self.accept()


class StyledPacmanButton(QPushButton):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setText("🟡")  # Using a yellow circle emoji as a Pacman-like icon
        self.setToolTip("Play Pacman")  # Show text on hover
        
        # Create a much more compact button
        self.setStyleSheet("""
            QPushButton {
                background-color: #333333; 
                color: #FFD800;
                border-radius: 12px;
                min-width: 24px;
                max-width: 24px;
                min-height: 24px;
                max-height: 24px;
                padding: 0px;
                font-weight: bold;
                font-size: 12px;
                border: 1px solid #666666;
            }
            QPushButton:hover {
                background-color: #444444;
                border: 1px solid #FFD800;
            }
            QPushButton:pressed {
                background-color: #222222;
            }
        """)


# Create menu item
def open_pacman_game():
    """Open the Pacman game dialog"""
    global pacman_dialog
    if pacman_dialog is None or not pacman_dialog.isVisible():
        pacman_dialog = PacmanDialog(mw)
    
    pacman_dialog.show()
    pacman_dialog.raise_()
    pacman_dialog.activateWindow()


# Add Pacman button to Anki main window (compatible with Anki 24.11+)
def setup_pacman_button():
    """Add Pacman button to Anki in a way that's compatible with newer Anki versions"""
    try:
        # Create the button
        pacman_button = StyledPacmanButton()
        qconnect(pacman_button.clicked, open_pacman_game)
        
        # Add to main window - newer Anki versions
        # For Anki 24.11+, we need a different approach
        # Add button directly to main window instead of toolbar
        pacman_button.setParent(mw)
        pacman_button.show()
        
        # Position the button in the top-right corner
        def reposition_button():
            toolbar_height = 40  # Estimated toolbar height
            button_width = pacman_button.width()
            mw_width = mw.width()
            pacman_button.move(mw_width - button_width - 20, toolbar_height + 10)
        
        # Reposition when window is resized
        mw.resized.connect(reposition_button)
        
        # Initial positioning
        QTimer.singleShot(500, reposition_button)
        
        return pacman_button
    except Exception as e:
        print(f"Error setting up Pacman button: {e}")
        return None


# Create menu item for the game (keep this for backward compatibility)
pacman_action = QAction("Play Pacman", mw)
qconnect(pacman_action.triggered, open_pacman_game)
mw.form.menuTools.addAction(pacman_action)

# Add the styled button using the compatible method
pacman_button = setup_pacman_button()


# Make sure user_files directory exists
if not os.path.exists(USER_FILES_DIR):
    try:
        os.makedirs(USER_FILES_DIR)
    except Exception as e:
        print(f"Error creating user_files directory: {e}")
