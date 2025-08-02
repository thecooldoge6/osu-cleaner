import os
import threading
import tkinter as tk
from tkinter import filedialog, messagebox, ttk, scrolledtext
from subprocess import Popen, PIPE, DEVNULL
from PIL import Image
import hashlib
from collections import defaultdict, Counter
import zipfile
import tempfile
import shutil
import multiprocessing
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor, as_completed
import time
from pathlib import Path
import json
import re
import sqlite3
from datetime import datetime, timedelta
import wave
import struct
import logging

# Optional imports
try:
    import psutil
    HAS_PSUTIL = True
except ImportError:
    HAS_PSUTIL = False

try:
    import mutagen
    from mutagen.mp3 import MP3
    from mutagen.oggvorbis import OggVorbis
    HAS_MUTAGEN = True
except ImportError:
    HAS_MUTAGEN = False

VIDEO_EXTENSIONS = {'.mp4', '.avi', '.flv', '.wmv', '.mov', '.mkv', '.webm'}
HITSOUND_EXTENSIONS = {'.wav'}
AUDIO_EXTENSIONS = {'.mp3', '.ogg'}
IMAGE_EXTENSIONS = {'.png', '.jpg', '.jpeg'}
STORYBOARD_EXTENSIONS = {'.osb'}
OSZ_EXTENSIONS = {'.osz'}
OSU_EXT = '.osu'

stop_requested = False

# Enhanced configuration
BITRATE_OPTIONS = {
    "32 kbps": "32k",
    "64 kbps": "64k", 
    "96 kbps": "96k",
    "128 kbps": "128k",
    "160 kbps": "160k",
    "192 kbps": "192k",
    "256 kbps": "256k",
    "320 kbps": "320k"
}

IMAGE_QUALITY_OPTIONS = ["Off", "480p", "720p", "1080p", "1440p"]
BACKGROUND_OPTIONS = ["Keep Original", "Black & White", "Remove Completely"]
SPEED_OPTIONS = ["Normal", "Fast (4 threads)", "Turbo (8 threads)", "Max (All CPU cores)", "Adaptive"]
EXTRA_OPTIONS = ["Remove Videos", "Remove Unused Images", "Clean Empty Folders"]

# New feature options
GENRE_BITRATES = {
    "Electronic/EDM": "192k",
    "Rock/Metal": "256k", 
    "Classical/Orchestral": "320k",
    "Pop/Vocal": "160k",
    "Instrumental": "192k",
    "Default": "128k"
}

VERIFICATION_OPTIONS = ["Audio Playback", "Image Loading", "Beatmap Parsing", "File Integrity"]
PROTECTION_OPTIONS = ["Recent Downloads (7 days)", "Favorite Collections", "Specific Mappers", "Manual Exclude List"]

# Cache for file operations and new analytics
_size_cache = {}
_hash_cache = {}
_audio_info_cache = {}
_beatmap_cache = {}

# Analytics storage
analytics_db = None
whitelist_data = {'mappers': set(), 'folders': set(), 'recent_days': 7}

def init_analytics_db():
    """Initialize SQLite database for analytics"""
    global analytics_db
    try:
        db_path = os.path.join(os.path.expanduser("~"), "osu_cleaner_analytics.db")
        analytics_db = sqlite3.connect(db_path, check_same_thread=False)
        
        analytics_db.execute('''
            CREATE TABLE IF NOT EXISTS cleanup_sessions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp TEXT,
                total_saved INTEGER,
                files_processed INTEGER,
                duration REAL,
                settings TEXT
            )
        ''')
        
        analytics_db.execute('''
            CREATE TABLE IF NOT EXISTS file_stats (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                session_id INTEGER,
                file_type TEXT,
                original_size INTEGER,
                compressed_size INTEGER,
                compression_ratio REAL,
                FOREIGN KEY (session_id) REFERENCES cleanup_sessions (id)
            )
        ''')
        
        analytics_db.commit()
    except Exception as e:
        print(f"Analytics DB initialization failed: {e}")

def load_whitelist():
    """Load whitelist configuration"""
    global whitelist_data
    try:
        whitelist_file = os.path.join(os.path.expanduser("~"), "osu_cleaner_whitelist.json")
        if os.path.exists(whitelist_file):
            with open(whitelist_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
                whitelist_data['mappers'] = set(data.get('mappers', []))
                whitelist_data['folders'] = set(data.get('folders', []))
                whitelist_data['recent_days'] = data.get('recent_days', 7)
    except Exception as e:
        print(f"Whitelist loading failed: {e}")

def save_whitelist():
    """Save whitelist configuration"""
    try:
        whitelist_file = os.path.join(os.path.expanduser("~"), "osu_cleaner_whitelist.json")
        data = {
            'mappers': list(whitelist_data['mappers']),
            'folders': list(whitelist_data['folders']),
            'recent_days': whitelist_data['recent_days']
        }
        with open(whitelist_file, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
    except Exception as e:
        print(f"Whitelist saving failed: {e}")

def format_size(size_bytes):
    for unit in ['B', 'KB', 'MB', 'GB']:
        if size_bytes < 1024:
            return f"{size_bytes:.2f} {unit}"
        size_bytes /= 1024
    return f"{size_bytes:.2f} TB"

def get_optimal_thread_count():
    """Dynamically calculate optimal thread count based on system resources"""
    cpu_count = multiprocessing.cpu_count()
    
    if HAS_PSUTIL:
        try:
            memory_gb = psutil.virtual_memory().total / (1024**3)
            if memory_gb < 4:
                return max(2, cpu_count // 2)
            elif memory_gb < 8:
                return max(4, cpu_count)
            else:
                return min(16, cpu_count * 2)
        except:
            pass
    
    if cpu_count <= 2:
        return 2
    elif cpu_count <= 4:
        return 4
    elif cpu_count <= 8:
        return min(8, cpu_count)
    else:
        return min(12, cpu_count)

def get_thread_count():
    """Get thread count based on speed setting"""
    speed_mode = speed_var.get()
    if speed_mode == "Fast (4 threads)":
        return 4
    elif speed_mode == "Turbo (8 threads)":
        return 8
    elif speed_mode == "Max (All CPU cores)":
        return multiprocessing.cpu_count()
    elif speed_mode == "Adaptive":
        return get_optimal_thread_count()
    else:
        return 1

def get_file_size_cached(filepath):
    """Get file size with caching"""
    if filepath not in _size_cache:
        try:
            _size_cache[filepath] = os.path.getsize(filepath)
        except:
            _size_cache[filepath] = 0
    return _size_cache[filepath]

def get_audio_info(filepath):
    """Get detailed audio information with caching"""
    if filepath in _audio_info_cache:
        return _audio_info_cache[filepath]
    
    info = {'bitrate': 0, 'duration': 0, 'channels': 2, 'sample_rate': 44100, 'genre': 'Unknown'}
    
    try:
        if HAS_MUTAGEN:
            if filepath.lower().endswith('.mp3'):
                audio = MP3(filepath)
                info['bitrate'] = getattr(audio.info, 'bitrate', 0)
                info['duration'] = getattr(audio.info, 'length', 0)
                info['channels'] = getattr(audio.info, 'channels', 2)
                info['sample_rate'] = getattr(audio.info, 'sample_rate', 44100)
                
                # Try to extract genre from tags
                if 'TCON' in audio:
                    info['genre'] = str(audio['TCON'][0])
                elif 'TIT2' in audio:  # Use title to guess genre
                    title = str(audio['TIT2'][0]).lower()
                    if any(word in title for word in ['electronic', 'edm', 'dubstep', 'techno']):
                        info['genre'] = 'Electronic/EDM'
                    elif any(word in title for word in ['rock', 'metal', 'punk']):
                        info['genre'] = 'Rock/Metal'
                    elif any(word in title for word in ['classical', 'orchestra', 'symphony']):
                        info['genre'] = 'Classical/Orchestral'
                    elif any(word in title for word in ['pop', 'vocal', 'singer']):
                        info['genre'] = 'Pop/Vocal'
            
            elif filepath.lower().endswith('.ogg'):
                audio = OggVorbis(filepath)
                info['bitrate'] = getattr(audio.info, 'bitrate', 0)
                info['duration'] = getattr(audio.info, 'length', 0)
                info['channels'] = getattr(audio.info, 'channels', 2)
                info['sample_rate'] = getattr(audio.info, 'sample_rate', 44100)
        
        # Fallback using FFprobe
        if info['bitrate'] == 0:
            cmd = ["ffprobe", "-v", "quiet", "-show_entries", 
                   "format=bit_rate,duration", "-show_entries",
                   "stream=channels,sample_rate", "-of", "csv=p=0", filepath]
            try:
                proc = Popen(cmd, stdout=PIPE, stderr=DEVNULL)
                output = proc.communicate(timeout=5)[0].decode('utf-8', errors='ignore')
                if proc.returncode == 0:
                    parts = output.strip().split(',')
                    if len(parts) >= 2:
                        info['bitrate'] = int(parts[1]) if parts[1].isdigit() else 0
                        info['duration'] = float(parts[0]) if parts[0].replace('.', '').isdigit() else 0
            except:
                pass
    
    except Exception as e:
        pass
    
    _audio_info_cache[filepath] = info
    return info

def parse_beatmap_file(osu_file_path):
    """Parse .osu file and extract metadata"""
    if osu_file_path in _beatmap_cache:
        return _beatmap_cache[osu_file_path]
    
    beatmap_info = {
        'title': '',
        'artist': '',
        'creator': '',
        'version': '',
        'background': '',
        'audio_file': '',
        'video_files': [],
        'events': [],
        'timing_points': [],
        'hit_objects': [],
        'star_rating': 0.0,
        'approach_rate': 5.0,
        'overall_difficulty': 5.0
    }
    
    try:
        with open(osu_file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        # Parse metadata
        metadata_match = re.search(r'\[General\](.*?)\[', content, re.DOTALL)
        if metadata_match:
            general_section = metadata_match.group(1)
            for line in general_section.split('\n'):
                line = line.strip()
                if line.startswith('AudioFilename:'):
                    beatmap_info['audio_file'] = line.split(':', 1)[1].strip()
        
        metadata_match = re.search(r'\[Metadata\](.*?)\[', content, re.DOTALL)
        if metadata_match:
            metadata_section = metadata_match.group(1)
            for line in metadata_section.split('\n'):
                line = line.strip()
                if ':' in line:
                    key, value = line.split(':', 1)
                    key = key.strip().lower()
                    if key == 'title':
                        beatmap_info['title'] = value.strip()
                    elif key == 'artist':
                        beatmap_info['artist'] = value.strip()
                    elif key == 'creator':
                        beatmap_info['creator'] = value.strip()
                    elif key == 'version':
                        beatmap_info['version'] = value.strip()
        
        # Parse difficulty
        difficulty_match = re.search(r'\[Difficulty\](.*?)\[', content, re.DOTALL)
        if difficulty_match:
            diff_section = difficulty_match.group(1)
            for line in diff_section.split('\n'):
                line = line.strip()
                if ':' in line:
                    key, value = line.split(':', 1)
                    key = key.strip()
                    try:
                        if key == 'ApproachRate':
                            beatmap_info['approach_rate'] = float(value.strip())
                        elif key == 'OverallDifficulty':
                            beatmap_info['overall_difficulty'] = float(value.strip())
                    except:
                        pass
        
        # Parse events for background and video
        events_match = re.search(r'\[Events\](.*?)(\[|$)', content, re.DOTALL)
        if events_match:
            events_section = events_match.group(1)
            for line in events_section.split('\n'):
                line = line.strip()
                if line.startswith('0,0,'):  # Background event
                    parts = line.split(',')
                    if len(parts) >= 3:
                        bg_file = parts[2].strip('"')
                        beatmap_info['background'] = bg_file
                elif line.startswith('Video,') or line.startswith('1,'):  # Video event
                    parts = line.split(',')
                    if len(parts) >= 3:
                        video_file = parts[2].strip('"') if line.startswith('Video,') else parts[2].strip('"')
                        beatmap_info['video_files'].append(video_file)
                
                beatmap_info['events'].append(line)
        
        # Simple star rating estimation based on AR and OD
        ar = beatmap_info['approach_rate']
        od = beatmap_info['overall_difficulty']
        beatmap_info['star_rating'] = (ar + od) / 2.0  # Very rough estimate
    
    except Exception as e:
        pass
    
    _beatmap_cache[osu_file_path] = beatmap_info
    return beatmap_info

def is_protected_by_whitelist(folder_path, creator_name=None):
    """Check if a beatmap is protected by whitelist settings"""
    try:
        folder_name = os.path.basename(folder_path)
        
        # Check manual exclude list
        if folder_name in whitelist_data['folders']:
            return True, "Manual exclude list"
        
        # Check mapper whitelist
        if creator_name and creator_name in whitelist_data['mappers']:
            return True, f"Protected mapper: {creator_name}"
        
        # Check recent downloads
        if whitelist_data['recent_days'] > 0:
            folder_stat = os.path.getctime(folder_path)
            cutoff_date = datetime.now() - timedelta(days=whitelist_data['recent_days'])
            if datetime.fromtimestamp(folder_stat) > cutoff_date:
                return True, f"Recent download ({whitelist_data['recent_days']} days)"
        
        return False, ""
    
    except:
        return False, ""

def detect_audio_silence(filepath, threshold_db=-40, min_duration=5.0):
    """Detect silent sections in audio files"""
    try:
        cmd = [
            "ffmpeg", "-i", filepath, "-af", 
            f"silencedetect=noise={threshold_db}dB:d={min_duration}",
            "-f", "null", "-"
        ]
        
        proc = Popen(cmd, stdout=DEVNULL, stderr=PIPE)
        stderr = proc.communicate(timeout=30)[1].decode('utf-8', errors='ignore')
        
        # Parse silence detection output
        silence_starts = re.findall(r'silence_start: ([\d.]+)', stderr)
        silence_ends = re.findall(r'silence_end: ([\d.]+)', stderr)
        
        silent_sections = []
        for i, start in enumerate(silence_starts):
            end = silence_ends[i] if i < len(silence_ends) else None
            if end:
                duration = float(end) - float(start)
                silent_sections.append({
                    'start': float(start),
                    'end': float(end),
                    'duration': duration
                })
        
        return silent_sections
    
    except:
        return []

def normalize_audio_volume(filepath, target_lufs=-16):
    """Normalize audio volume using FFmpeg"""
    try:
        temp_path = filepath + ".normalized.tmp"
        
        # First pass: analyze loudness
        cmd1 = [
            "ffmpeg", "-i", filepath, "-af", "loudnorm=print_format=json",
            "-f", "null", "-"
        ]
        
        proc1 = Popen(cmd1, stdout=DEVNULL, stderr=PIPE)
        stderr1 = proc1.communicate(timeout=30)[1].decode('utf-8', errors='ignore')
        
        # Extract loudness info
        json_match = re.search(r'\{[^}]*"input_i"[^}]*\}', stderr1)
        if not json_match:
            return False
        
        loudness_info = json.loads(json_match.group())
        input_i = loudness_info.get('input_i', '0')
        input_tp = loudness_info.get('input_tp', '0')
        input_lra = loudness_info.get('input_lra', '0')
        input_thresh = loudness_info.get('input_thresh', '0')
        
        # Second pass: apply normalization
        cmd2 = [
            "ffmpeg", "-y", "-i", filepath, "-af",
            f"loudnorm=I={target_lufs}:TP=-1.5:LRA=11:measured_I={input_i}:measured_LRA={input_lra}:measured_TP={input_tp}:measured_thresh={input_thresh}:linear=true:print_format=summary",
            "-c:a", "libmp3lame", temp_path
        ]
        
        proc2 = Popen(cmd2, stdout=DEVNULL, stderr=PIPE)
        if proc2.communicate(timeout=60)[0] is not None and proc2.returncode == 0:
            if os.path.exists(temp_path):
                original_size = get_file_size_cached(filepath)
                new_size = get_file_size_cached(temp_path)
                
                os.replace(temp_path, filepath)
                return True
        
        # Cleanup on failure
        if os.path.exists(temp_path):
            os.unlink(temp_path)
        return False
    
    except:
        return False

def verify_file_integrity(filepath, file_type):
    """Verify file integrity after processing"""
    try:
        if file_type == "audio":
            # Test audio playback
            cmd = ["ffprobe", "-v", "quiet", "-show_entries", "format=duration", filepath]
            proc = Popen(cmd, stdout=PIPE, stderr=DEVNULL)
            output = proc.communicate(timeout=10)[0]
            return proc.returncode == 0 and len(output) > 0
        
        elif file_type == "image":
            # Test image loading
            with Image.open(filepath) as img:
                img.verify()
            return True
        
        elif file_type == "beatmap":
            # Test beatmap parsing
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            return '[General]' in content and '[HitObjects]' in content
        
        return True
    
    except:
        return False

def get_audio_hash_optimized(filepath):
    """Generate hash with caching and optimized chunk size"""
    if filepath in _hash_cache:
        return _hash_cache[filepath]
    
    try:
        chunk_size = min(1024 * 1024, get_file_size_cached(filepath))
        with open(filepath, 'rb') as f:
            chunk = f.read(chunk_size)
            file_hash = hashlib.blake2b(chunk, digest_size=16).hexdigest()
            _hash_cache[filepath] = file_hash
            return file_hash
    except:
        return None

def find_duplicate_beatmaps(songs_folder):
    """Find duplicate beatmaps by analyzing metadata"""
    beatmap_signatures = defaultdict(list)
    
    for folder_path in Path(songs_folder).iterdir():
        if not folder_path.is_dir():
            continue
        
        try:
            # Get all .osu files in the folder
            osu_files = list(folder_path.glob("*.osu"))
            if not osu_files:
                continue
            
            # Parse first .osu file for metadata
            beatmap_info = parse_beatmap_file(str(osu_files[0]))
            if not beatmap_info['title'] or not beatmap_info['artist']:
                continue
            
            # Create signature based on title and artist (normalized)
            title = re.sub(r'[^\w\s]', '', beatmap_info['title'].lower()).strip()
            artist = re.sub(r'[^\w\s]', '', beatmap_info['artist'].lower()).strip()
            signature = f"{artist}_{title}"
            
            beatmap_signatures[signature].append({
                'folder': str(folder_path),
                'title': beatmap_info['title'],
                'artist': beatmap_info['artist'], 
                'creator': beatmap_info['creator'],
                'size': sum(get_file_size_cached(str(f)) for f in folder_path.rglob('*') if f.is_file())
            })
        
        except Exception as e:
            continue
    
    duplicates = []
    for signature, beatmaps in beatmap_signatures.items():
        if len(beatmaps) > 1:
            # Sort by size (keep largest) and creation date
            beatmaps.sort(key=lambda x: (-x['size'], os.path.getctime(x['folder'])))
            duplicates.extend(beatmaps[1:])  # Mark all but the first as duplicates
    
    return duplicates

def analyze_mapset_sizes(songs_folder):
    """Analyze and rank beatmap sets by size"""
    mapset_sizes = []
    
    for folder_path in Path(songs_folder).iterdir():
        if not folder_path.is_dir():
            continue
        
        try:
            total_size = 0
            file_breakdown = {'audio': 0, 'images': 0, 'videos': 0, 'other': 0}
            
            for file_path in folder_path.rglob('*'):
                if file_path.is_file():
                    size = get_file_size_cached(str(file_path))
                    total_size += size
                    
                    ext = file_path.suffix.lower()
                    if ext in AUDIO_EXTENSIONS:
                        file_breakdown['audio'] += size
                    elif ext in IMAGE_EXTENSIONS:
                        file_breakdown['images'] += size
                    elif ext in VIDEO_EXTENSIONS:
                        file_breakdown['videos'] += size
                    else:
                        file_breakdown['other'] += size
            
            if total_size > 0:
                mapset_sizes.append({
                    'folder': folder_path.name,
                    'path': str(folder_path),
                    'total_size': total_size,
                    'breakdown': file_breakdown
                })
        
        except:
            continue
    
    return sorted(mapset_sizes, key=lambda x: x['total_size'], reverse=True)

def detect_corrupted_files(songs_folder):
    """Detect corrupted or problematic files"""
    corrupted_files = []
    
    for folder_path in Path(songs_folder).iterdir():
        if not folder_path.is_dir():
            continue
        
        try:
            for file_path in folder_path.rglob('*'):
                if not file_path.is_file():
                    continue
                
                filepath_str = str(file_path)
                ext = file_path.suffix.lower()
                
                # Check audio files
                if ext in AUDIO_EXTENSIONS:
                    if not verify_file_integrity(filepath_str, "audio"):
                        corrupted_files.append({
                            'path': filepath_str,
                            'type': 'audio',
                            'reason': 'Corrupted or unreadable audio file'
                        })
                
                # Check image files
                elif ext in IMAGE_EXTENSIONS:
                    if not verify_file_integrity(filepath_str, "image"):
                        corrupted_files.append({
                            'path': filepath_str,
                            'type': 'image', 
                            'reason': 'Corrupted or unreadable image file'
                        })
                
                # Check .osu files
                elif ext == '.osu':
                    if not verify_file_integrity(filepath_str, "beatmap"):
                        corrupted_files.append({
                            'path': filepath_str,
                            'type': 'beatmap',
                            'reason': 'Invalid or corrupted .osu file'
                        })
                
                # Check for broken symlinks
                elif file_path.is_symlink() and not file_path.exists():
                    corrupted_files.append({
                        'path': filepath_str,
                        'type': 'symlink',
                        'reason': 'Broken symbolic link'
                    })
        
        except:
            continue
    
    return corrupted_files

def compress_audio_ffmpeg_optimized(filepath, target_bitrate, mono_mode=False, normalize=False, genre_based=False):
    """Enhanced audio compression with genre awareness and normalization"""
    temp_path = filepath + ".temp.mp3"
    original_size = get_file_size_cached(filepath)
    
    # Genre-based bitrate selection
    if genre_based:
        audio_info = get_audio_info(filepath)
        genre = audio_info.get('genre', 'Default')
        if genre in GENRE_BITRATES:
            target_bitrate = GENRE_BITRATES[genre]
        
        # Skip if already at or below target bitrate
        current_bitrate = audio_info.get('bitrate', 0)
        target_bitrate_num = int(target_bitrate.rstrip('k')) * 1000
        if current_bitrate > 0 and current_bitrate <= target_bitrate_num:
            return 0  # Already optimally compressed
    
    # Normalize volume first if requested
    if normalize:
        normalize_audio_volume(filepath)
    
    # Build FFmpeg command
    cmd = [
        "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
        "-i", filepath,
        "-c:a", "libmp3lame",
        "-ar", "44100",
        "-ac", "1" if mono_mode else "2",
        "-b:a", target_bitrate,
        "-minrate", target_bitrate,
        "-maxrate", target_bitrate,
        "-bufsize", target_bitrate,
        "-vn", "-f", "mp3",
        temp_path
    ]
    
    try:
        proc = Popen(cmd, stdout=DEVNULL, stderr=PIPE)
        stdout, stderr = proc.communicate(timeout=60)
        
        if proc.returncode == 0 and os.path.exists(temp_path):
            compressed_size = get_file_size_cached(temp_path)
            
            if compressed_size > 0 and compressed_size < original_size:
                # Verify integrity
                if verify_file_integrity(temp_path, "audio"):
                    os.replace(temp_path, filepath)
                    
                    # Log compression stats for analytics
                    if analytics_db:
                        try:
                            analytics_db.execute('''
                                INSERT INTO file_stats (file_type, original_size, compressed_size, compression_ratio)
                                VALUES (?, ?, ?, ?)
                            ''', ('audio', original_size, compressed_size, compressed_size / original_size))
                        except:
                            pass
                    
                    return original_size - compressed_size
            
            # Clean up on failure
            if os.path.exists(temp_path):
                os.unlink(temp_path)
        
        return 0
    
    except Exception as e:
        if os.path.exists(temp_path):
            try:
                os.unlink(temp_path)
            except:
                pass
        return 0

def batch_delete_files(file_list, dry_run=False):
    """Optimized batch file deletion with verification"""
    if dry_run:
        return sum(get_file_size_cached(f) for f in file_list)
    
    total_saved = 0
    dir_groups = defaultdict(list)
    
    for file_path in file_list:
        dir_groups[os.path.dirname(file_path)].append(file_path)
    
    for directory, files in dir_groups.items():
        for file_path in files:
            try:
                size = get_file_size_cached(file_path)
                os.unlink(file_path)
                total_saved += size
            except:
                continue
    
    return total_saved

def is_background_image(filepath, folder_path):
    """Enhanced background image detection"""
    try:
        beatmap_folder = os.path.dirname(filepath)
        filename = os.path.basename(filepath)
        
        # Check .osu files for background references
        for osu_file in os.listdir(beatmap_folder):
            if osu_file.endswith('.osu'):
                osu_path = os.path.join(beatmap_folder, osu_file)
                beatmap_info = parse_beatmap_file(osu_path)
                if beatmap_info['background'] == filename:
                    return True
        
        # Enhanced filename pattern detection
        filename_lower = filename.lower()
        bg_indicators = ['bg', 'background', 'back', 'wallpaper', 'wp', 'bkg', 'cover', 'album']
        if any(indicator in filename_lower for indicator in bg_indicators):
            return True
            
        # Check if it's the largest image in the folder (likely background)
        try:
            current_size = get_file_size_cached(filepath)
            max_size = 0
            for other_file in os.listdir(beatmap_folder):
                if other_file.lower().endswith(('.png', '.jpg', '.jpeg')):
                    other_path = os.path.join(beatmap_folder, other_file)
                    if other_path != filepath:
                        other_size = get_file_size_cached(other_path)
                        max_size = max(max_size, other_size)
            
            if current_size > max_size:
                return True
        except:
            pass
        
        # Final fallback: assume large images are backgrounds
        try:
            with Image.open(filepath) as img:
                w, h = img.size
                return w >= 800 and h >= 600
        except:
            return False
    
    except:
        return False

def resize_image_optimized(path, max_dim, bg_mode, extreme_mode, folder_path=None):
    """Enhanced image processing with better background detection"""
    try:
        path_obj = Path(path)
        original_size = get_file_size_cached(path)
        
        if original_size < 1024:
            return 0
        
        is_background = is_background_image(path, folder_path)
        
        # Remove completely option
        if is_background and bg_mode == "Remove Completely":
            try:
                os.unlink(path)
                return original_size
            except:
                return 0
        
        with Image.open(path) as img:
            w, h = img.size
            
            if (max_dim > 0 and w <= max_dim and h <= max_dim and 
                not extreme_mode and bg_mode == "Keep Original"):
                return 0
            
            # Apply black & white filter if requested
            if bg_mode == "Black & White" and is_background:
                img = img.convert("L").convert("RGB")
            
            # Resize logic
            needs_resize = False
            if max_dim > 0 and (w > max_dim or h > max_dim):
                ratio = min(max_dim / w, max_dim / h)
                new_size = (int(w * ratio), int(h * ratio))
                resample = Image.LANCZOS if ratio < 1 else Image.BICUBIC
                img = img.resize(new_size, resample)
                needs_resize = True
            
            if (needs_resize or extreme_mode or 
                (bg_mode == "Black & White" and is_background)):
                
                if img.mode in ("RGBA", "P"):
                    background = Image.new('RGB', img.size, (255, 255, 255))
                    if img.mode == "RGBA":
                        background.paste(img, mask=img.split()[-1])
                    else:
                        background.paste(img)
                    img = background
                
                quality = 50 if extreme_mode else 85
                
                jpeg_path = str(path_obj.with_suffix('.jpg'))
                img.save(jpeg_path, "JPEG", quality=quality, optimize=True, progressive=True)
                
                if path.lower().endswith('.png'):
                    os.unlink(path)
                
                # Verify integrity
                if verify_file_integrity(jpeg_path, "image"):
                    new_size = get_file_size_cached(jpeg_path)
                    return max(0, original_size - new_size)
                else:
                    # Restore original if verification failed
                    if not path.lower().endswith('.png'):
                        os.rename(jpeg_path, path)
            
            return 0
    except Exception as e:
        return 0

def remove_videos_from_beatmap(beatmap_folder, dry_run=False):
    """Enhanced video removal with .osu file updates"""
    removed_size = 0
    
    try:
        video_files = []
        for file in os.listdir(beatmap_folder):
            if file.lower().endswith(tuple(VIDEO_EXTENSIONS)):
                video_files.append(os.path.join(beatmap_folder, file))
        
        if not video_files:
            return 0
        
        for video_path in video_files:
            video_name = os.path.basename(video_path)
            removed_size += get_file_size_cached(video_path)
            
            if not dry_run:
                os.unlink(video_path)
                
                # Update .osu files to remove video references
                for osu_file in os.listdir(beatmap_folder):
                    if osu_file.endswith('.osu'):
                        osu_path = os.path.join(beatmap_folder, osu_file)
                        try:
                            with open(osu_path, 'r', encoding='utf-8', errors='ignore') as f:
                                content = f.read()
                            
                            # Remove video lines from [Events] section
                            lines = content.split('\n')
                            new_lines = []
                            for line in lines:
                                if video_name not in line or not (line.strip().startswith('Video,') or line.strip().startswith('1,')):
                                    new_lines.append(line)
                            
                            with open(osu_path, 'w', encoding='utf-8', errors='ignore') as f:
                                f.write('\n'.join(new_lines))
                        except:
                            continue
    
    except:
        pass
    
    return removed_size

def scan_folder_optimized(folder, remove_hitsounds, remove_audio, remove_images, remove_storyboards, 
                         find_duplicates, process_osz, extra_features, enable_smart_detection):
    """Enhanced folder scanning with smart detection"""
    deletions = []
    audios = []
    images_to_convert = []
    storyboards = []
    osz_files = []
    videos = []
    unused_images = []
    empty_folders = []
    corrupted_files = []
    duplicate_beatmaps = []
    large_files = []
    silent_hitsounds = []
    broken_symlinks = []
    
    audio_hashes = defaultdict(list) if find_duplicates else None
    folder_path = Path(folder)
    
    # Smart detection features
    if enable_smart_detection:
        corrupted_files = detect_corrupted_files(folder)
        duplicate_beatmaps = find_duplicate_beatmaps(folder)
    
    # Single pass through all files
    for file_path in folder_path.rglob('*'):
        if not file_path.is_file():
            continue
            
        ext = file_path.suffix.lower()
        full_path = str(file_path)
        file_size = get_file_size_cached(full_path)
        
        # Check for large files (>50MB)
        if enable_smart_detection and file_size > 50 * 1024 * 1024:
            large_files.append({
                'path': full_path,
                'size': file_size,
                'type': ext
            })
        
        # Check for broken symlinks
        if enable_smart_detection and file_path.is_symlink() and not file_path.exists():
            broken_symlinks.append(full_path)
        
        # Regular processing
        if process_osz and ext in OSZ_EXTENSIONS:
            osz_files.append(full_path)
        elif remove_hitsounds and ext in HITSOUND_EXTENSIONS:
            # Check for silent hitsounds if smart detection is enabled
            if enable_smart_detection:
                try:
                    with wave.open(full_path, 'rb') as wav_file:
                        frames = wav_file.readframes(wav_file.getnframes())
                        if len(frames) > 0:
                            # Simple silence detection for WAV files
                            max_amplitude = max(struct.unpack(f'{len(frames)//2}h', frames))
                            if max_amplitude < 100:  # Very quiet
                                silent_hitsounds.append(full_path)
                except:
                    pass
            
            deletions.append(full_path)
        elif remove_audio and ext in AUDIO_EXTENSIONS:
            audios.append(full_path)
            if find_duplicates:
                file_hash = get_audio_hash_optimized(full_path)
                if file_hash:
                    audio_hashes[file_hash].append(full_path)
        elif remove_images and ext in IMAGE_EXTENSIONS:
            images_to_convert.append(full_path)
        elif remove_storyboards and ext in STORYBOARD_EXTENSIONS:
            storyboards.append(full_path)
        elif "Remove Videos" in extra_features and ext in VIDEO_EXTENSIONS:
            videos.append(full_path)
    
    # Process duplicates
    duplicate_audios = []
    if find_duplicates and audio_hashes:
        for paths in audio_hashes.values():
            if len(paths) > 1:
                paths.sort(key=get_file_size_cached)
                duplicate_audios.extend(paths[1:])
    
    # Find unused images
    if "Remove Unused Images" in extra_features:
        for beatmap_folder in folder_path.iterdir():
            if beatmap_folder.is_dir():
                try:
                    osu_content = ""
                    for osu_file in beatmap_folder.glob("*.osu"):
                        try:
                            with open(osu_file, 'r', encoding='utf-8', errors='ignore') as f:
                                osu_content += f.read()
                        except:
                            continue
                    
                    for img_file in beatmap_folder.glob("*"):
                        if img_file.suffix.lower() in IMAGE_EXTENSIONS:
                            img_name = img_file.name
                            if img_name not in osu_content and f'"{img_name}"' not in osu_content:
                                unused_images.append(str(img_file))
                except:
                    continue
    
    # Find empty folders
    if "Clean Empty Folders" in extra_features:
        for folder_path_item in folder_path.rglob('*'):
            if folder_path_item.is_dir():
                try:
                    if not any(folder_path_item.iterdir()):
                        empty_folders.append(str(folder_path_item))
                except:
                    continue
    
    return (deletions, audios, images_to_convert, storyboards, duplicate_audios, osz_files, 
            videos, unused_images, empty_folders, corrupted_files, duplicate_beatmaps, 
            large_files, silent_hitsounds, broken_symlinks)

def process_files_parallel(file_list, process_func, *args, max_workers=None):
    """Generic parallel file processor with progress tracking"""
    if not file_list:
        return []
    
    if max_workers is None:
        max_workers = get_thread_count()
    
    results = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        if process_func.__name__ == 'resize_image_optimized':
            future_to_file = {
                executor.submit(process_func, filepath, *args, os.path.dirname(filepath)): filepath 
                for filepath in file_list
            }
        else:
            future_to_file = {
                executor.submit(process_func, filepath, *args): filepath 
                for filepath in file_list
            }
        
        for future in as_completed(future_to_file):
            try:
                result = future.result(timeout=30)
                results.append(result)
            except:
                results.append(0)
    
    return results

def process_osz_file_optimized(osz_path, remove_hitsounds, remove_audio, remove_images, remove_storyboards, 
                              mp3_bitrate, bg_mode, extreme_mode, mono_mode, max_dim, dry_run, 
                              normalize_audio, genre_based):
    """Enhanced OSZ processing"""
    try:
        original_size = get_file_size_cached(osz_path)
        
        if dry_run:
            return original_size * 0.35, 1
        
        with tempfile.TemporaryDirectory() as temp_dir:
            extract_dir = Path(temp_dir) / "extracted"
            extract_dir.mkdir()
            
            with zipfile.ZipFile(osz_path, 'r') as zip_ref:
                zip_ref.extractall(extract_dir)
            
            total_saved = 0
            files_to_process = {'audio': [], 'images': [], 'delete': []}
            
            for file_path in extract_dir.rglob('*'):
                if not file_path.is_file():
                    continue
                    
                ext = file_path.suffix.lower()
                full_path = str(file_path)
                
                if remove_hitsounds and ext in HITSOUND_EXTENSIONS:
                    files_to_process['delete'].append(full_path)
                elif remove_audio and ext in AUDIO_EXTENSIONS:
                    files_to_process['audio'].append(full_path)
                elif remove_images and ext in IMAGE_EXTENSIONS:
                    files_to_process['images'].append(full_path)
                elif remove_storyboards and ext in STORYBOARD_EXTENSIONS:
                    files_to_process['delete'].append(full_path)
            
            if files_to_process['delete']:
                total_saved += batch_delete_files(files_to_process['delete'])
            
            if files_to_process['audio']:
                results = process_files_parallel(
                    files_to_process['audio'],
                    compress_audio_ffmpeg_optimized,
                    mp3_bitrate, mono_mode, normalize_audio, genre_based,
                    max_workers=min(4, len(files_to_process['audio']))
                )
                total_saved += sum(r for r in results if r)
            
            if files_to_process['images']:
                results = process_files_parallel(
                    files_to_process['images'],
                    resize_image_optimized,
                    max_dim, bg_mode, extreme_mode,
                    max_workers=min(6, len(files_to_process['images']))
                )
                total_saved += sum(r for r in results if r)
            
            # Recompress with maximum compression
            temp_osz = Path(temp_dir) / "temp.osz"
            with zipfile.ZipFile(temp_osz, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zip_ref:
                for file_path in extract_dir.rglob('*'):
                    if file_path.is_file():
                        arcname = file_path.relative_to(extract_dir)
                        zip_ref.write(file_path, arcname)
            
            shutil.move(str(temp_osz), osz_path)
            
            new_size = get_file_size_cached(osz_path)
            final_saved = original_size - new_size
            
            return max(final_saved, total_saved), 1
    
    except Exception as e:
        return 0, 0

def save_analytics_session(total_saved, stats, time_taken, settings):
    """Save cleanup session to analytics database"""
    if not analytics_db:
        return
    
    try:
        cursor = analytics_db.execute('''
            INSERT INTO cleanup_sessions (timestamp, total_saved, files_processed, duration, settings)
            VALUES (?, ?, ?, ?, ?)
        ''', (
            datetime.now().isoformat(),
            total_saved,
            sum(stats.values()),
            time_taken,
            json.dumps(settings)
        ))
        
        analytics_db.commit()
        return cursor.lastrowid
    except Exception as e:
        print(f"Failed to save analytics: {e}")
        return None

def generate_analytics_report():
    """Generate analytics report"""
    if not analytics_db:
        return "Analytics database not available"
    
    try:
        # Get recent sessions
        sessions = analytics_db.execute('''
            SELECT timestamp, total_saved, files_processed, duration
            FROM cleanup_sessions
            ORDER BY timestamp DESC
            LIMIT 10
        ''').fetchall()
        
        if not sessions:
            return "No cleanup sessions recorded yet"
        
        report = "=== osu! Cleaner Analytics Report ===\n\n"
        
        total_saved = sum(s[1] for s in sessions)
        total_files = sum(s[2] for s in sessions)
        total_time = sum(s[3] for s in sessions)
        
        report += f"Total space saved: {format_size(total_saved)}\n"
        report += f"Total files processed: {total_files:,}\n"
        report += f"Total processing time: {total_time:.1f} seconds\n"
        report += f"Average speed: {total_files/max(total_time, 1):.1f} files/second\n\n"
        
        report += "Recent Sessions:\n"
        for session in sessions[:5]:
            timestamp, saved, files, duration = session
            dt = datetime.fromisoformat(timestamp)
            report += f"  {dt.strftime('%Y-%m-%d %H:%M')}: {format_size(saved)} saved, {files} files, {duration:.1f}s\n"
        
        return report
    
    except Exception as e:
        return f"Error generating report: {e}"

def threaded_cleanup_optimized(folder, remove_hitsounds, remove_audio, remove_images, remove_storyboards, 
                              find_duplicates, process_osz, mp3_bitrate, progress_callback, done_callback, 
                              dry_run, extra_features, advanced_options):
    global stop_requested
    
    start_time = time.time()
    
    # Clear caches
    _size_cache.clear()
    _hash_cache.clear()
    _audio_info_cache.clear()
    _beatmap_cache.clear()
    
    # Enhanced scanning
    progress_callback(0, 100, "Scanning files with advanced detection...")
    scan_result = scan_folder_optimized(
        folder, remove_hitsounds, remove_audio, remove_images, remove_storyboards, 
        find_duplicates, process_osz, extra_features, advanced_options.get('smart_detection', False)
    )
    
    (deletions, audios, images, storyboards, duplicate_audios, osz_files, 
     videos, unused_images, empty_folders, corrupted_files, duplicate_beatmaps, 
     large_files, silent_hitsounds, broken_symlinks) = scan_result
    
    # Apply whitelist protection
    protected_count = 0
    if advanced_options.get('enable_whitelist', False):
        # Filter out protected beatmaps
        all_file_lists = [deletions, audios, images, storyboards, duplicate_audios, videos, unused_images]
        for file_list in all_file_lists:
            i = 0
            while i < len(file_list):
                folder_path = os.path.dirname(file_list[i])
                # Get creator name from .osu files
                creator_name = None
                try:
                    for osu_file in Path(folder_path).glob("*.osu"):
                        beatmap_info = parse_beatmap_file(str(osu_file))
                        creator_name = beatmap_info.get('creator', '')
                        break
                except:
                    pass
                
                is_protected, reason = is_protected_by_whitelist(folder_path, creator_name)
                if is_protected:
                    file_list.pop(i)
                    protected_count += 1
                else:
                    i += 1
    
    # Get processing parameters
    max_dim = 0
    resize_mode = image_quality_var.get()
    bg_mode = background_var.get()
    extreme_mode = extreme_var.get()
    mono_mode = mono_var.get()
    normalize_audio = advanced_options.get('normalize_audio', False)
    genre_based = advanced_options.get('genre_based_compression', False)
    
    if resize_mode == "480p":
        max_dim = 640
    elif resize_mode == "720p":
        max_dim = 1280
    elif resize_mode == "1080p":
        max_dim = 1920
    elif resize_mode == "1440p":
        max_dim = 2560

    total_tasks = (len(deletions) + len(audios) + len(images) + len(storyboards) + 
                   len(duplicate_audios) + len(osz_files) + len(videos) + 
                   len(unused_images) + len(empty_folders) + len(broken_symlinks))
    
    if total_tasks == 0:
        stats = {"hitsounds": 0, "audio": 0, "images": 0, "storyboards": 0, 
                "duplicates": 0, "osz": 0, "videos": 0, "unused": 0, "folders": 0,
                "corrupted": len(corrupted_files), "duplicate_beatmaps": len(duplicate_beatmaps),
                "large_files": len(large_files), "protected": protected_count}
        done_callback(0, stats, 0)
        return
    
    current = 0
    total_saved = 0
    stats = {"hitsounds": 0, "audio": 0, "images": 0, "storyboards": 0, "duplicates": 0, 
             "osz": 0, "videos": 0, "unused": 0, "folders": 0, "corrupted": len(corrupted_files),
             "duplicate_beatmaps": len(duplicate_beatmaps), "large_files": len(large_files), 
             "protected": protected_count, "broken_symlinks": 0}

    # Enhanced batch operations
    operations = [
        ("hitsounds", deletions, lambda files: batch_delete_files(files, dry_run)),
        ("storyboards", storyboards, lambda files: batch_delete_files(files, dry_run)),
        ("duplicates", duplicate_audios, lambda files: batch_delete_files(files, dry_run)),
        ("videos", videos, lambda files: batch_delete_files(files, dry_run)),
        ("unused", unused_images, lambda files: batch_delete_files(files, dry_run)),
        ("broken_symlinks", broken_symlinks, lambda files: batch_delete_files(files, dry_run)),
    ]
    
    # Process batch deletions
    for op_name, file_list, operation in operations:
        if file_list and not stop_requested:
            progress_callback(current, total_tasks, f"Processing {len(file_list)} {op_name}...")
            
            if not dry_run:
                saved = operation(file_list)
                total_saved += saved
                stats[op_name] = len(file_list)
            else:
                stats[op_name] = len(file_list)
                if op_name != "broken_symlinks":  # Symlinks have no size
                    total_saved += sum(get_file_size_cached(f) for f in file_list if os.path.exists(f))
            
            current += len(file_list)
            progress_callback(current, total_tasks, f"{'Would process' if dry_run else 'Processed'} {stats[op_name]} {op_name}")

    # Clean empty folders
    if empty_folders and not stop_requested:
        progress_callback(current, total_tasks, f"Cleaning {len(empty_folders)} empty folders...")
        
        if not dry_run:
            for folder_path in empty_folders:
                try:
                    os.rmdir(folder_path)
                    stats["folders"] += 1
                except:
                    continue
        else:
            stats["folders"] = len(empty_folders)
        
        current += len(empty_folders)
        progress_callback(current, total_tasks, f"{'Would clean' if dry_run else 'Cleaned'} {stats['folders']} empty folders")

    # Process audio files with enhanced features
    if audios and not stop_requested:
        progress_callback(current, total_tasks, f"Compressing {len(audios)} audio files...")
        
        if not dry_run:
            results = process_files_parallel(audios, compress_audio_ffmpeg_optimized, 
                                           mp3_bitrate, mono_mode, normalize_audio, genre_based)
            for result in results:
                if result:
                    stats["audio"] += 1
                    total_saved += result
        else:
            stats["audio"] = len(audios)
            total_saved += sum(get_file_size_cached(f) * 0.4 for f in audios)
        
        current += len(audios)
        progress_callback(current, total_tasks, f"{'Would compress' if dry_run else 'Compressed'} {stats['audio']} audio files")

    # Process images with verification
    if images and not stop_requested and (max_dim > 0 or bg_mode != "Keep Original" or extreme_mode):
        progress_callback(current, total_tasks, f"Processing {len(images)} images...")
        
        if not dry_run:
            results = process_files_parallel(images, resize_image_optimized, max_dim, bg_mode, extreme_mode)
            for result in results:
                if result:
                    stats["images"] += 1
                    total_saved += result
        else:
            stats["images"] = len(images)
            total_saved += sum(get_file_size_cached(f) * 0.3 for f in images)
        
        current += len(images)
        progress_callback(current, total_tasks, f"{'Would process' if dry_run else 'Processed'} {stats['images']} images")

    # Process OSZ files
    for i, osz in enumerate(osz_files):
        if stop_requested:
            break
        
        progress_callback(current, total_tasks, f"Processing OSZ {i+1}/{len(osz_files)}: {Path(osz).name}")
        
        size_saved, processed = process_osz_file_optimized(
            osz, remove_hitsounds, remove_audio, remove_images, remove_storyboards,
            mp3_bitrate, bg_mode, extreme_mode, mono_mode, max_dim, dry_run,
            normalize_audio, genre_based
        )
        
        if processed:
            stats["osz"] += 1
            total_saved += size_saved
        
        current += 1

    # Save analytics
    end_time = time.time()
    time_taken = end_time - start_time
    
    if not dry_run:
        settings = {
            'bitrate': mp3_bitrate,
            'image_quality': resize_mode,
            'background_mode': bg_mode,
            'extreme_mode': extreme_mode,
            'mono_mode': mono_mode,
            'normalize_audio': normalize_audio,
            'genre_based': genre_based
        }
        save_analytics_session(total_saved, stats, time_taken, settings)
    
    done_callback(total_saved, stats, time_taken)

# GUI Enhancement Functions
def open_whitelist_editor():
    """Open whitelist configuration window"""
    whitelist_window = tk.Toplevel(root)
    whitelist_window.title("Whitelist Configuration")
    whitelist_window.geometry("600x500")
    whitelist_window.configure(bg="#222")
    
    # Mappers section
    mappers_frame = ttk.LabelFrame(whitelist_window, text="Protected Mappers")
    mappers_frame.pack(padx=10, pady=10, fill="both", expand=True)
    
    mappers_listbox = tk.Listbox(mappers_frame, bg="#333", fg="#EEE", selectbackground="#555")
    mappers_listbox.pack(side="left", fill="both", expand=True, padx=5, pady=5)
    
    mappers_scroll = ttk.Scrollbar(mappers_frame, orient="vertical", command=mappers_listbox.yview)
    mappers_scroll.pack(side="right", fill="y")
    mappers_listbox.config(yscrollcommand=mappers_scroll.set)
    
    # Load current mappers
    for mapper in whitelist_data['mappers']:
        mappers_listbox.insert(tk.END, mapper)
    
    mappers_buttons = tk.Frame(mappers_frame, bg="#222")
    mappers_buttons.pack(side="bottom", fill="x", padx=5, pady=5)
    
    mapper_entry = ttk.Entry(mappers_buttons, width=30)
    mapper_entry.pack(side="left", padx=5)
    
    def add_mapper():
        mapper = mapper_entry.get().strip()
        if mapper and mapper not in whitelist_data['mappers']:
            whitelist_data['mappers'].add(mapper)
            mappers_listbox.insert(tk.END, mapper)
            mapper_entry.delete(0, tk.END)
    
    def remove_mapper():
        selection = mappers_listbox.curselection()
        if selection:
            mapper = mappers_listbox.get(selection[0])
            whitelist_data['mappers'].discard(mapper)
            mappers_listbox.delete(selection[0])
    
    ttk.Button(mappers_buttons, text="Add", command=add_mapper).pack(side="left", padx=5)
    ttk.Button(mappers_buttons, text="Remove", command=remove_mapper).pack(side="left", padx=5)
    
    # Folders section
    folders_frame = ttk.LabelFrame(whitelist_window, text="Protected Folders (Exact Names)")
    folders_frame.pack(padx=10, pady=5, fill="both", expand=True)
    
    folders_listbox = tk.Listbox(folders_frame, bg="#333", fg="#EEE", selectbackground="#555")
    folders_listbox.pack(side="left", fill="both", expand=True, padx=5, pady=5)
    
    folders_scroll = ttk.Scrollbar(folders_frame, orient="vertical", command=folders_listbox.yview)
    folders_scroll.pack(side="right", fill="y")
    folders_listbox.config(yscrollcommand=folders_scroll.set)
    
    # Load current folders
    for folder in whitelist_data['folders']:
        folders_listbox.insert(tk.END, folder)
    
    folders_buttons = tk.Frame(folders_frame, bg="#222")
    folders_buttons.pack(side="bottom", fill="x", padx=5, pady=5)
    
    folder_entry = ttk.Entry(folders_buttons, width=30)
    folder_entry.pack(side="left", padx=5)
    
    def add_folder():
        folder = folder_entry.get().strip()
        if folder and folder not in whitelist_data['folders']:
            whitelist_data['folders'].add(folder)
            folders_listbox.insert(tk.END, folder)
            folder_entry.delete(0, tk.END)
    
    def remove_folder():
        selection = folders_listbox.curselection()
        if selection:
            folder = folders_listbox.get(selection[0])
            whitelist_data['folders'].discard(folder)
            folders_listbox.delete(selection[0])
    
    ttk.Button(folders_buttons, text="Add", command=add_folder).pack(side="left", padx=5)
    ttk.Button(folders_buttons, text="Remove", command=remove_folder).pack(side="left", padx=5)
    
    # Recent downloads protection
    recent_frame = ttk.LabelFrame(whitelist_window, text="Recent Downloads Protection")
    recent_frame.pack(padx=10, pady=5, fill="x")
    
    recent_days_var = tk.IntVar(value=whitelist_data['recent_days'])
    
    ttk.Label(recent_frame, text="Protect downloads from last").pack(side="left", padx=5)
    recent_spinbox = ttk.Spinbox(recent_frame, from_=0, to=30, textvariable=recent_days_var, width=5)
    recent_spinbox.pack(side="left", padx=5)
    ttk.Label(recent_frame, text="days (0 = disabled)").pack(side="left", padx=5)
    
    # Save button
    def save_and_close():
        whitelist_data['recent_days'] = recent_days_var.get()
        save_whitelist()
        whitelist_window.destroy()
    
    ttk.Button(whitelist_window, text="Save & Close", command=save_and_close).pack(pady=10)

def open_analytics_window():
    """Open analytics and reporting window"""
    analytics_window = tk.Toplevel(root)
    analytics_window.title("Analytics & Reports")
    analytics_window.geometry("800x600")
    analytics_window.configure(bg="#222")
    
    notebook = ttk.Notebook(analytics_window)
    notebook.pack(fill="both", expand=True, padx=10, pady=10)
    
    # Analytics Report Tab
    report_frame = ttk.Frame(notebook)
    notebook.add(report_frame, text="Analytics Report")
    
    report_text = scrolledtext.ScrolledText(report_frame, bg="#333", fg="#EEE", font=("Consolas", 10))
    report_text.pack(fill="both", expand=True, padx=10, pady=10)
    
    def refresh_report():
        report_text.delete(1.0, tk.END)
        report_text.insert(1.0, generate_analytics_report())
    
    ttk.Button(report_frame, text="Refresh Report", command=refresh_report).pack(pady=5)
    refresh_report()
    
    # Mapset Analysis Tab
    analysis_frame = ttk.Frame(notebook)
    notebook.add(analysis_frame, text="Mapset Analysis")
    
    analysis_text = scrolledtext.ScrolledText(analysis_frame, bg="#333", fg="#EEE", font=("Consolas", 10))
    analysis_text.pack(fill="both", expand=True, padx=10, pady=10)
    
    def analyze_mapsets():
        folder = folder_var.get()
        if not folder or not os.path.isdir(folder):
            messagebox.showerror("Error", "Please select a valid Songs folder first.")
            return
        
        analysis_text.delete(1.0, tk.END)
        analysis_text.insert(1.0, "Analyzing mapsets... Please wait...")
        analysis_window.update()
        
        try:
            mapset_sizes = analyze_mapset_sizes(folder)
            
            report = "=== Mapset Size Analysis ===\n\n"
            report += f"Top 20 Largest Mapsets:\n"
            
            for i, mapset in enumerate(mapset_sizes[:20], 1):
                report += f"{i:2d}. {mapset['folder'][:60]}...\n"
                report += f"     Total: {format_size(mapset['total_size'])}\n"
                breakdown = mapset['breakdown']
                report += f"     Audio: {format_size(breakdown['audio'])}, "
                report += f"Images: {format_size(breakdown['images'])}, "
                report += f"Videos: {format_size(breakdown['videos'])}, "
                report += f"Other: {format_size(breakdown['other'])}\n\n"
            
            # Summary statistics
            total_size = sum(m['total_size'] for m in mapset_sizes)
            total_audio = sum(m['breakdown']['audio'] for m in mapset_sizes)
            total_images = sum(m['breakdown']['images'] for m in mapset_sizes)
            total_videos = sum(m['breakdown']['videos'] for m in mapset_sizes)
            
            report += f"=== Summary ===\n"
            report += f"Total mapsets analyzed: {len(mapset_sizes)}\n"
            report += f"Total size: {format_size(total_size)}\n"
            report += f"Audio files: {format_size(total_audio)} ({total_audio/total_size*100:.1f}%)\n"
            report += f"Image files: {format_size(total_images)} ({total_images/total_size*100:.1f}%)\n"
            report += f"Video files: {format_size(total_videos)} ({total_videos/total_size*100:.1f}%)\n"
            
            analysis_text.delete(1.0, tk.END)
            analysis_text.insert(1.0, report)
        
        except Exception as e:
            analysis_text.delete(1.0, tk.END)
            analysis_text.insert(1.0, f"Analysis failed: {str(e)}")
    
    ttk.Button(analysis_frame, text="Analyze Current Songs Folder", command=analyze_mapsets).pack(pady=5)
    
    # Duplicate Detection Tab
    duplicates_frame = ttk.Frame(notebook)
    notebook.add(duplicates_frame, text="Duplicate Detection")
    
    duplicates_text = scrolledtext.ScrolledText(duplicates_frame, bg="#333", fg="#EEE", font=("Consolas", 10))
    duplicates_text.pack(fill="both", expand=True, padx=10, pady=10)
    
    def find_duplicates():
        folder = folder_var.get()
        if not folder or not os.path.isdir(folder):
            messagebox.showerror("Error", "Please select a valid Songs folder first.")
            return
        
        duplicates_text.delete(1.0, tk.END)
        duplicates_text.insert(1.0, "Finding duplicate beatmaps... Please wait...")
        duplicates_frame.update()
        
        try:
            duplicate_beatmaps = find_duplicate_beatmaps(folder)
            
            if not duplicate_beatmaps:
                duplicates_text.delete(1.0, tk.END)
                duplicates_text.insert(1.0, "No duplicate beatmaps found!")
                return
            
            report = f"=== Found {len(duplicate_beatmaps)} Duplicate Beatmaps ===\n\n"
            
            total_wasted_space = 0
            for i, dup in enumerate(duplicate_beatmaps, 1):
                report += f"{i:3d}. {dup['title']} - {dup['artist']}\n"
                report += f"     Mapper: {dup['creator']}\n"
                report += f"     Size: {format_size(dup['size'])}\n"
                report += f"     Folder: {os.path.basename(dup['folder'])}\n\n"
                total_wasted_space += dup['size']
            
            report += f"Total wasted space from duplicates: {format_size(total_wasted_space)}\n"
            
            duplicates_text.delete(1.0, tk.END)
            duplicates_text.insert(1.0, report)
        
        except Exception as e:
            duplicates_text.delete(1.0, tk.END)
            duplicates_text.insert(1.0, f"Duplicate detection failed: {str(e)}")
    
    ttk.Button(duplicates_frame, text="Find Duplicate Beatmaps", command=find_duplicates).pack(pady=5)

def get_bitrate_from_selection():
    """Get bitrate with validation"""
    mp3_quality_label = mp3_quality_var.get()
    mp3_bitrate = BITRATE_OPTIONS.get(mp3_quality_label, "128k")
    
    if mp3_bitrate not in ["32k", "64k", "96k", "128k", "160k", "192k", "256k", "320k"]:
        print(f"Warning: Invalid bitrate {mp3_bitrate}, defaulting to 128k")
        mp3_bitrate = "128k"
    
    return mp3_bitrate

def test_single_audio_file():
    """Test compression on a single file for debugging"""
    test_file = filedialog.askopenfilename(
        title="Select an audio file to test",
        filetypes=[("Audio files", "*.mp3 *.ogg"), ("All files", "*.*")]
    )
    
    if test_file:
        bitrate = mp3_quality_var.get()
        target_bitrate = BITRATE_OPTIONS.get(bitrate, "128k")
        
        # Create debug window
        debug_window = tk.Toplevel(root)
        debug_window.title("Audio Compression Debug")
        debug_window.geometry("600x400")
        debug_window.configure(bg="#222")
        
        debug_text = scrolledtext.ScrolledText(debug_window, bg="#333", fg="#EEE", font=("Consolas", 10))
        debug_text.pack(fill="both", expand=True, padx=10, pady=10)
        
        def run_debug():
            debug_text.delete(1.0, tk.END)
            debug_text.insert(tk.END, f"Testing compression on: {os.path.basename(test_file)}\n")
            debug_text.insert(tk.END, f"Target bitrate: {target_bitrate}\n")
            debug_text.insert(tk.END, f"Mono mode: {mono_var.get()}\n\n")
            debug_window.update()
            
            # Get original file info
            original_size = get_file_size_cached(test_file)
            audio_info = get_audio_info(test_file)
            
            debug_text.insert(tk.END, f"Original size: {format_size(original_size)}\n")
            debug_text.insert(tk.END, f"Original bitrate: {audio_info.get('bitrate', 'Unknown')}kbps\n")
            debug_text.insert(tk.END, f"Duration: {audio_info.get('duration', 0):.1f}s\n")
            debug_text.insert(tk.END, f"Channels: {audio_info.get('channels', 'Unknown')}\n")
            debug_text.insert(tk.END, f"Genre detected: {audio_info.get('genre', 'Unknown')}\n\n")
            debug_window.update()
            
            # Test compression
            debug_text.insert(tk.END, "Running compression test...\n")
            debug_window.update()
            
            # Make a copy for testing
            test_copy = test_file + ".debug_copy"
            shutil.copy2(test_file, test_copy)
            
            try:
                result = compress_audio_ffmpeg_optimized(test_copy, target_bitrate, mono_var.get(), 
                                                       normalize_var.get(), genre_based_var.get())
                
                if result > 0:
                    new_size = get_file_size_cached(test_copy)
                    compression_ratio = new_size / original_size
                    debug_text.insert(tk.END, f"✓ Compression successful!\n")
                    debug_text.insert(tk.END, f"New size: {format_size(new_size)}\n")
                    debug_text.insert(tk.END, f"Space saved: {format_size(result)}\n")
                    debug_text.insert(tk.END, f"Compression ratio: {compression_ratio:.2%}\n")
                    
                    # Verify integrity
                    if verify_file_integrity(test_copy, "audio"):
                        debug_text.insert(tk.END, "✓ File integrity verified\n")
                    else:
                        debug_text.insert(tk.END, "⚠ File integrity check failed\n")
                else:
                    debug_text.insert(tk.END, "✗ Compression failed or no improvement\n")
                
                # Clean up
                if os.path.exists(test_copy):
                    os.unlink(test_copy)
            
            except Exception as e:
                debug_text.insert(tk.END, f"✗ Error during compression: {str(e)}\n")
                if os.path.exists(test_copy):
                    os.unlink(test_copy)
        
        ttk.Button(debug_window, text="Run Debug Test", command=run_debug).pack(pady=10)

def start_cleanup():
    global stop_requested
    stop_requested = False
    folder = folder_var.get()
    if not folder or not os.path.isdir(folder):
        messagebox.showerror("Error", "Please select a valid Songs folder.")
        return

    # Get all settings
    remove_hitsounds = hitsound_var.get()
    remove_audio = audio_var.get()
    remove_images = image_var.get()
    remove_storyboards = storyboard_var.get()
    find_duplicates = duplicate_var.get()
    process_osz = osz_var.get()
    mp3_quality_label = mp3_quality_var.get()
    mp3_bitrate = BITRATE_OPTIONS.get(mp3_quality_label, "128k")
    dry_run = dry_run_var.get()
    
    # Validate bitrate
    if mp3_bitrate not in ["32k", "64k", "96k", "128k", "160k", "192k", "256k", "320k"]:
        print(f"Warning: Invalid bitrate {mp3_bitrate}, defaulting to 128k")
        mp3_bitrate = "128k"
    
    # Get extra features
    extra_features = []
    if remove_videos_var.get():
        extra_features.append("Remove Videos")
    if remove_unused_var.get():
        extra_features.append("Remove Unused Images")
    if clean_folders_var.get():
        extra_features.append("Clean Empty Folders")
    
    # Get advanced options
    advanced_options = {
        'smart_detection': smart_detection_var.get(),
        'enable_whitelist': enable_whitelist_var.get(),
        'normalize_audio': normalize_var.get(),
        'genre_based_compression': genre_based_var.get(),
        'enable_verification': verification_var.get()
    }

    if not any([remove_hitsounds, remove_audio, remove_images, remove_storyboards, 
                find_duplicates, process_osz]) and not extra_features:
        messagebox.showwarning("Warning", "Select at least one option to clean/compress.")
        return

    progress_bar["value"] = 0
    status_label.config(text="Working...")
    cancel_button.config(state="normal")

    def update_progress(current, total, msg):
        percent = (current / total) * 100 if total else 100
        progress_bar["value"] = percent
        status_label.config(text=f"{msg} ({current}/{total})")
        root.update_idletasks()

    def cleanup_done(total_saved, stats, time_taken):
        files_per_sec = sum(stats.values()) / max(time_taken, 0.1)
        
        # Enhanced summary with new features
        base_summary = (f"{'Would save' if dry_run else 'Saved'} {format_size(total_saved)} in {time_taken:.1f}s "
                       f"({files_per_sec:.0f} files/sec)")
        
        details = []
        if stats.get('hitsounds', 0) > 0:
            details.append(f"Hitsounds: {stats['hitsounds']}")
        if stats.get('audio', 0) > 0:
            details.append(f"Audio: {stats['audio']}")
        if stats.get('images', 0) > 0:
            details.append(f"Images: {stats['images']}")
        if stats.get('storyboards', 0) > 0:
            details.append(f"Storyboards: {stats['storyboards']}")
        if stats.get('duplicates', 0) > 0:
            details.append(f"Duplicates: {stats['duplicates']}")
        if stats.get('osz', 0) > 0:
            details.append(f"OSZ: {stats['osz']}")
        if stats.get('videos', 0) > 0:
            details.append(f"Videos: {stats['videos']}")
        if stats.get('unused', 0) > 0:
            details.append(f"Unused: {stats['unused']}")
        if stats.get('folders', 0) > 0:
            details.append(f"Folders: {stats['folders']}")
        if stats.get('broken_symlinks', 0) > 0:
            details.append(f"Symlinks: {stats['broken_symlinks']}")
        
        summary = base_summary
        if details:
            summary += f" | {', '.join(details)}"
        
        # Add detection stats
        detection_info = []
        if stats.get('corrupted', 0) > 0:
            detection_info.append(f"Corrupted: {stats['corrupted']}")
        if stats.get('duplicate_beatmaps', 0) > 0:
            detection_info.append(f"Dup.Maps: {stats['duplicate_beatmaps']}")
        if stats.get('large_files', 0) > 0:
            detection_info.append(f"Large: {stats['large_files']}")
        if stats.get('protected', 0) > 0:
            detection_info.append(f"Protected: {stats['protected']}")
        
        if detection_info:
            summary += f" | Detected: {', '.join(detection_info)}"
        
        status_label.config(text=summary)
        cancel_button.config(state="disabled")
        
        # Show detailed popup if requested
        if advanced_options.get('show_detailed_results', True):
            result_msg = f"Cleanup Complete!\n\n"
            result_msg += f"Space {'would be' if dry_run else ''} saved: {format_size(total_saved)}\n"
            result_msg += f"Processing time: {time_taken:.1f} seconds\n"
            result_msg += f"Performance: {files_per_sec:.0f} files/second\n\n"
            
            if details:
                result_msg += "Files processed:\n" + "\n".join(f"• {detail}" for detail in details)
            
            if detection_info:
                result_msg += f"\n\nSmart detection results:\n" + "\n".join(f"• {info}" for info in detection_info)
            
            messagebox.showinfo("Cleanup Complete", result_msg)

    thread = threading.Thread(target=threaded_cleanup_optimized,
                              args=(folder, remove_hitsounds, remove_audio, remove_images, 
                                    remove_storyboards, find_duplicates, process_osz, mp3_bitrate, 
                                    update_progress, cleanup_done, dry_run, extra_features, advanced_options))
    thread.daemon = True
    thread.start()

def cancel_cleanup():
    global stop_requested
    stop_requested = True
    status_label.config(text="Canceling...")
    cancel_button.config(state="disabled")

# --- Enhanced GUI Setup ---
root = tk.Tk()
root.title("osu! Cleaner - Enhanced with Advanced Features")
root.geometry("800x900")
root.configure(bg="#222")

# Initialize components
init_analytics_db()
load_whitelist()

# Set thread priority for better performance
try:
    if os.name == 'nt' and HAS_PSUTIL:
        import psutil
        p = psutil.Process(os.getpid())
        p.nice(psutil.HIGH_PRIORITY_CLASS)
    elif os.name == 'nt':
        os.system(f"wmic process where processid={os.getpid()} CALL setpriority \"high priority\"")
except:
    pass

style = ttk.Style()
style.theme_use("clam")
style.configure("TLabel", background="#222", foreground="#EEE")
style.configure("TButton", background="#444", foreground="#EEE")
style.configure("TEntry", fieldbackground="#333", foreground="#EEE", insertcolor="#EEE")
style.configure("TCheckbutton", background="#222", foreground="#EEE")

# Variables
folder_var = tk.StringVar()
mp3_quality_var = tk.StringVar(value="128 kbps")
image_quality_var = tk.StringVar(value=IMAGE_QUALITY_OPTIONS[0])
background_var = tk.StringVar(value=BACKGROUND_OPTIONS[0])
speed_var = tk.StringVar(value="Adaptive")
dry_run_var = tk.BooleanVar(value=False)
stealth_var = tk.BooleanVar(value=False)

# Enhanced feature variables
smart_detection_var = tk.BooleanVar(value=True)
enable_whitelist_var = tk.BooleanVar(value=False)
normalize_var = tk.BooleanVar(value=False)
genre_based_var = tk.BooleanVar(value=False)
verification_var = tk.BooleanVar(value=True)

# Folder selection
frame = ttk.LabelFrame(root, text="osu! Songs Folder")
frame.pack(padx=10, pady=10, fill="x")

entry = ttk.Entry(frame, textvariable=folder_var, width=60)
entry.pack(side="left", padx=5, pady=5)

def browse_folder():
    path = filedialog.askdirectory(title="Select osu! Songs Folder")
    if path:
        folder_var.set(path)

browse_btn = ttk.Button(frame, text="Browse", command=browse_folder)
browse_btn.pack(side="left", padx=5)

# Basic cleanup options
toggles_frame = ttk.LabelFrame(root, text="Basic Cleanup Options")
toggles_frame.pack(padx=10, pady=10, fill="x")

hitsound_var = tk.BooleanVar(value=True)
audio_var = tk.BooleanVar(value=True)
image_var = tk.BooleanVar(value=True)
storyboard_var = tk.BooleanVar(value=False)
duplicate_var = tk.BooleanVar(value=False)
osz_var = tk.BooleanVar(value=False)

ttk.Checkbutton(toggles_frame, text="Remove Hitsounds (.wav)", variable=hitsound_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(toggles_frame, text="Compress Audio (.mp3/.ogg)", variable=audio_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(toggles_frame, text="Convert & Resize Images", variable=image_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(toggles_frame, text="Remove Storyboards (.osb)", variable=storyboard_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(toggles_frame, text="Remove Duplicate Audio Files", variable=duplicate_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(toggles_frame, text="Process .osz Packs", variable=osz_var).pack(anchor="w", padx=10, pady=2)

# Enhanced extra features
extra_frame = ttk.LabelFrame(root, text="🚀 Power Features")
extra_frame.pack(padx=10, pady=5, fill="x")

remove_videos_var = tk.BooleanVar(value=False)
remove_unused_var = tk.BooleanVar(value=False)
clean_folders_var = tk.BooleanVar(value=False)

ttk.Checkbutton(extra_frame, text="🎬 Remove Videos (.mp4/.avi/.mov)", variable=remove_videos_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(extra_frame, text="🖼️ Remove Unused Images", variable=remove_unused_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(extra_frame, text="📁 Clean Empty Folders", variable=clean_folders_var).pack(anchor="w", padx=10, pady=2)

# Smart detection features
smart_frame = ttk.LabelFrame(root, text="🧠 Smart Detection & Protection")
smart_frame.pack(padx=10, pady=5, fill="x")

ttk.Checkbutton(smart_frame, text="🔍 Enable Smart Detection (corrupted files, large files, etc.)", variable=smart_detection_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(smart_frame, text="🛡️ Enable Whitelist Protection", variable=enable_whitelist_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(smart_frame, text="✅ Enable Post-Process Verification", variable=verification_var).pack(anchor="w", padx=10, pady=2)

whitelist_buttons = tk.Frame(smart_frame, bg="#222")
whitelist_buttons.pack(anchor="w", padx=20, pady=2)

ttk.Button(whitelist_buttons, text="Configure Whitelist", command=open_whitelist_editor).pack(side="left", padx=5)
ttk.Button(whitelist_buttons, text="View Analytics", command=open_analytics_window).pack(side="left", padx=5)

# Audio processing options
audio_frame = ttk.LabelFrame(root, text="🎵 Advanced Audio Processing")
audio_frame.pack(padx=10, pady=5, fill="x")

quality_row = tk.Frame(audio_frame, bg="#222")
quality_row.pack(fill="x", padx=10, pady=5)

ttk.Label(quality_row, text="Bitrate:").pack(side="left")
quality_dropdown = ttk.Combobox(quality_row, textvariable=mp3_quality_var, state="readonly", 
                               values=list(BITRATE_OPTIONS.keys()), width=15)
quality_dropdown.pack(side="left", padx=5)

ttk.Checkbutton(audio_frame, text="🎚️ Normalize Audio Volume", variable=normalize_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(audio_frame, text="🎭 Genre-Based Compression", variable=genre_based_var).pack(anchor="w", padx=10, pady=2)

# Image processing options
image_frame = ttk.LabelFrame(root, text="🖼️ Image Processing")
image_frame.pack(padx=10, pady=5, fill="x")

resize_row = tk.Frame(image_frame, bg="#222")
resize_row.pack(fill="x", padx=10, pady=5)

ttk.Label(resize_row, text="Max Resolution:").pack(side="left")
resize_dropdown = ttk.OptionMenu(resize_row, image_quality_var, *IMAGE_QUALITY_OPTIONS)
resize_dropdown.pack(side="left", padx=5)

ttk.Label(resize_row, text="Background Mode:").pack(side="left", padx=(20,5))
bg_dropdown = ttk.OptionMenu(resize_row, background_var, *BACKGROUND_OPTIONS)
bg_dropdown.pack(side="left", padx=5)

# Performance options
perf_frame = ttk.LabelFrame(root, text="⚡ Performance & Quality")
perf_frame.pack(padx=10, pady=5, fill="x")

speed_row = tk.Frame(perf_frame, bg="#222")
speed_row.pack(fill="x", padx=10, pady=5)

ttk.Label(speed_row, text="Speed:").pack(side="left")
speed_dropdown = ttk.OptionMenu(speed_row, speed_var, *SPEED_OPTIONS)
speed_dropdown.pack(side="left", padx=5)

extreme_var = tk.BooleanVar(value=False)
mono_var = tk.BooleanVar(value=False)

ttk.Checkbutton(perf_frame, text="🔥 Extreme Image Compression (Quality 50%)", variable=extreme_var).pack(anchor="w", padx=10, pady=2)
ttk.Checkbutton(perf_frame, text="📻 Convert Audio to Mono (50% size reduction)", variable=mono_var).pack(anchor="w", padx=10, pady=2)

# Mode options
mode_frame = tk.Frame(root, bg="#222")
mode_frame.pack(pady=5)

ttk.Checkbutton(mode_frame, text="👁️ Dry Run Mode (Preview Only)", variable=dry_run_var).pack(side="left", padx=10)
ttk.Checkbutton(mode_frame, text="🥷 Stealth Mode (Hide window)", variable=stealth_var).pack(side="left", padx=10)

# Control buttons
button_frame = tk.Frame(root, bg="#222")
button_frame.pack(pady=10)

ttk.Button(button_frame, text="🚀 Start Enhanced Cleanup", command=start_cleanup).pack(side="left", padx=5)
ttk.Button(button_frame, text="🔧 Debug Single Audio", command=test_single_audio_file).pack(side="left", padx=5)

# Progress and status
progress_bar = ttk.Progressbar(root, length=600, mode="determinate")
progress_bar.pack(pady=5)

status_label = ttk.Label(root, text="Ready! Enhanced osu! Cleaner with Smart Detection, Whitelist Protection, and Advanced Analytics")
status_label.pack(pady=5)

cancel_button = ttk.Button(root, text="Cancel", command=cancel_cleanup, state="disabled")
cancel_button.pack(pady=5)

# Footer with version info
footer_frame = tk.Frame(root, bg="#222")
footer_frame.pack(side="bottom", fill="x", pady=5)

version_label = ttk.Label(footer_frame, text="Enhanced osu! Cleaner v2.0 - Now with Smart Detection, Analytics & Protection!", 
                         font=("Arial", 8), foreground="#888")
version_label.pack()

# Cleanup on exit
def on_closing():
    global analytics_db
    if analytics_db:
        analytics_db.close()
    save_whitelist()
    root.destroy()

root.protocol("WM_DELETE_WINDOW", on_closing)

if __name__ == "__main__":
    root.mainloop()