import tkinter as tk
from tkinter import ttk, filedialog, messagebox, font, simpledialog
import ttkbootstrap as tb
from ttkbootstrap.constants import *
import requests
import threading
import os
import math
import time
import queue
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import uuid
import platform
import subprocess
import re
import shutil
from urllib.parse import unquote

CONFIG_FILE = "config.json"
HISTORY_FILE = "data.json"
DEFAULT_TEMP_DIR_NAME = ".download_temp_cache"
DEFAULT_SETTINGS = {
    "theme": "solar",
    "num_threads": 8,
    "auto_threads": False,
    "download_dir": str(Path.home() / "Downloads"),
    "speed_limit_enabled": False,
    "speed_limit_mbps": 10.0,
    "font_family": "Segoe UI" if platform.system() == "Windows" else "Arial",
    "font_size": 10,
    "window_width": 950,
    "window_height": 700,
    "detailed_pane_height": 150,
}
UPDATE_INTERVAL_MS = 500
PROGRESS_INTERVAL_BYTES = 1024 * 64
SPEED_LIMIT_INTERVAL = 0.2
BYTES_PER_MB = 1024 * 1024
NO_LIMIT = -1.0

class SettingsManager:
    def __init__(self, filename=CONFIG_FILE, defaults=None):
        if defaults is None:
            defaults = DEFAULT_SETTINGS
        self.filename = filename
        self.defaults = defaults
        self.settings = self.load_settings()

    def load_settings(self):
        try:
            with open(self.filename, 'r', encoding='utf-8') as f:
                loaded_settings = json.load(f)
                settings = self.defaults.copy()
                settings.update(loaded_settings)
                settings["num_threads"] = int(settings.get("num_threads", self.defaults["num_threads"]))
                settings["font_size"] = int(settings.get("font_size", self.defaults["font_size"]))
                settings["window_width"] = int(settings.get("window_width", self.defaults["window_width"]))
                settings["window_height"] = int(settings.get("window_height", self.defaults["window_height"]))
                settings["detailed_pane_height"] = int(settings.get("detailed_pane_height", self.defaults["detailed_pane_height"]))
                if settings["detailed_pane_height"] < 50: settings["detailed_pane_height"] = 50
                settings["speed_limit_enabled"] = bool(settings.get("speed_limit_enabled", self.defaults["speed_limit_enabled"]))
                try:
                    settings["speed_limit_mbps"] = float(settings.get("speed_limit_mbps", self.defaults["speed_limit_mbps"]))
                    if settings["speed_limit_mbps"] <= 0:
                        print(f"Warning: Invalid speed limit value ({settings['speed_limit_mbps']}). Resetting to default.")
                        settings["speed_limit_mbps"] = self.defaults["speed_limit_mbps"]
                except (ValueError, TypeError):
                    print(f"Warning: Invalid type for speed_limit_mbps. Resetting to default.")
                    settings["speed_limit_mbps"] = self.defaults["speed_limit_mbps"]
                Path(settings["download_dir"]).mkdir(parents=True, exist_ok=True)
                return settings
        except (FileNotFoundError, json.JSONDecodeError, ValueError, TypeError, OSError) as e:
            print(f"Config file error/missing ({e}). Using defaults & creating new file.")
            try:
                Path(self.defaults["download_dir"]).mkdir(parents=True, exist_ok=True)
            except OSError as dir_err:
                print(f"Could not create default download dir: {dir_err}. Setting to home.")
                self.defaults["download_dir"] = str(Path.home())
            self.save_settings(self.defaults)
            return self.defaults.copy()

    def save_settings(self, settings_dict=None):
        if settings_dict is None:
            settings_dict = self.settings
        try:
            Path(settings_dict["download_dir"]).mkdir(parents=True, exist_ok=True)
            try:
                settings_dict["detailed_pane_height"] = int(settings_dict.get("detailed_pane_height", self.defaults["detailed_pane_height"]))
                if settings_dict["detailed_pane_height"] < 50: settings_dict["detailed_pane_height"] = 50
            except (ValueError, TypeError):
                settings_dict["detailed_pane_height"] = self.defaults["detailed_pane_height"]
            try:
                settings_dict["speed_limit_mbps"] = float(settings_dict.get("speed_limit_mbps", self.defaults["speed_limit_mbps"]))
            except (ValueError, TypeError):
                settings_dict["speed_limit_mbps"] = self.defaults["speed_limit_mbps"]
            with open(self.filename, 'w', encoding='utf-8') as f:
                json.dump(settings_dict, f, indent=4)
            self.settings = settings_dict
        except IOError as e:
            print(f"Error saving settings: {e}")
            messagebox.showerror("Error Saving Settings", f"Could not save settings to {self.filename}.\n{e}")
        except OSError as e:
             print(f"Error creating download directory: {e}")
             messagebox.showerror("Error Saving Settings", f"Could not create download directory:\n{settings_dict['download_dir']}\n{e}")

    def get(self, key):
        return self.settings.get(key, self.defaults.get(key))

    def set(self, key, value):
        self.settings[key] = value

class Downloader:
    def __init__(self, progress_queue):
        self.progress_queue = progress_queue
        self.executor = ThreadPoolExecutor(max_workers=max(4, os.cpu_count() or 1 * 8))
        self.active_downloads = {}

        self.speed_limit_lock = threading.Lock()
        self.limit_enabled = False
        self.limit_bytes_per_sec = 0.0
        self.global_downloaded_this_interval = 0
        self.global_interval_start_time = time.monotonic()

        self.task_limits_lock = threading.Lock()
        self.task_limits = {}

    def set_speed_limit(self, enabled: bool, limit_mbps: float):
        with self.speed_limit_lock:
            self.limit_enabled = enabled
            if self.limit_enabled:
                self.limit_bytes_per_sec = max(0.1 * BYTES_PER_MB, limit_mbps * BYTES_PER_MB)
                print(f"Global Speed limit set: {enabled}, {limit_mbps} MB/s ({self.limit_bytes_per_sec:.2f} B/s)")
            else:
                self.limit_bytes_per_sec = 0.0
                print("Global Speed limit disabled.")
            self.global_downloaded_this_interval = 0
            self.global_interval_start_time = time.monotonic()

    def set_task_speed_limit(self, task_id: str, limit_mbps: float):
        """Sets or removes a speed limit for a specific task."""
        with self.task_limits_lock:
            if limit_mbps is None or limit_mbps <= 0:
                if task_id in self.task_limits:
                    del self.task_limits[task_id]
                print(f"Removed speed limit for task {task_id}")
                return True
            else:
                limit_bytes_per_sec = max(0.1 * BYTES_PER_MB, limit_mbps * BYTES_PER_MB)
                if self.task_limits.get(task_id) != limit_bytes_per_sec:
                    self.task_limits[task_id] = limit_bytes_per_sec
                    print(f"Set speed limit for task {task_id}: {limit_mbps} MB/s ({limit_bytes_per_sec:.2f} B/s)")
                    return True
                return False

    def get_task_speed_limit_mbps(self, task_id: str) -> float:
        """Gets the speed limit for a task in MB/s, returns NO_LIMIT if none."""
        with self.task_limits_lock:
            limit_bps = self.task_limits.get(task_id, NO_LIMIT * BYTES_PER_MB)
            if limit_bps <= 0:
                 return NO_LIMIT
            else:
                 return limit_bps / BYTES_PER_MB

    def _remove_task_limit(self, task_id: str):
         """Internal helper to remove task limit entry."""
         with self.task_limits_lock:
             if task_id in self.task_limits:
                 del self.task_limits[task_id]

    def _apply_speed_limit_delay(self, downloaded_bytes):
        """Checks GLOBAL speed and sleeps if necessary."""
        if not self.limit_enabled or self.limit_bytes_per_sec <= 0:
            return

        with self.speed_limit_lock:
            if not self.limit_enabled or self.limit_bytes_per_sec <= 0: return
            current_time = time.monotonic()
            self.global_downloaded_this_interval += downloaded_bytes
            elapsed_this_interval = current_time - self.global_interval_start_time
            if elapsed_this_interval >= SPEED_LIMIT_INTERVAL:
                current_global_speed_bps = self.global_downloaded_this_interval / elapsed_this_interval
                limit_bps_for_calc = self.limit_bytes_per_sec
                if current_global_speed_bps > limit_bps_for_calc:
                    excess_bytes = self.global_downloaded_this_interval - (limit_bps_for_calc * elapsed_this_interval)
                    delay_needed = excess_bytes / limit_bps_for_calc if limit_bps_for_calc > 0 else 0
                    if delay_needed > 0.001:
                        try: time.sleep(delay_needed)
                        except ValueError: pass
                self.global_interval_start_time = time.monotonic()
                self.global_downloaded_this_interval = 0

    def _download_part(self, task_id, url, start_byte, end_byte, part_num, temp_folder, cancel_event, pause_event):
        """Downloads a part, respects GLOBAL and TASK speed limits."""
        part_filename = os.path.join(temp_folder, f"part_{part_num}")
        downloaded_bytes_part = 0
        last_reported_bytes = 0
        start_time_part = time.time()
        mode = 'wb'
        expected_size = end_byte - start_byte + 1
        initial_offset = 0

        part_limit_bytes_per_sec = NO_LIMIT * BYTES_PER_MB
        part_downloaded_this_interval = 0
        part_interval_start_time = time.monotonic()
        last_limit_check_time = time.monotonic()

        try:
            if os.path.exists(part_filename):
                 current_size = os.path.getsize(part_filename)
                 if current_size == expected_size:
                     self.progress_queue.put({
                         "type": "part_progress", "task_id": task_id, "part_num": part_num,
                         "current": expected_size, "total": expected_size, "speed_bps": 0,
                         "status": "Hoàn thành (đã có)"
                     })
                     return {'success': True, 'filename': part_filename, 'size': expected_size, 'part_num': part_num, 'resumed': False}
                 elif 0 < current_size < expected_size:
                     headers = {'Range': f'bytes={start_byte + current_size}-{end_byte}'}
                     downloaded_bytes_part = current_size
                     last_reported_bytes = current_size
                     initial_offset = current_size
                     mode = 'ab'
                     print(f"[Task {task_id} Part {part_num}] Resuming from byte {initial_offset}")
                 else:
                     headers = {'Range': f'bytes={start_byte}-{end_byte}'}
                     mode = 'wb'
                     print(f"[Task {task_id} Part {part_num}] Overwriting existing part file (size mismatch).")
            else:
                 headers = {'Range': f'bytes={start_byte}-{end_byte}'}
                 mode = 'wb'

            req_headers = headers.copy()
            req_headers['User-Agent'] = 'PythonDownloadManager/1.0'
            response = requests.get(url, headers=req_headers, stream=True, timeout=60)
            response.raise_for_status()

            with open(part_filename, mode) as f:
                for chunk in response.iter_content(chunk_size=8192):
                    if cancel_event.is_set(): return {'success': False, 'error': 'Bị hủy', 'part_num': part_num}
                    if pause_event.is_set():
                         self.progress_queue.put({
                              "type": "part_progress", "task_id": task_id, "part_num": part_num,
                              "current": downloaded_bytes_part, "total": expected_size, "speed_bps": 0,
                              "status": "Tạm dừng"
                          })
                         while pause_event.is_set():
                             if cancel_event.is_set(): return {'success': False, 'error': 'Bị hủy', 'part_num': part_num}
                             time.sleep(0.2)
                         start_time_part = time.time()
                         initial_offset = downloaded_bytes_part
                         last_reported_bytes = downloaded_bytes_part
                         part_interval_start_time = time.monotonic()
                         part_downloaded_this_interval = 0
                         last_limit_check_time = time.monotonic()

                    if chunk:
                        chunk_len = len(chunk)
                        f.write(chunk)
                        downloaded_bytes_part += chunk_len
                        current_mono_time = time.monotonic()

                        if current_mono_time - last_limit_check_time > 0.1:
                            with self.task_limits_lock:
                                part_limit_bytes_per_sec = self.task_limits.get(task_id, NO_LIMIT * BYTES_PER_MB)
                            last_limit_check_time = current_mono_time

                        if part_limit_bytes_per_sec > 0:
                            part_downloaded_this_interval += chunk_len
                            part_elapsed_this_interval = current_mono_time - part_interval_start_time
                            if part_elapsed_this_interval >= SPEED_LIMIT_INTERVAL:
                                current_part_speed_bps = part_downloaded_this_interval / part_elapsed_this_interval
                                if current_part_speed_bps > part_limit_bytes_per_sec:
                                    part_excess_bytes = part_downloaded_this_interval - (part_limit_bytes_per_sec * part_elapsed_this_interval)
                                    part_delay_needed = part_excess_bytes / part_limit_bytes_per_sec if part_limit_bytes_per_sec > 0 else 0
                                    if part_delay_needed > 0.001:
                                        try: time.sleep(part_delay_needed)
                                        except ValueError: pass
                                part_interval_start_time = time.monotonic()
                                part_downloaded_this_interval = 0

                        self._apply_speed_limit_delay(chunk_len)

                        if downloaded_bytes_part - last_reported_bytes >= PROGRESS_INTERVAL_BYTES or downloaded_bytes_part == expected_size:
                            elapsed_time = time.time() - start_time_part
                            current_speed_bps = ((downloaded_bytes_part - initial_offset) / elapsed_time) * 8 if elapsed_time > 0.01 else 0
                            self.progress_queue.put({
                                "type": "part_progress", "task_id": task_id, "part_num": part_num,
                                "current": downloaded_bytes_part, "total": expected_size,
                                "speed_bps": current_speed_bps, "status": "Đang tải"
                            })
                            last_reported_bytes = downloaded_bytes_part

            final_size = os.path.getsize(part_filename)
            if final_size == expected_size:
                  elapsed_time = time.time() - start_time_part
                  final_speed_bps = ((expected_size - initial_offset) / elapsed_time) * 8 if elapsed_time > 0.01 else 0
                  self.progress_queue.put({
                      "type": "part_progress", "task_id": task_id, "part_num": part_num,
                      "current": expected_size, "total": expected_size,
                      "speed_bps": final_speed_bps, "status": "Hoàn thành"
                  })
                  return {'success': True, 'filename': part_filename, 'size': expected_size, 'part_num': part_num, 'resumed': initial_offset > 0}
            else:
                  if cancel_event.is_set(): return {'success': False, 'error': 'Bị hủy', 'part_num': part_num}
                  error_detail = f"Kích thước không khớp khi kết thúc (mong đợi {expected_size}, nhận được {final_size})"
                  print(f"[Task {task_id} Part {part_num}] Error: {error_detail}")
                  self.progress_queue.put({"type": "part_error", "task_id": task_id, "part_num": part_num, "error": error_detail})
                  return {'success': False, 'error': 'Kích thước không khớp', 'part_num': part_num}

        except requests.exceptions.RequestException as e:
              if cancel_event.is_set(): return {'success': False, 'error': 'Bị hủy (khi đang kết nối)', 'part_num': part_num}
              error_detail = f"Lỗi mạng: {e}"
              self.progress_queue.put({"type": "part_error", "task_id": task_id, "part_num": part_num, "error": error_detail})
              return {'success': False, 'error': str(e), 'part_num': part_num}
        except IOError as e:
              if cancel_event.is_set(): return {'success': False, 'error': 'Bị hủy (khi đang ghi file)', 'part_num': part_num}
              error_detail = f"Lỗi I/O: {e}"
              self.progress_queue.put({"type": "part_error", "task_id": task_id, "part_num": part_num, "error": error_detail})
              return {'success': False, 'error': str(e), 'part_num': part_num}
        except Exception as e:
              if cancel_event.is_set(): return {'success': False, 'error': 'Bị hủy (lỗi không xác định)', 'part_num': part_num}
              import traceback
              error_detail = f"Lỗi không xác định: {e}"
              print(f"[Task {task_id}] Unknown error in part {part_num}: {e}\n{traceback.format_exc()}")
              self.progress_queue.put({"type": "part_error", "task_id": task_id, "part_num": part_num, "error": error_detail})
              return {'success': False, 'error': error_detail, 'part_num': part_num}

    def format_speed(self, speed_bytes_sec):
        if speed_bytes_sec is None or not isinstance(speed_bytes_sec, (int, float)) or speed_bytes_sec < 0: return "-"
        if speed_bytes_sec < 1: return "0 B/s"
        size_name = ("B/s", "KB/s", "MB/s", "GB/s", "TB/s")
        try: i = min(len(size_name) - 1, int(math.floor(math.log(speed_bytes_sec, 1024))))
        except ValueError: i = 0
        p = math.pow(1024, i)
        s = speed_bytes_sec / p
        precision = 1
        return f"{s:.{precision}f} {size_name[i]}"

    def _merge_files(self, task_id, part_results, final_filename, num_parts_expected, total_size):
        print(f"[Task {task_id}] Merging into: {final_filename}")
        self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Đang ghép file..."})
        temp_folder = None
        success = False
        try:
            valid_results = [res for res in part_results if res and res.get('filename')]
            if not valid_results: raise IOError("Không tìm thấy kết quả hợp lệ của các phần.")
            temp_folder = os.path.dirname(valid_results[0]['filename'])

            successful_parts = sorted([res for res in part_results if res and res.get('success')], key=lambda x: x['part_num'])

            if len(successful_parts) != num_parts_expected:
                raise IOError(f"Số lượng phần thành công không khớp ({len(successful_parts)}/{num_parts_expected}).")

            total_written = 0
            with open(final_filename, 'wb') as final_file:
                for i, part_info in enumerate(successful_parts):
                    if part_info['part_num'] != i:
                        raise IOError(f"Thứ tự phần không khớp: mong đợi {i}, nhận được {part_info['part_num']}.")
                    part_filename = part_info['filename']
                    if not os.path.exists(part_filename):
                        raise FileNotFoundError(f"File phần không tìm thấy: {part_filename}")
                    with open(part_filename, 'rb') as part_file:
                        shutil.copyfileobj(part_file, final_file, length=1024*1024)
                    part_size = os.path.getsize(part_filename)
                    total_written += part_size

            final_merged_size = os.path.getsize(final_filename)
            if final_merged_size != total_size:
                print(f"[Task {task_id}] Warning: Kích thước sau ghép ({final_merged_size}) != kích thước mong đợi ({total_size}).")
                self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Hoàn thành (kích thước khác!)", "progress": 100})
                success = True
            else:
                print(f"[Task {task_id}] Ghép file thành công. Tổng kích thước: {final_merged_size} bytes.")
                self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Hoàn thành", "progress": 100})
                success = True
        except (IOError, FileNotFoundError, Exception) as e:
            import traceback
            print(f"[Task {task_id}] Lỗi khi ghép file: {e}\n{traceback.format_exc()}")
            self.progress_queue.put({"type": "error", "task_id": task_id, "error": f"Lỗi ghép file: {e}"})
            success = False
        finally:
            if temp_folder and os.path.isdir(temp_folder):
                 self._cleanup_temp_dir(task_id, temp_folder)
            elif temp_folder:
                 print(f"[Task {task_id}] Thư mục tạm không tìm thấy để dọn dẹp: {temp_folder}")
        return success

    def _run_download_task(self, task_id, url, num_threads, output_filename, temp_base_dir, total_size_known):
        start_time_task = time.time()
        task_control = self.active_downloads.get(task_id)
        if not task_control:
            print(f"[Task {task_id}] Task control block not found at start. Aborting.")
            self._remove_task_limit(task_id)
            return

        self.progress_queue.put({"type": "start", "task_id": task_id,
                                 "filename": os.path.basename(output_filename),
                                 "url": url, "total_size": total_size_known,
                                 "num_parts": num_threads})
        temp_task_dir = os.path.join(temp_base_dir, task_id)
        try:
            os.makedirs(temp_task_dir, exist_ok=True)
        except OSError as e:
            self.progress_queue.put({"type": "error", "task_id": task_id, "error": f"Không thể tạo thư mục tạm: {e}"})
            if task_id in self.active_downloads: del self.active_downloads[task_id]
            self._remove_task_limit(task_id)
            return

        task_control = self.active_downloads.get(task_id)
        if not task_control:
            print(f"[Task {task_id}] Task control block disappeared after temp dir creation. Aborting.")
            self._remove_task_limit(task_id)
            self._cleanup_temp_dir(task_id, temp_task_dir)
            return
        cancel_event = task_control['cancel_event']
        pause_event = task_control['pause_event']

        total_size = total_size_known
        if num_threads <= 0: num_threads = 1
        chunk_size = math.ceil(total_size / num_threads)
        part_futures = []
        actual_num_parts = 0
        if chunk_size <= 0 and total_size > 0: chunk_size = total_size; num_threads = 1
        if total_size <= 0:
             self.progress_queue.put({"type": "error", "task_id": task_id, "error": "Kích thước file là 0 bytes."})
             if task_id in self.active_downloads: del self.active_downloads[task_id]
             self._remove_task_limit(task_id)
             self._cleanup_temp_dir(task_id, temp_task_dir)
             return

        for i in range(num_threads):
            start_byte = i * chunk_size
            end_byte = min(start_byte + chunk_size - 1, total_size - 1)
            if start_byte >= total_size: continue
            actual_num_parts += 1
            future = self.executor.submit(self._download_part, task_id, url, start_byte, end_byte, i, temp_task_dir, cancel_event, pause_event)
            part_futures.append(future)

        if actual_num_parts != num_threads and actual_num_parts > 0:
             self.progress_queue.put({"type": "info_update", "task_id": task_id, "num_parts": actual_num_parts})
             print(f"[Task {task_id}] Adjusted number of parts to {actual_num_parts}")
        elif actual_num_parts == 0 and total_size > 0:
             print(f"[Task {task_id}] Warning: Calculated 0 parts for a file of size {total_size}. Check logic.")
             self.progress_queue.put({"type": "error", "task_id": task_id, "error": "Lỗi tính toán phần tải."})
             if task_id in self.active_downloads: del self.active_downloads[task_id]
             self._remove_task_limit(task_id)
             self._cleanup_temp_dir(task_id, temp_task_dir)
             return

        part_results = []
        all_parts_reported_success = True
        parts_completed_count = 0
        for future in part_futures:
              try:
                  result = future.result()
                  part_results.append(result)
                  if result and result.get('success'):
                      parts_completed_count += 1
                  elif result and not cancel_event.is_set() and result.get('error') != 'Bị hủy':
                      all_parts_reported_success = False
                      print(f"[Task {task_id} Part {result.get('part_num', '?')}] Failed with error: {result.get('error', 'Unknown')}")
                  elif not result and not cancel_event.is_set():
                      all_parts_reported_success = False
                      print(f"[Task {task_id}] Warning: Received None result for a part future.")
              except Exception as e:
                  print(f"[Task {task_id}] Critical error getting future result: {e}")
                  part_results.append({'success': False, 'error': f'Lỗi hệ thống: {e}', 'part_num': -1})
                  all_parts_reported_success = False

        final_status_known = False
        if cancel_event.is_set():
            print(f"[Task {task_id}] Download cancelled by user request.")
            self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Đã hủy"})
            final_status_known = True
            self._cleanup_temp_dir(task_id, temp_task_dir)

        elif all_parts_reported_success and parts_completed_count == actual_num_parts and actual_num_parts > 0:
            if self._merge_files(task_id, part_results, output_filename, actual_num_parts, total_size):
                print(f"[Task {task_id}] Download and merge successful.")
            else:
                print(f"[Task {task_id}] Merge failed after successful part downloads.")
            final_status_known = True

        if not final_status_known:
            if actual_num_parts == 0 and total_size > 0:
                 print(f"[Task {task_id}] Download failed: No parts were processed.")
                 self.progress_queue.put({"type": "error", "task_id": task_id, "error": "Không có phần nào được xử lý."})
            else:
                print(f"[Task {task_id}] Download failed (parts completed: {parts_completed_count}/{actual_num_parts}). Not merging.")
                self.progress_queue.put({"type": "error", "task_id": task_id, "error": "Một hoặc nhiều phần tải bị lỗi."})
            self._cleanup_temp_dir(task_id, temp_task_dir)

        if task_id in self.active_downloads:
            del self.active_downloads[task_id]
        self._remove_task_limit(task_id)

    def _cleanup_temp_dir(self, task_id, temp_folder):
         if temp_folder and os.path.isdir(temp_folder):
              parent_dir = os.path.dirname(temp_folder)
              print(f"[Task {task_id}] Dọn dẹp thư mục tạm: {temp_folder}")
              try:
                 shutil.rmtree(temp_folder)
                 print(f"[Task {task_id}] Đã xóa thư mục tạm.")
                 if os.path.isdir(parent_dir) and os.path.basename(parent_dir) == DEFAULT_TEMP_DIR_NAME:
                     try:
                         if not os.listdir(parent_dir):
                             os.rmdir(parent_dir)
                             print(f"[Task {task_id}] Đã xóa thư mục cache cha rỗng: {parent_dir}")
                     except OSError as e:
                         print(f"[Task {task_id}] Không thể xóa thư mục cache cha {parent_dir} (có thể không còn rỗng hoặc lỗi khác): {e}")
              except OSError as e:
                   print(f"[Task {task_id}] Lỗi khi xóa thư mục tạm {temp_folder}: {e}")
              except Exception as e:
                   print(f"[Task {task_id}] Lỗi không mong muốn khi dọn dẹp {parent_dir}: {e}")

    def start_new_download(self, url, num_threads, output_filename, temp_base_dir, file_info):
        task_id = str(uuid.uuid4())
        total_size = file_info.get('size', 0)
        if total_size <= 0:
             self.progress_queue.put({"type": "error", "task_id": task_id, "error": "Kích thước file không hợp lệ (<=0)."})
             print(f"Error starting download: File size is {total_size} for {url}")
             return None
        num_threads = max(1, int(num_threads))
        if total_size < 1 * 1024 * 1024: num_threads = 1
        elif total_size < 10 * 1024 * 1024: num_threads = min(num_threads, 4)

        self.active_downloads[task_id] = {
            'cancel_event': threading.Event(),
            'pause_event': threading.Event(),
            'url': url, 'output_filename': output_filename, 'total_size': total_size,
            'filename': file_info.get('name', 'Unknown'), 'status': 'Bắt đầu...',
            'progress': 0, 'speed_bps': 0, 'elapsed_time': 0,
            'num_parts_expected': num_threads, 'parts': {}
        }
        thread_main_task = threading.Thread(
            target=self._run_download_task,
            args=(task_id, url, num_threads, output_filename, temp_base_dir, total_size),
            daemon=True
        )
        thread_main_task.start()
        self.active_downloads[task_id]['main_thread'] = thread_main_task
        return task_id

    def cancel_download(self, task_id):
         if task_id in self.active_downloads:
             control = self.active_downloads[task_id]
             if not control['cancel_event'].is_set():
                 print(f"Requesting cancel for task: {task_id}")
                 control['pause_event'].clear()
                 control['cancel_event'].set()
                 self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Đang hủy..."})
                 return True
             else: return False
         else: return False

    def pause_download(self, task_id):
        if task_id in self.active_downloads:
             control = self.active_downloads[task_id]
             if not control['cancel_event'].is_set():
                 if not control['pause_event'].is_set():
                     print(f"Requesting pause for task: {task_id}")
                     control['pause_event'].set()
                     self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Đã tạm dừng"})
                 return True
             else: return False
        else: return False

    def resume_download(self, task_id):
        if task_id in self.active_downloads:
             control = self.active_downloads[task_id]
             if control['pause_event'].is_set():
                 print(f"Requesting resume for task: {task_id}")
                 control['pause_event'].clear()
                 self.progress_queue.put({"type": "status_update", "task_id": task_id, "status": "Đang tải..."})
                 return True
             else: return False
        else: return False

    def shutdown(self):
        print("Shutting down: Cancelling active downloads...")
        active_ids = list(self.active_downloads.keys())
        threads_to_join = []
        if active_ids:
            for task_id in active_ids:
                if self.cancel_download(task_id):
                     if task_id in self.active_downloads and 'main_thread' in self.active_downloads[task_id]:
                         threads_to_join.append(self.active_downloads[task_id]['main_thread'])
            if threads_to_join:
                print(f"Waiting up to 2s for {len(threads_to_join)} active task(s) to acknowledge cancellation...")
                join_timeout = 2.0; start_wait = time.time()
                for thread in threads_to_join:
                    time_left = join_timeout - (time.time() - start_wait)
                    if time_left <= 0: print("Timeout waiting for threads to join."); break
                    thread.join(timeout=max(0.1, time_left))
            remaining_tasks = list(self.active_downloads.keys())
            if remaining_tasks:
                print(f"Warning: Tasks {remaining_tasks} may not have exited cleanly after cancel request.")
                with self.task_limits_lock:
                    for task_id in remaining_tasks:
                        if task_id in self.task_limits:
                            del self.task_limits[task_id]
                            print(f"Forcefully cleaned up speed limit for task {task_id} during shutdown.")
        print("Shutting down ThreadPoolExecutor...")
        self.executor.shutdown(wait=True, cancel_futures=True)
        print("Downloader shutdown complete.")


class DownloadManagerApp(tb.Window):
    def __init__(self, settings_manager):
        self.settings_manager = settings_manager
        theme = self.settings_manager.get("theme")
        try: super().__init__(themename=theme)
        except tk.TclError:
            print(f"Theme '{theme}' not found. Falling back to default.")
            super().__init__(themename=DEFAULT_SETTINGS["theme"])
            self.settings_manager.set("theme", DEFAULT_SETTINGS["theme"])
            self.settings_manager.save_settings()

        self.title("Python Download Manager")
        win_w = max(800, self.settings_manager.get('window_width'))
        win_h = max(600, self.settings_manager.get('window_height'))
        screen_w = self.winfo_screenwidth(); screen_h = self.winfo_screenheight()
        x_pos = max(0, (screen_w // 2) - (win_w // 2))
        y_pos = max(0, (screen_h // 2) - (win_h // 2))
        self.geometry(f"{win_w}x{win_h}+{x_pos}+{y_pos}")
        self.minsize(700, 500)

        self.app_font = font.Font(family=self.settings_manager.get('font_family'), size=self.settings_manager.get('font_size'))
        self.style.configure('.', font=self.app_font)
        self.style.configure('Treeview', rowheight=self.app_font.metrics('linespace') + 5)
        self.style.configure('Treeview.Heading', font=self.app_font)

        self.url_var = tk.StringVar()

        self.current_file_info = None
        self.download_tasks = {}
        self.task_stt_counter = 0
        self.progress_queue = queue.Queue()
        self.downloader = Downloader(self.progress_queue)
        self.sort_column = 'stt'; self.sort_reverse = False
        self.selected_task_id = None

        self.create_widgets()
        self.create_context_menu()
        self.update_settings_ui()
        self.apply_speed_limit_to_downloader()
        self.load_history()

        self._queue_processor_after_id = self.after(100, self.process_progress_queue)
        self.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.bind('<Configure>', self.on_window_configure)

        self.url_var.trace_add('write', self.on_url_entry_change)

    def create_widgets(self):
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(pady=10, padx=10, expand=True, fill=BOTH)

        self.download_tab = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.download_tab, text='Download')
        self.create_download_tab_widgets(self.download_tab)

        self.settings_tab = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.settings_tab, text='Cài đặt')
        self.create_settings_tab_widgets(self.settings_tab)

        self.tree.tag_configure('error', foreground='red')
        self.tree.tag_configure('completed', foreground='gray')
        self.tree.tag_configure('paused', foreground='blue')

    def create_download_tab_widgets(self, parent):
        input_area_frame = ttk.Frame(parent)
        input_area_frame.pack(side=TOP, fill=X, pady=(0, 5), padx=0)

        url_input_frame = ttk.Frame(input_area_frame)
        url_input_frame.pack(fill=X, pady=(0, 2))
        url_label = ttk.Label(url_input_frame, text="URL:")
        url_label.pack(side=LEFT, padx=(0, 5))

        self.url_entry = ttk.Entry(url_input_frame, textvariable=self.url_var)

        self.url_entry.pack(side=LEFT, expand=True, fill=X, padx=5)
        self.url_entry.bind("<Return>", lambda event: self.check_or_download_url())
        self.check_download_button = ttk.Button(url_input_frame, text="🔎 Kiểm tra", command=self.check_or_download_url, width=12)
        self.check_download_button.pack(side=LEFT, padx=(5, 0))

        self.file_info_frame = ttk.Frame(input_area_frame)
        self.file_info_frame.pack(fill=X, pady=2)
        self.file_name_label = ttk.Label(self.file_info_frame, text="Tên file: -", anchor=W)
        self.file_name_label.pack(side=LEFT, padx=5, fill=X, expand=True)
        self.file_size_label = ttk.Label(self.file_info_frame, text="Kích thước: -", width=20, anchor=W)
        self.file_size_label.pack(side=LEFT, padx=5)

        save_frame = ttk.Frame(input_area_frame)
        save_frame.pack(fill=X, pady=(2, 5))
        save_label = ttk.Label(save_frame, text="Lưu tại:")
        save_label.pack(side=LEFT, padx=(0, 5))
        self.save_path_var = tk.StringVar(value=self.settings_manager.get("download_dir"))
        save_entry = ttk.Entry(save_frame, textvariable=self.save_path_var, state="readonly")
        save_entry.pack(side=LEFT, expand=True, fill=X, padx=5)
        browse_button = ttk.Button(save_frame, text="📂 Duyệt", command=self.browse_save_location, width=10)
        browse_button.pack(side=LEFT, padx=(5, 0))

        action_frame = ttk.Frame(parent)
        action_frame.pack(side=BOTTOM, fill=X, pady=(5, 0), padx=0)
        self.pause_button = ttk.Button(action_frame, text="⏸ Tạm dừng", command=self.pause_selected_download, state=DISABLED)
        self.pause_button.pack(side=LEFT, padx=5)
        self.resume_button = ttk.Button(action_frame, text="▶ Tiếp tục", command=self.resume_selected_download, state=DISABLED)
        self.resume_button.pack(side=LEFT, padx=5)
        self.cancel_button = ttk.Button(action_frame, text="❌ Hủy", command=self.cancel_selected_download, state=DISABLED)
        self.cancel_button.pack(side=LEFT, padx=5)
        self.open_folder_button = ttk.Button(action_frame, text="📂 Mở Thư mục", command=self.open_selected_folder, state=DISABLED)
        self.open_folder_button.pack(side=LEFT, padx=5)
        self.delete_button = ttk.Button(action_frame, text="⛔ Xóa File", command=self.delete_selected_file, state=DISABLED)
        self.delete_button.pack(side=LEFT, padx=5)
        self.clear_finished_button = ttk.Button(action_frame, text="🧹 Xóa Hoàn thành", command=self.clear_finished_tasks)
        self.clear_finished_button.pack(side=RIGHT, padx=5)

        self.detailed_progress_frame = ttk.LabelFrame(parent, text="Chi tiết tiến trình", padding=5)
        self.detailed_progress_frame.pack(side=BOTTOM, fill=X, expand=False, pady=(5, 0), padx=0)
        initial_detail_height = self.settings_manager.get("detailed_pane_height")
        self.detailed_progress_frame.config(height=initial_detail_height)


        list_frame = ttk.LabelFrame(parent, text="Danh sách tải về", padding=5)
        list_frame.pack(side=TOP, fill=BOTH, expand=True, pady=0, padx=0)

        columns = ('stt', 'filename', 'elapsed', 'size', 'status', 'speed')
        self.tree = ttk.Treeview(list_frame, columns=columns, show='headings', selectmode='browse')

        col_widths = {'stt': 40, 'filename': 250, 'elapsed': 80, 'size': 110, 'status': 120, 'speed': 90}
        col_anchors = {'stt': CENTER, 'filename': W, 'elapsed': E, 'size': E, 'status': W, 'speed': E}
        self.col_headings = {'stt': 'Stt', 'filename': 'Tên File', 'elapsed': 'Đã chạy', 'size': 'Kích thước', 'status': 'Trạng thái', 'speed': 'Tốc độ'}
        self.sort_indicators = {col: '' for col in columns}

        for col in columns:
            self.tree.heading(col, text=self.col_headings[col] + self.sort_indicators[col], anchor=col_anchors[col],
                              command=lambda c=col: self.sort_treeview(c))
            can_stretch = (col in ['filename', 'status'])
            self.tree.column(col, width=col_widths[col], anchor=col_anchors[col], stretch=can_stretch, minwidth=max(40, col_widths[col]//2))

        vsb = ttk.Scrollbar(list_frame, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(list_frame, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side=RIGHT, fill=Y)
        hsb.pack(side=BOTTOM, fill=X)
        self.tree.pack(side=LEFT, fill=BOTH, expand=True)

        self.tree.bind('<<TreeviewSelect>>', self.on_tree_select)
        self.tree.bind("<Button-3>", self.show_context_menu)
        self.tree.bind("<Double-1>", self.on_tree_double_click)

        self.update_detailed_progress_ui(None)


    def create_settings_tab_widgets(self, parent):
        theme_frame = ttk.LabelFrame(parent, text="Giao diện", padding=10)
        theme_frame.pack(fill=X, pady=5)
        theme_label = ttk.Label(theme_frame, text="Chọn Theme:")
        theme_label.pack(side=LEFT, padx=(0, 10))
        self.theme_combobox = ttk.Combobox(theme_frame, values=self.style.theme_names(), state="readonly")
        self.theme_combobox.pack(side=LEFT, fill=X, expand=True)
        self.theme_combobox.bind("<<ComboboxSelected>>", self.apply_theme)

        download_frame = ttk.LabelFrame(parent, text="Cài đặt Download", padding=10)
        download_frame.pack(fill=X, pady=5)

        threads_frame = ttk.Frame(download_frame)
        threads_frame.pack(fill=X, pady=3)
        threads_label = ttk.Label(threads_frame, text="Số luồng tải tối đa:")
        threads_label.pack(side=LEFT, padx=(0, 10))
        self.threads_spinbox_var = tk.IntVar(value=self.settings_manager.get("num_threads"))
        self.threads_spinbox = ttk.Spinbox(threads_frame, from_=1, to=64, width=5, textvariable=self.threads_spinbox_var)
        self.threads_spinbox.pack(side=LEFT)
        ToolTip(self.threads_spinbox, text="Số kết nối đồng thời cho mỗi file. Nhiều hơn không phải lúc nào cũng nhanh hơn.")

        speed_limit_frame = ttk.Frame(download_frame)
        speed_limit_frame.pack(fill=X, pady=3)
        self.speed_limit_enabled_var = tk.BooleanVar(value=self.settings_manager.get("speed_limit_enabled"))
        self.speed_limit_check = ttk.Checkbutton(speed_limit_frame, text="Giới hạn tốc độ tải về (Toàn cục)", variable=self.speed_limit_enabled_var, command=self.toggle_speed_limit_entry)
        self.speed_limit_check.pack(side=LEFT, padx=(0, 10))
        ToolTip(self.speed_limit_check, text="Bật/Tắt giới hạn tốc độ tải tối đa cho TOÀN BỘ ứng dụng.")
        self.speed_limit_mbps_var = tk.DoubleVar(value=self.settings_manager.get("speed_limit_mbps"))
        self.speed_limit_entry = ttk.Entry(speed_limit_frame, textvariable=self.speed_limit_mbps_var, width=6)
        self.speed_limit_entry.pack(side=LEFT, padx=(0, 2))
        ToolTip(self.speed_limit_entry, text="Tốc độ tải tối đa mong muốn (ví dụ: 5.5)")
        speed_unit_label = ttk.Label(speed_limit_frame, text="MB/s")
        speed_unit_label.pack(side=LEFT)

        save_dir_frame = ttk.Frame(download_frame)
        save_dir_frame.pack(fill=X, pady=3)
        save_dir_label = ttk.Label(save_dir_frame, text="Thư mục lưu mặc định:")
        save_dir_label.pack(side=LEFT, padx=(0, 10))
        save_dir_display_label = ttk.Label(save_dir_frame, textvariable=self.save_path_var, relief="sunken", padding=2)
        save_dir_display_label.pack(side=LEFT, fill=X, expand=True, padx=(0, 5))
        change_save_dir_button = ttk.Button(save_dir_frame, text="Thay đổi...", command=self.browse_save_location, width=10)
        change_save_dir_button.pack(side=LEFT)

        font_ui_frame = ttk.LabelFrame(parent, text="Font Chữ (Yêu cầu khởi động lại)", padding=10)
        font_ui_frame.pack(fill=X, pady=5)
        try: available_fonts = sorted(list(font.families()))
        except tk.TclError: available_fonts = [self.settings_manager.get("font_family")]
        font_family_frame = ttk.Frame(font_ui_frame)
        font_family_frame.pack(fill=X, pady=2)
        font_family_label = ttk.Label(font_family_frame, text="Font Family:")
        font_family_label.pack(side=LEFT, padx=(0, 10), anchor=W)
        self.font_family_combobox = ttk.Combobox(font_family_frame, values=available_fonts, state="readonly", width=30)
        self.font_family_combobox.pack(side=LEFT, fill=X, expand=True)
        font_size_frame = ttk.Frame(font_ui_frame)
        font_size_frame.pack(fill=X, pady=2, anchor=W)
        font_size_label = ttk.Label(font_size_frame, text="Cỡ chữ:")
        font_size_label.pack(side=LEFT, padx=(0, 10), anchor=W)
        self.font_size_var = tk.IntVar(value=self.settings_manager.get("font_size"))
        self.font_size_spinbox = ttk.Spinbox(font_size_frame, from_=8, to=20, width=5, textvariable=self.font_size_var)
        self.font_size_spinbox.pack(side=LEFT)

        window_size_frame = ttk.LabelFrame(parent, text="Kích Thước Cửa Sổ (Yêu cầu khởi động lại)", padding=10)
        window_size_frame.pack(fill=X, pady=5)
        win_w_label = ttk.Label(window_size_frame, text="Rộng:")
        win_w_label.pack(side=LEFT, padx=(0, 5))
        self.win_w_var = tk.IntVar(value=self.settings_manager.get("window_width"))
        win_w_entry = ttk.Entry(window_size_frame, textvariable=self.win_w_var, width=7)
        win_w_entry.pack(side=LEFT, padx=(0, 15))
        win_h_label = ttk.Label(window_size_frame, text="Cao:")
        win_h_label.pack(side=LEFT, padx=(0, 5))
        self.win_h_var = tk.IntVar(value=self.settings_manager.get("window_height"))
        win_h_entry = ttk.Entry(window_size_frame, textvariable=self.win_h_var, width=7)
        win_h_entry.pack(side=LEFT)

        save_button_frame = ttk.Frame(parent)
        save_button_frame.pack(pady=20)
        save_button = ttk.Button(save_button_frame, text="💾 Lưu Cài Đặt", command=self.save_settings, style='success.TButton')
        save_button.pack(side=LEFT, padx=5)
        reset_button = ttk.Button(save_button_frame, text="♻ Đặt lại Mặc định", command=self.reset_settings, style='warning.TButton')
        reset_button.pack(side=LEFT, padx=5)


    def on_url_entry_change(self, *args):
        """Callback executed when the URL entry text variable changes."""
        try:
            if self.check_download_button.winfo_exists() and \
               self.file_name_label.winfo_exists() and \
               self.file_size_label.winfo_exists():
                if self.check_download_button.cget('text') == "⏬ Download":
                    self.check_download_button.config(text="🔎 Kiểm tra", state=NORMAL)
                    self.file_name_label.config(text="Tên file: -")
                    self.file_size_label.config(text="Kích thước: -")
                    self.current_file_info = None
        except tk.TclError:
            pass
        except AttributeError:
            pass


    def toggle_speed_limit_entry(self):
        if self.speed_limit_enabled_var.get(): self.speed_limit_entry.config(state=NORMAL)
        else: self.speed_limit_entry.config(state=DISABLED)

    def browse_save_location(self):
        directory = filedialog.askdirectory(initialdir=self.save_path_var.get(), title="Chọn thư mục lưu file")
        if directory:
            norm_dir = os.path.normpath(directory)
            self.save_path_var.set(norm_dir)

    def check_or_download_url(self):
        url = self.url_var.get().strip()
        if not url: messagebox.showwarning("Thiếu URL", "Vui lòng nhập URL.", parent=self); return
        if not url.lower().startswith(('http://', 'https://')): messagebox.showerror("URL không hợp lệ", "URL phải bắt đầu bằng http:// hoặc https://", parent=self); return
        if self.check_download_button.cget('text') == "⏬ Download": self.start_download()
        else: self.check_url(url)

    def check_url(self, url):
        self.check_download_button.config(state=DISABLED, text="⏳ Đang kiểm tra...")
        self.file_name_label.config(text="Tên file: Đang kiểm tra...")
        self.file_size_label.config(text="Kích thước: Đang kiểm tra...")
        self.current_file_info = None
        self._checking_url = True
        thread = threading.Thread(target=self._check_url_worker, args=(url,), daemon=True)
        thread.start()

    def _check_url_worker(self, url):
        try:
            headers = { 'User-Agent': 'PythonDownloadManager/1.0', 'Accept-Encoding': 'identity' }
            response = requests.head(url, allow_redirects=True, timeout=20, headers=headers)
            response.raise_for_status()

            content_length = response.headers.get('content-length')
            accept_ranges = response.headers.get('accept-ranges', '').lower()
            content_disposition = response.headers.get('content-disposition')
            final_url = response.url
            needs_get = False
            if not content_length: needs_get = True
            else:
                try:
                    if int(content_length) < 0: needs_get = True
                except ValueError: needs_get = True
            if needs_get:
                 print("HEAD request didn't return valid Content-Length, trying GET...")
                 get_headers = headers.copy(); get_headers['Range'] = 'bytes=0-1'
                 get_resp = requests.get(url, stream=True, timeout=10, headers=get_headers, allow_redirects=True)
                 get_resp.raise_for_status()
                 content_range = get_resp.headers.get('content-range')
                 if content_range:
                     match = re.search(r'/(\d+)$', content_range)
                     if match: content_length = match.group(1)
                     else: content_length = get_resp.headers.get('content-length')
                 else: content_length = get_resp.headers.get('content-length')
                 accept_ranges = get_resp.headers.get('accept-ranges', '').lower()
                 content_disposition = get_resp.headers.get('content-disposition')
                 final_url = get_resp.url
                 get_resp.close()
                 if not content_length:
                     self.after(0, self.update_check_result, None, "Không thể lấy kích thước file (HEAD và GET).")
                     return
            try:
                 total_size = int(content_length)
                 if total_size < 0: raise ValueError("Kích thước file không hợp lệ (< 0).")
            except (ValueError, TypeError) as e:
                  self.after(0, self.update_check_result, None, f"Kích thước file không hợp lệ: {e}")
                  return

            range_support = (accept_ranges == 'bytes')
            if not range_support:
                  print(f"Warning: Server does not report 'Accept-Ranges: bytes' (reported: '{accept_ranges}') for {final_url}. Download may be single-threaded.")

            filename = "Unknown"
            if content_disposition:
                  fn_star_match = re.search(r"filename\*=([^']+)'([^']*)'\"?([^;\"]+)\"?", content_disposition)
                  if fn_star_match:
                      encoding, _, encoded_name = fn_star_match.groups()
                      try: filename = unquote(encoded_name, encoding=encoding or 'utf-8', errors='replace')
                      except Exception as e:
                          print(f"Error decoding filename* ({encoding}): {e}. Trying plain filename.")
                          filename = "Unknown"
                  if filename == "Unknown":
                      fn_match = re.search(r'filename="?([^;"]+)"?', content_disposition)
                      if fn_match:
                          raw_filename = fn_match.group(1).strip().strip("'\"")
                          try: filename = unquote(raw_filename, encoding='utf-8', errors='strict')
                          except UnicodeDecodeError:
                              try:
                                  filename = unquote(raw_filename, encoding='latin-1', errors='replace')
                                  print(f"Warning: Used latin-1 fallback for filename: {filename}")
                              except Exception: filename = raw_filename
                          except Exception: filename = raw_filename
            if filename == "Unknown" or not filename.strip():
                  from urllib.parse import urlparse
                  try:
                      parsed_path = urlparse(final_url).path
                      base_name = os.path.basename(unquote(parsed_path, encoding='utf-8', errors='replace'))
                      if base_name: filename = base_name
                      else: filename = f"download_{int(time.time())}"
                  except Exception as parse_err:
                      print(f"Error parsing URL for filename: {parse_err}")
                      filename = f"download_{int(time.time())}"

            filename = re.sub(r'[\x00-\x1f\x7f]', '', filename)
            filename = re.sub(r'[\\/*?:"<>|]', '_', filename)
            filename = filename.strip('. ')[:240]
            if not filename: filename = f"download_{int(time.time())}"

            file_info = {
                'name': filename, 'size': total_size, 'size_readable': self.format_size(total_size),
                'url': final_url, 'range_support': range_support
            }
            self.after(0, self.update_check_result, file_info, None)

        except requests.exceptions.Timeout: self.after(0, self.update_check_result, None, f"Lỗi: Hết thời gian chờ khi kiểm tra URL.")
        except requests.exceptions.SSLError as e: self.after(0, self.update_check_result, None, f"Lỗi SSL: {e}")
        except requests.exceptions.ConnectionError as e:
             err_str = str(e)
             if "getaddrinfo failed" in err_str or "Errno 11001" in err_str: err_msg = "Không thể phân giải tên máy chủ (DNS)."
             elif "Connection refused" in err_str: err_msg = "Kết nối bị từ chối bởi máy chủ."
             else: err_msg = f"Lỗi kết nối: {e}"
             self.after(0, self.update_check_result, None, err_msg)
        except requests.exceptions.RequestException as e:
            status_code = e.response.status_code if e.response is not None else 'N/A'
            error_text = e.response.text if e.response is not None else str(e)
            if len(error_text) > 200: error_text = error_text[:200] + "..."
            self.after(0, self.update_check_result, None, f"Lỗi kiểm tra URL: {status_code} - {error_text}")
        except Exception as e:
             import traceback
             print(f"Unknown error checking URL: {e}\n{traceback.format_exc()}")
             self.after(0, self.update_check_result, None, f"Lỗi không xác định: {e}")
        finally: self.after(0, lambda: setattr(self, '_checking_url', False))


    def update_check_result(self, file_info, error_message):
        self._checking_url = False
        if not error_message and file_info:
             self.current_file_info = file_info
             display_name = file_info['name']; max_len = 70
             if len(display_name) > max_len: display_name = display_name[:max_len-3] + "..."
             self.file_name_label.config(text=f"Tên file: {display_name}")
             self.file_size_label.config(text=f"Kích thước: {file_info['size_readable']}")
             current_url_in_entry = self.url_var.get().strip()
             if current_url_in_entry == file_info.get('url', ''):
                 self.check_download_button.config(text="⏬ Download", state=NORMAL)
             else:
                 self.check_download_button.config(text="🔎 Kiểm tra", state=NORMAL)
                 self.file_name_label.config(text="Tên file: -")
                 self.file_size_label.config(text="Kích thước: -")
                 self.current_file_info = None
        elif error_message:
            messagebox.showerror("Lỗi Kiểm Tra URL", error_message, parent=self)
            self.check_download_button.config(state=NORMAL, text="🔎 Kiểm tra")
            self.file_name_label.config(text="Tên file: Lỗi")
            self.file_size_label.config(text="Kích thước: Lỗi")
            self.current_file_info = None
        else:
             self.check_download_button.config(state=NORMAL, text="🔎 Kiểm tra")

    def start_download(self):
        if not self.current_file_info: messagebox.showerror("Lỗi", "Vui lòng kiểm tra URL hợp lệ trước.", parent=self); return

        num_threads = self.threads_spinbox_var.get()
        if not self.current_file_info.get('range_support', True):
             if messagebox.askyesno("Cảnh báo", "Máy chủ có thể không hỗ trợ tải đa luồng (resume).\nTiếp tục tải bằng một luồng duy nhất?", parent=self): num_threads = 1
             else: return

        url = self.current_file_info['url']; filename = self.current_file_info['name']
        total_size = self.current_file_info['size']; save_dir = self.save_path_var.get()
        output_filename = os.path.join(save_dir, filename)

        try: Path(save_dir).mkdir(parents=True, exist_ok=True)
        except OSError as e: messagebox.showerror("Lỗi Thư Mục Lưu", f"Không thể tạo hoặc truy cập thư mục lưu:\n{save_dir}\n{e}", parent=self); return

        counter = 1; base, ext = os.path.splitext(filename)
        base = re.sub(r'\s*\(\d+\)$', '', base).strip()
        original_output_filename = output_filename
        while os.path.exists(output_filename):
            new_filename = f"{base} ({counter}){ext}"
            output_filename = os.path.join(save_dir, new_filename)
            counter += 1
        if output_filename != original_output_filename:
             new_base_filename = os.path.basename(output_filename)
             print(f"File exists, renaming to: {new_base_filename}")
             self.current_file_info['name'] = new_base_filename
             filename = new_base_filename

        temp_base_dir = os.path.join(save_dir, DEFAULT_TEMP_DIR_NAME)
        try: os.makedirs(temp_base_dir, exist_ok=True)
        except OSError as e: messagebox.showerror("Lỗi Tạo Thư Mục", f"Không thể tạo thư mục tạm:\n{temp_base_dir}\n{e}", parent=self); return

        task_id = self.downloader.start_new_download(url, num_threads, output_filename, temp_base_dir, self.current_file_info)

        if task_id:
            self.task_stt_counter += 1; stt = self.task_stt_counter
            item_id = self.tree.insert('', 0, iid=task_id, values=(
                stt, filename, '0s', self.format_size(total_size), 'Bắt đầu...', '-'
            ))
            self.download_tasks[task_id] = {
                 'item_id': item_id, 'task_id': task_id, 'stt': stt, 'filename': filename,
                 'total_size': total_size, 'output_path': output_filename,
                 'start_time': time.time(), 'last_update_time': time.time(),
                 'bytes_downloaded': 0, 'last_bytes_downloaded': 0,
                 'status': 'Bắt đầu...', 'num_parts': num_threads,
                 'parts': {}, 'parts_widgets': {}, 'url': url,
                 'last_detailed_update_time': 0,
                 'speed_limit_mbps': NO_LIMIT
            }
            print(f"Started download task: {task_id} (Stt: {stt}) for {filename}")

            self.url_var.set("")
            self.url_entry.focus()

            if item_id: self.tree.selection_set(item_id); self.tree.focus(item_id); self.on_tree_select()
        else: print("Failed to initiate download task.")


    def process_progress_queue(self):
        tasks_to_update = {}
        try:
            while True:
                message = self.progress_queue.get_nowait()
                task_id = message.get("task_id")
                if not task_id: continue
                if task_id not in self.download_tasks:
                     if message.get("type") == "error": print(f"Received error for unknown/removed task {task_id}: {message.get('error', 'Unknown error')}")
                     continue
                if task_id not in tasks_to_update:
                    tasks_to_update[task_id] = {'parts_progress': [], 'status_update': None, 'error': None, 'info_update': None, 'start': None}
                msg_type = message.get("type")
                if msg_type == "start": tasks_to_update[task_id]['start'] = message
                elif msg_type == "part_progress": tasks_to_update[task_id]['parts_progress'].append(message)
                elif msg_type == "status_update": tasks_to_update[task_id]['status_update'] = message
                elif msg_type == "error": tasks_to_update[task_id]['error'] = message
                elif msg_type == "info_update": tasks_to_update[task_id]['info_update'] = message
                elif msg_type == "part_error":
                    print(f"Part Error Task {task_id} Part {message.get('part_num')}: {message.get('error')}")
        except queue.Empty: pass

        for task_id, updates in tasks_to_update.items():
            if task_id not in self.download_tasks: continue
            task_info = self.download_tasks[task_id]
            item_id = task_info.get('item_id')
            if not item_id or not self.tree.exists(item_id): continue

            tree_values_changed = False
            try:
                current_values = list(self.tree.item(item_id, 'values'))
                current_tags = set(self.tree.item(item_id, 'tags'))
            except tk.TclError: continue

            new_tree_values = current_values[:]
            new_tags = current_tags.copy()

            if updates['error']:
                message = updates['error']
                task_info['status'] = 'Lỗi'
                if 'start_time' in task_info: new_tree_values[2] = self.format_time(time.time() - task_info['start_time'], short=True)
                else: new_tree_values[2] = '-'
                new_tree_values[4] = 'Lỗi'
                new_tree_values[5] = '-'
                new_tags = {'error'}
                tree_values_changed = True
            elif updates['start'] and task_info['status'] != 'Lỗi':
                 message = updates['start']
                 task_info['status'] = 'Đang tải...'
                 task_info['start_time'] = time.time()
                 task_info['total_size'] = message.get('total_size', task_info.get('total_size', 0))
                 task_info['num_parts'] = message.get('num_parts', task_info.get('num_parts', 1))
                 size_str = self.format_size(task_info['total_size']) if task_info['total_size'] else "N/A"
                 new_tree_values = [task_info['stt'], task_info['filename'], '0s', size_str, task_info['status'], '0 B/s']
                 new_tags = set()
                 tree_values_changed = True

            if updates['status_update'] and task_info['status'] != 'Lỗi':
                message = updates['status_update']
                new_status = message['status']
                if new_status != task_info['status']:
                    task_info['status'] = new_status
                    new_tree_values[4] = task_info['status']
                    is_active = task_info['status'] == 'Đang tải...'
                    is_paused = task_info['status'] == 'Đã tạm dừng'
                    is_complete_or_cancelled = task_info['status'] in ["Hoàn thành", "Đã hủy", "Hoàn thành (kích thước khác!)"]
                    if is_complete_or_cancelled: new_tree_values[5] = "-"; new_tags = {'completed'};
                    elif is_paused: new_tags = {'paused'}; new_tree_values[5] = "-"
                    elif is_active: new_tags = set()
                    else: new_tags = set(); new_tree_values[5] = '-'
                    if 'start_time' in task_info and is_complete_or_cancelled: new_tree_values[2] = self.format_time(time.time() - task_info['start_time'], short=True)
                    tree_values_changed = True
                    if (message.get('progress') == 100 and task_info['status'] != 'Lỗi') \
                       or task_info['status'] in ["Hoàn thành", "Hoàn thành (kích thước khác!)"]:
                         task_info['progress'] = 100
                         if task_info['total_size'] > 0: task_info['bytes_downloaded'] = task_info['total_size']
                         if self.selected_task_id == task_id: self.update_detailed_progress_widgets(task_id)

            if updates['info_update']:
                 message = updates['info_update']
                 new_num_parts = message.get('num_parts')
                 if new_num_parts is not None and new_num_parts != task_info.get('num_parts'):
                      print(f"Task {task_id} updated num_parts to {new_num_parts}")
                      task_info['num_parts'] = new_num_parts
                      if self.selected_task_id == task_id: self.update_detailed_progress_ui(task_id)

            if updates['parts_progress'] and task_info['status'] == 'Đang tải...':
                for part_msg in updates['parts_progress']:
                    part_num = part_msg['part_num']
                    task_info['parts'][part_num] = {'current': part_msg['current'], 'total': part_msg['total'], 'speed': part_msg['speed_bps'], 'status': part_msg['status']}
                total_downloaded = sum(p_data.get('current', 0) for p_data in task_info['parts'].values())
                task_info['bytes_downloaded'] = total_downloaded
                total_speed_bps = sum(p_data.get('speed', 0) for p_data in task_info['parts'].values() if p_data.get('status') == 'Đang tải')
                progress_percent = (total_downloaded / task_info['total_size']) * 100 if task_info['total_size'] > 0 else 0
                task_info['progress'] = progress_percent
                elapsed_since_start = time.time() - task_info.get('start_time', time.time())
                new_tree_values[2] = self.format_time(elapsed_since_start, short=True)
                new_tree_values[5] = self.format_speed(total_speed_bps / 8)
                tree_values_changed = True

            if tree_values_changed:
                try:
                     tags_to_set = tuple(new_tags)
                     self.tree.item(item_id, values=tuple(new_tree_values), tags=tags_to_set)
                except tk.TclError as e: print(f"Error updating tree item {item_id} (maybe deleted?): {e}")

            if self.selected_task_id == task_id:
                 now = time.time()
                 needs_detailed_widget_update = (updates['parts_progress'] or now - task_info.get('last_detailed_update_time', 0) > 0.6)
                 if updates['status_update'] or updates['error']: self.update_action_buttons_state(task_id)
                 if needs_detailed_widget_update:
                      self.update_detailed_progress_widgets(task_id)
                      task_info['last_detailed_update_time'] = now
                 if tree_values_changed: self._update_detailed_status_label(task_id)

        if hasattr(self, '_queue_processor_after_id') and self._queue_processor_after_id:
             try: self.after_cancel(self._queue_processor_after_id)
             except tk.TclError: pass
        if self.winfo_exists():
            self._queue_processor_after_id = self.after(UPDATE_INTERVAL_MS, self.process_progress_queue)

    def sort_treeview(self, col):
        if col not in self.col_headings: return
        items = []
        for iid in self.tree.get_children(''):
             task_data = self.download_tasks.get(iid)
             if not task_data: continue
             val_to_sort = None
             if col == 'stt': val_to_sort = task_data.get('stt', 0)
             elif col == 'filename': val_to_sort = task_data.get('filename', '').lower()
             elif col == 'elapsed':
                  start = task_data.get('start_time', 0); status = task_data.get('status','')
                  is_active = status in ['Đang tải...', 'Đang ghép file...', 'Bắt đầu...']
                  if start > 0 and is_active: val_to_sort = time.time() - start
                  else: val_to_sort = float('inf')
             elif col == 'size': val_to_sort = task_data.get('total_size', 0)
             elif col == 'status': val_to_sort = task_data.get('status', '')
             elif col == 'speed':
                  try:
                      current_values = self.tree.item(iid, 'values')
                      if len(current_values) > 5: val_to_sort = self.parse_speed(current_values[5])
                      else: val_to_sort = 0
                  except (IndexError, ValueError, TypeError, tk.TclError): val_to_sort = 0
             if val_to_sort is not None: items.append((val_to_sort, iid))

        reverse_sort = self.sort_reverse if self.sort_column == col else False
        next_reverse_state = not reverse_sort if self.sort_column == col else False
        try: items.sort(key=lambda x: x[0], reverse=reverse_sort)
        except TypeError as e:
            print(f"Error sorting column {col} due to mixed types: {e}. Trying string sort.")
            try: items.sort(key=lambda x: str(x[0]).lower(), reverse=reverse_sort)
            except Exception as e2: print(f"Fallback string sort failed for column {col}: {e2}")
        except Exception as e: print(f"Error sorting column {col}: {e}")

        for index, (val, iid) in enumerate(items):
            try:
                 if self.tree.exists(iid): self.tree.move(iid, '', index)
            except tk.TclError: continue

        if self.sort_column and self.sort_column != col and self.sort_column in self.col_headings:
             current_heading = self.col_headings.get(self.sort_column, self.sort_column)
             try:
                  if self.tree.winfo_exists(): self.tree.heading(self.sort_column, text=current_heading)
             except tk.TclError: pass
        indicator = ' ⏬' if reverse_sort else ' ⏫'
        new_heading = self.col_headings.get(col, col) + indicator
        try:
             if self.tree.winfo_exists(): self.tree.heading(col, text=new_heading)
        except tk.TclError: pass

        self.sort_column = col
        self.sort_reverse = next_reverse_state

    def parse_speed(self, speed_str):
        if not isinstance(speed_str, str): return 0
        speed_str = speed_str.strip().upper(); parts = speed_str.split()
        if len(parts) != 2 or parts[0] in ['-', 'N/A', 'TÍNH', '0', '0.0']: return 0
        val_str, unit_str = parts
        try:
             val = float(val_str); unit = unit_str.replace('/S', '').replace('/SEC', '')
             multipliers = {'B': 1, 'K': 1024, 'KB': 1024, 'M': 1024**2, 'MB': 1024**2, 'G': 1024**3, 'GB': 1024**3, 'T': 1024**4, 'TB': 1024**4}
             multiplier = multipliers.get(unit.rstrip('.'), 0)
             return int(val * multiplier)
        except (ValueError, TypeError, KeyError): return 0

    def update_detailed_progress_ui(self, task_id):
        for widget in self.detailed_progress_frame.winfo_children(): widget.destroy()
        if task_id and task_id in self.download_tasks: self.download_tasks[task_id]['parts_widgets'] = {}

        if task_id is None or task_id not in self.download_tasks:
            self.detailed_progress_frame.config(text="Chi tiết tiến trình")
            placeholder_label = ttk.Label(self.detailed_progress_frame, text="Chọn một mục để xem chi tiết.")
            placeholder_label.pack(padx=10, pady=20)
            self.selected_task_id = None
            return

        task_info = self.download_tasks[task_id]
        self.selected_task_id = task_id
        display_filename = task_info['filename']; max_len = 60
        if len(display_filename) > max_len: display_filename = display_filename[:max_len-3]+"..."
        self.detailed_progress_frame.config(text=f"Chi tiết: {display_filename}")

        total_progress_frame = ttk.Frame(self.detailed_progress_frame)
        total_progress_frame.pack(side=TOP, fill=X, expand=False, pady=(5, 2), padx=5)
        main_pb = ttk.Progressbar(total_progress_frame, orient=HORIZONTAL, length=300, mode='determinate', maximum=100)
        main_pb.pack(side=LEFT, fill=X, expand=True, padx=(0, 10))
        task_info['parts_widgets']['main_pb'] = main_pb
        main_percent_label = ttk.Label(total_progress_frame, text="0.0%", width=7, anchor=E)
        main_percent_label.pack(side=LEFT)
        task_info['parts_widgets']['main_percent_label'] = main_percent_label
        main_status_label = ttk.Label(total_progress_frame, text=f"Trạng thái: {task_info.get('status', 'N/A')}", anchor=W)
        main_status_label.pack(side=LEFT, padx=(15, 0), fill=X, expand=True)
        task_info['parts_widgets']['main_status_label'] = main_status_label

        scrollable_container = ttk.Frame(self.detailed_progress_frame)
        scrollable_container.pack(side=TOP, fill=X, expand=False, pady=(5, 0), padx=5)
        parts_canvas = tk.Canvas(scrollable_container, borderwidth=0, highlightthickness=0)
        h_scrollbar = ttk.Scrollbar(scrollable_container, orient=HORIZONTAL, command=parts_canvas.xview)
        h_scrollbar.pack(side=BOTTOM, fill=X)
        parts_canvas.pack(side=TOP, fill=X, expand=False)
        parts_canvas.configure(xscrollcommand=h_scrollbar.set)
        parts_content_frame = ttk.Frame(parts_canvas)
        parts_canvas.create_window((0, 0), window=parts_content_frame, anchor="nw", tags="content_frame")

        num_parts = task_info.get('num_parts', 0)
        if num_parts > 0:
            max_cols = 4
            for i in range(num_parts):
                part_frame = ttk.Frame(parts_content_frame)
                row, col = divmod(i, max_cols)
                part_frame.grid(row=row, column=col, padx=3, pady=1, sticky="w")
                part_label = ttk.Label(part_frame, text=f"P{i}:", width=4); part_label.pack(side=LEFT, padx=(3, 2))
                part_pb = ttk.Progressbar(part_frame, orient=HORIZONTAL, length=80, mode='determinate', maximum=100); part_pb.pack(side=LEFT, fill=X, expand=True, padx=2)
                part_info_label = ttk.Label(part_frame, text="0%", width=5, anchor=E); part_info_label.pack(side=LEFT, padx=(2, 3))
                task_info['parts_widgets'][i] = {'pb': part_pb, 'info_label': part_info_label}
        else:
             no_info_label = ttk.Label(parts_content_frame, text="Chưa có thông tin chi tiết phần."); no_info_label.pack(pady=10)

        def update_scroll_region(event=None):
            parts_content_frame.update_idletasks()
            bbox = parts_canvas.bbox("all")
            if bbox:
                scroll_width, scroll_height = bbox[2] - bbox[0], bbox[3] - bbox[1]
                parts_canvas.config(scrollregion=(0, 0, scroll_width, scroll_height))
                new_canvas_height = scroll_height + 2
                if abs(parts_canvas.winfo_height() - new_canvas_height) > 1: parts_canvas.config(height=new_canvas_height)
        parts_content_frame.bind("<Configure>", update_scroll_region, add='+')
        parts_canvas.after(10, update_scroll_region)

        self.update_detailed_progress_widgets(task_id)
        self._update_detailed_status_label(task_id)

    def update_detailed_progress_widgets(self, task_id):
        if task_id != self.selected_task_id or task_id not in self.download_tasks: return
        task_info = self.download_tasks[task_id]; widgets = task_info.get('parts_widgets', {})
        overall_progress = task_info.get('progress', 0)
        if 'main_pb' in widgets and widgets['main_pb'].winfo_exists(): widgets['main_pb']['value'] = overall_progress
        if 'main_percent_label' in widgets and widgets['main_percent_label'].winfo_exists(): widgets['main_percent_label'].config(text=f"{overall_progress:.1f}%")
        num_parts = task_info.get('num_parts', 0)
        for i in range(num_parts):
            part_widgets = widgets.get(i)
            if part_widgets and part_widgets['pb'].winfo_exists() and part_widgets['info_label'].winfo_exists():
                 part_data = task_info.get('parts',{}).get(i)
                 if part_data:
                    part_total = part_data.get('total', 1); part_current = part_data.get('current', 0)
                    part_percent = (part_current / part_total) * 100 if part_total > 0 else 0
                    part_widgets['pb']['value'] = part_percent; part_widgets['info_label'].config(text=f"{part_percent:.0f}%")
                 else: part_widgets['pb']['value'] = 0; part_widgets['info_label'].config(text="0%")

    def _update_detailed_status_label(self, task_id):
         if task_id != self.selected_task_id or task_id not in self.download_tasks: return
         task_info = self.download_tasks[task_id]; widgets = task_info.get('parts_widgets', {})
         if 'main_status_label' in widgets and widgets['main_status_label'].winfo_exists():
             current_status = task_info.get('status', 'Không rõ'); status_text = f"Trạng thái: {current_status}"
             task_limit_mbps = task_info.get('speed_limit_mbps', NO_LIMIT)
             if task_limit_mbps != NO_LIMIT: status_text += f" (Giới hạn: {task_limit_mbps:.1f} MB/s)"
             status_color = self.style.lookup('TLabel', 'foreground')
             try:
                 if self.tree.exists(task_id):
                     current_tags = self.tree.item(task_id, 'tags')
                     if current_tags:
                         tag_name = current_tags[0]
                         if tag_name == 'error': status_color = 'red'
                         elif tag_name == 'paused': status_color = 'blue'
                         elif tag_name == 'completed': status_color = 'gray'
                         else:
                             try:
                                 tag_config = self.tree.tag_configure(tag_name)
                                 if tag_config and 'foreground' in tag_config:
                                     fg = tag_config['foreground']
                                     if isinstance(fg, (list, tuple)) and len(fg) >= 4 and fg[3]: status_color = fg[3]
                                     elif isinstance(fg, (list, tuple)) and len(fg) >= 3 and fg[2]: status_color = fg[2]
                                     elif isinstance(fg, str) and fg: status_color = fg
                             except tk.TclError: pass
             except tk.TclError: pass
             widgets['main_status_label'].config(text=status_text, foreground=status_color)

    def update_action_buttons_state(self, task_id):
        status = None; file_exists = False; output_path = None; is_active_in_downloader = False
        if task_id and task_id in self.download_tasks:
            task_info = self.download_tasks[task_id]; status = task_info.get('status', '')
            output_path = task_info.get('output_path', '')
            if output_path: file_exists = os.path.exists(output_path) and os.path.isfile(output_path)
            is_active_in_downloader = task_id in self.downloader.active_downloads
        can_pause = status == 'Đang tải...' and is_active_in_downloader
        can_resume = status == 'Đã tạm dừng' and is_active_in_downloader
        can_cancel = status in ['Đang tải...', 'Đã tạm dừng', 'Bắt đầu...', 'Đang ghép file...'] and is_active_in_downloader
        can_open = status in ['Hoàn thành', "Hoàn thành (kích thước khác!)"] and file_exists
        can_delete_file = file_exists and status not in ['Đang tải...', 'Đang ghép file...']
        if hasattr(self, 'pause_button') and self.pause_button.winfo_exists(): self.pause_button.config(state=NORMAL if can_pause else DISABLED)
        if hasattr(self, 'resume_button') and self.resume_button.winfo_exists(): self.resume_button.config(state=NORMAL if can_resume else DISABLED)
        if hasattr(self, 'cancel_button') and self.cancel_button.winfo_exists(): self.cancel_button.config(state=NORMAL if can_cancel else DISABLED)
        if hasattr(self, 'open_folder_button') and self.open_folder_button.winfo_exists(): self.open_folder_button.config(state=NORMAL if can_open else DISABLED)
        if hasattr(self, 'delete_button') and self.delete_button.winfo_exists(): self.delete_button.config(state=NORMAL if can_delete_file else DISABLED)

    def on_tree_select(self, event=None):
        selected_items = self.tree.selection()
        new_selected_id = selected_items[0] if selected_items else None
        if new_selected_id != self.selected_task_id: self.selected_task_id = new_selected_id
        if self.selected_task_id:
             if self.selected_task_id in self.download_tasks:
                 self.update_detailed_progress_ui(self.selected_task_id)
                 self.update_action_buttons_state(self.selected_task_id)
             else:
                  print(f"Warning: Selected task {self.selected_task_id} not found in download_tasks.")
                  self.update_detailed_progress_ui(None); self.update_action_buttons_state(None)
        else: self.update_detailed_progress_ui(None); self.update_action_buttons_state(None)
        if self.selected_task_id and self.selected_task_id in self.download_tasks: self._update_detailed_status_label(self.selected_task_id)

    def on_tree_double_click(self, event=None):
        iid = self.tree.identify_row(event.y)
        if not iid: return
        if iid in self.download_tasks:
             task_info = self.download_tasks[iid]; status = task_info.get('status','')
             output_path = task_info.get('output_path', ''); file_exists = os.path.exists(output_path) if output_path else False
             if status in ['Hoàn thành', "Hoàn thành (kích thước khác!)"] and file_exists: self.open_selected_file(iid)
             elif status == 'Đã tạm dừng': self.resume_selected_download()
             elif status == 'Đang tải...': self.pause_selected_download()

    def pause_selected_download(self):
        if self.selected_task_id: self.downloader.pause_download(self.selected_task_id)
    def resume_selected_download(self):
        if self.selected_task_id: self.downloader.resume_download(self.selected_task_id)
    def cancel_selected_download(self):
        if self.selected_task_id:
            task_info = self.download_tasks.get(self.selected_task_id)
            if task_info:
                 filename = task_info.get('filename', 'task này')
                 if messagebox.askyesno("Xác nhận Hủy", f"Bạn có chắc muốn hủy download:\n{filename}?", parent=self):
                     if not self.downloader.cancel_download(self.selected_task_id): messagebox.showerror("Lỗi", "Không thể gửi yêu cầu hủy task.", parent=self)
            else: messagebox.showerror("Lỗi", "Task không tồn tại.", parent=self)
        else: messagebox.showwarning("Chưa chọn", "Vui lòng chọn download để hủy.", parent=self)
    def open_selected_folder(self):
         if self.selected_task_id:
              task_info = self.download_tasks.get(self.selected_task_id)
              if task_info and task_info.get('output_path'):
                   folder_path = os.path.dirname(task_info['output_path'])
                   try:
                       if os.path.isdir(folder_path):
                           print(f"Opening folder: {folder_path}")
                           system = platform.system()
                           if system == "Windows":
                               file_path = task_info['output_path']
                               if os.path.exists(file_path): subprocess.run(['explorer', '/select,', file_path], check=False)
                               else: os.startfile(folder_path)
                           elif system == "Darwin": subprocess.run(["open", "-R", task_info['output_path']], check=True)
                           else:
                                try:
                                    fm = os.environ.get("XDG_CURRENT_DESKTOP")
                                    if fm and "gnome" in fm.lower(): subprocess.run(["nautilus", folder_path], check=True)
                                    elif fm and "kde" in fm.lower(): subprocess.run(["dolphin", folder_path], check=True)
                                    else: subprocess.run(["xdg-open", folder_path], check=True)
                                except FileNotFoundError: messagebox.showwarning("Lỗi", "Không thể mở thư mục. Lệnh mở thư mục không tìm thấy.", parent=self)
                                except subprocess.CalledProcessError as e: messagebox.showerror("Lỗi Mở Thư Mục", f"Lỗi khi chạy lệnh mở thư mục:\n{e}", parent=self)
                       else: messagebox.showerror("Lỗi", f"Thư mục không tồn tại:\n{folder_path}", parent=self)
                   except Exception as e: messagebox.showerror("Lỗi Mở Thư Mục", f"Đã xảy ra lỗi không mong muốn:\n{e}", parent=self)
              else: messagebox.showerror("Lỗi", "Không tìm thấy đường dẫn file.", parent=self)
         else: messagebox.showwarning("Chưa chọn", "Vui lòng chọn một download đã hoàn thành.", parent=self)
    def open_selected_file(self, task_id=None):
         target_task_id = task_id if task_id else self.selected_task_id
         if target_task_id:
              task_info = self.download_tasks.get(target_task_id)
              if task_info and task_info.get('output_path'):
                   file_path = task_info['output_path']
                   try:
                       if os.path.isfile(file_path):
                           print(f"Opening file: {file_path}")
                           system = platform.system()
                           if system == "Windows": os.startfile(file_path)
                           elif system == "Darwin": subprocess.run(["open", file_path], check=True)
                           else:
                                try: subprocess.run(["xdg-open", file_path], check=True)
                                except FileNotFoundError: messagebox.showwarning("Lỗi", "Không thể mở file. Lệnh xdg-open không tìm thấy.", parent=self)
                                except subprocess.CalledProcessError as e: messagebox.showerror("Lỗi Mở File", f"Lỗi khi chạy lệnh mở file:\n{e}", parent=self)
                       else: messagebox.showerror("Lỗi", f"File không tồn tại:\n{file_path}", parent=self)
                   except Exception as e: messagebox.showerror("Lỗi Mở File", f"Không thể mở file:\n{e}", parent=self)
              else: messagebox.showerror("Lỗi", "Không tìm thấy đường dẫn file.", parent=self)
         elif not task_id: messagebox.showwarning("Chưa chọn", "Vui lòng chọn download đã hoàn thành.", parent=self)
    def delete_selected_file(self):
        if self.selected_task_id:
            task_info = self.download_tasks.get(self.selected_task_id)
            if task_info and task_info.get('output_path'):
                file_path = task_info['output_path']; filename = task_info['filename']
                try:
                    if os.path.exists(file_path) and os.path.isfile(file_path):
                        if messagebox.askyesno("Xác nhận Xóa File", f"Bạn có chắc muốn XÓA VĨNH VIỄN file:\n{filename}\nkhỏi ổ đĩa? Hành động này không thể hoàn tác.", icon='warning', parent=self):
                            try:
                                os.remove(file_path); print(f"Deleted physical file: {file_path}")
                                messagebox.showinfo("Thành công", f"Đã xóa file: {filename}", parent=self)
                                self.update_action_buttons_state(self.selected_task_id)
                            except OSError as e: messagebox.showerror("Lỗi Xóa File", f"Không thể xóa file:\n{e}", parent=self)
                    else:
                         messagebox.showwarning("Không Tìm Thấy", f"File không còn tồn tại trên đĩa:\n{filename}", parent=self)
                         self.update_action_buttons_state(self.selected_task_id)
                except OSError as e: messagebox.showerror("Lỗi Hệ Thống File", f"Lỗi khi kiểm tra file:\n{e}", parent=self)
            else: messagebox.showerror("Lỗi", "Không tìm thấy đường dẫn file.", parent=self)
        else: messagebox.showwarning("Chưa chọn", "Vui lòng chọn mục để xóa file.", parent=self)
    def clear_finished_tasks(self):
         ids_to_remove = [task_id for task_id, info in self.download_tasks.items()
                          if info.get('status') in ['Hoàn thành', 'Đã hủy', 'Lỗi', "Hoàn thành (kích thước khác!)"]]
         if not ids_to_remove: messagebox.showinfo("Thông báo", "Không có mục nào đã hoàn thành/lỗi/hủy.", parent=self); return
         if messagebox.askyesno("Xác nhận Xóa", f"Xóa {len(ids_to_remove)} mục đã hoàn thành/lỗi/hủy khỏi danh sách?\n(File đã tải về sẽ không bị ảnh hưởng)", parent=self):
              print(f"Clearing {len(ids_to_remove)} finished/error/cancelled tasks from list.")
              selected_id_before = self.selected_task_id
              for task_id in ids_to_remove: self._remove_history_internal(task_id)
              if selected_id_before in ids_to_remove:
                  self.update_detailed_progress_ui(None); self.update_action_buttons_state(None)
              self.save_history()

    def create_context_menu(self):
        self.context_menu = tk.Menu(self, tearoff=0)
        self.context_menu.add_command(label="▶ Tiếp tục", command=self.context_resume)
        self.context_menu.add_command(label="⏸ Tạm dừng", command=self.context_pause)
        self.context_menu.add_command(label="❌ Hủy Download", command=self.context_cancel)
        self.context_menu.add_command(label="⚡ Giới hạn Tốc độ...", command=self.context_limit_speed)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="📂 Mở Thư mục Chứa File", command=self.context_open_folder)
        self.context_menu.add_command(label="🖱 Mở File", command=self.context_open_file)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="📋 Sao chép URL", command=self.context_copy_url)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="🧹 Xóa khỏi Danh sách", command=self.context_remove_history)
        self.context_menu.add_command(label="⛔ Xóa File và Khỏi Danh sách", command=self.context_delete_all)

    def show_context_menu(self, event):
        iid = self.tree.identify_row(event.y)
        if not iid: return
        if iid not in self.tree.selection():
            self.tree.selection_set(iid); self.tree.focus(iid)
            self.update_idletasks()
            self.on_tree_select()
        if not self.selected_task_id or self.selected_task_id != iid:
             print(f"Warning: Context menu target mismatch ({iid}) vs selected ({self.selected_task_id}). Aborting menu.")
             return
        task_info = self.download_tasks.get(self.selected_task_id)
        if not task_info: return

        status = task_info.get('status', ''); output_path = task_info.get('output_path', '')
        file_exists = os.path.exists(output_path) if output_path else False
        url_present = bool(task_info.get('url'))
        is_active_in_downloader = self.selected_task_id in self.downloader.active_downloads
        can_pause = status == 'Đang tải...' and is_active_in_downloader
        can_resume = status == 'Đã tạm dừng' and is_active_in_downloader
        can_cancel = status in ['Đang tải...', 'Đã tạm dừng', 'Bắt đầu...', 'Đang ghép file...'] and is_active_in_downloader
        can_limit_speed = status in ['Đang tải...', 'Đã tạm dừng'] and is_active_in_downloader
        can_open_folder = status in ['Hoàn thành', "Hoàn thành (kích thước khác!)"] and file_exists
        can_open_file = can_open_folder
        can_remove_history = status not in ['Đang tải...', 'Đang ghép file...', 'Đang hủy...']
        can_delete_all = file_exists and can_remove_history

        self.context_menu.entryconfig("▶ Tiếp tục", state=NORMAL if can_resume else DISABLED)
        self.context_menu.entryconfig("⏸ Tạm dừng", state=NORMAL if can_pause else DISABLED)
        self.context_menu.entryconfig("❌ Hủy Download", state=NORMAL if can_cancel else DISABLED)
        self.context_menu.entryconfig("⚡ Giới hạn Tốc độ...", state=NORMAL if can_limit_speed else DISABLED)
        self.context_menu.entryconfig("📂 Mở Thư mục Chứa File", state=NORMAL if can_open_folder else DISABLED)
        self.context_menu.entryconfig("🖱 Mở File", state=NORMAL if can_open_file else DISABLED)
        self.context_menu.entryconfig("📋 Sao chép URL", state=NORMAL if url_present else DISABLED)
        self.context_menu.entryconfig("🧹 Xóa khỏi Danh sách", state=NORMAL if can_remove_history else DISABLED)
        self.context_menu.entryconfig("⛔ Xóa File và Khỏi Danh sách", state=NORMAL if can_delete_all else DISABLED)

        try: self.context_menu.tk_popup(event.x_root, event.y_root)
        finally: self.context_menu.grab_release()

    def context_limit_speed(self):
        if not self.selected_task_id or self.selected_task_id not in self.download_tasks: return
        task_id = self.selected_task_id; task_info = self.download_tasks[task_id]
        current_limit_mbps = task_info.get('speed_limit_mbps', NO_LIMIT)
        prompt_default = current_limit_mbps if current_limit_mbps != NO_LIMIT else None
        if prompt_default is None and self.settings_manager.get("speed_limit_enabled"):
             prompt_default = self.settings_manager.get("speed_limit_mbps")
        new_limit = simpledialog.askfloat(
            "Giới hạn Tốc độ Task",
            f"Nhập tốc độ tối đa cho:\n'{task_info.get('filename', task_id)}'\n(MB/s, nhập 0 hoặc bỏ trống để bỏ giới hạn)",
            parent=self, minvalue=0.0, initialvalue=prompt_default
        )
        if new_limit is None: return
        limit_to_set = NO_LIMIT if new_limit <= 0 else new_limit
        if self.downloader.set_task_speed_limit(task_id, limit_to_set):
            task_info['speed_limit_mbps'] = limit_to_set
            self._update_detailed_status_label(task_id)
            print(f"Task {task_id} speed limit updated to: {limit_to_set} MB/s")
        else: print(f"Task {task_id} speed limit already set to {limit_to_set} MB/s. No change.")

    def context_pause(self): self.pause_selected_download()
    def context_resume(self): self.resume_selected_download()
    def context_cancel(self): self.cancel_selected_download()
    def context_open_folder(self): self.open_selected_folder()
    def context_open_file(self): self.open_selected_file()
    def context_copy_url(self):
        if self.selected_task_id:
            task_info = self.download_tasks.get(self.selected_task_id); url = task_info.get('url')
            if url:
                 try: self.clipboard_clear(); self.clipboard_append(url); print(f"Copied URL: {url}")
                 except tk.TclError: messagebox.showerror("Lỗi Clipboard", "Không thể truy cập clipboard.", parent=self)
            else: messagebox.showwarning("Thiếu URL", "Không tìm thấy URL để sao chép.", parent=self)
        else: messagebox.showwarning("Chưa chọn", "Vui lòng chọn mục trong danh sách.", parent=self)
    def context_remove_history(self):
        if self.selected_task_id:
            task_id = self.selected_task_id
            if task_id in self.download_tasks:
                filename = self.download_tasks[task_id].get('filename', 'Mục này')
                if messagebox.askyesno("Xác nhận", f"Xóa '{filename}' khỏi danh sách?\n(File đã tải về sẽ không bị xóa)", parent=self):
                    self._remove_history_internal(task_id); self.save_history()
            else: messagebox.showerror("Lỗi", "Không tìm thấy thông tin task.", parent=self)
        else: messagebox.showwarning("Chưa chọn", "Vui lòng chọn mục cần xóa.", parent=self)
    def context_delete_all(self):
        if self.selected_task_id:
            task_id = self.selected_task_id
            if task_id in self.download_tasks:
                task_info = self.download_tasks[task_id]; file_path = task_info.get('output_path'); filename = task_info.get('filename', 'File')
                should_remove_from_list = False
                try:
                    file_exists = file_path and os.path.exists(file_path) and os.path.isfile(file_path)
                    if file_exists:
                        if messagebox.askyesno("Xác nhận Xóa File", f"XÓA VĨNH VIỄN file:\n{filename}\nkhỏi ổ đĩa?", icon='warning', parent=self):
                            try: os.remove(file_path); print(f"Deleted file: {file_path}"); should_remove_from_list = True
                            except OSError as e: messagebox.showerror("Lỗi Xóa File", f"Không thể xóa file:\n{e}", parent=self); return
                        else: return
                    else:
                         if messagebox.askyesno("Xác nhận", f"File '{filename}' không tồn tại.\nXóa mục này khỏi danh sách?", parent=self): should_remove_from_list = True
                         else: return
                except OSError as e: messagebox.showerror("Lỗi Hệ Thống File", f"Lỗi khi kiểm tra file:\n{e}", parent=self); return
                if should_remove_from_list: self._remove_history_internal(task_id); self.save_history()
            else: messagebox.showerror("Lỗi", "Không tìm thấy thông tin task.", parent=self)
        else: messagebox.showwarning("Chưa chọn", "Vui lòng chọn mục cần xóa.", parent=self)

    def _remove_history_internal(self, task_id):
         if task_id in self.download_tasks:
             was_selected = (self.selected_task_id == task_id)
             try:
                 if self.tree.exists(task_id): self.tree.delete(task_id)
                 del self.download_tasks[task_id]
                 self.downloader._remove_task_limit(task_id)
                 if was_selected: self.update_detailed_progress_ui(None); self.update_action_buttons_state(None)
             except Exception as e:
                 print(f"Error removing task {task_id} from GUI: {e}")
                 if task_id in self.download_tasks: del self.download_tasks[task_id]
                 self.downloader._remove_task_limit(task_id)

    def apply_theme(self, event=None):
        selected_theme = self.theme_combobox.get(); print(f"Applying theme: {selected_theme}")
        try:
            self.style.theme_use(selected_theme); self.settings_manager.set("theme", selected_theme)
            self.tree.tag_configure('error', foreground='red'); self.tree.tag_configure('completed', foreground='gray'); self.tree.tag_configure('paused', foreground='blue')
            if self.selected_task_id: self._update_detailed_status_label(self.selected_task_id)
        except tk.TclError as e:
             messagebox.showerror("Lỗi Theme", f"Không thể áp dụng theme '{selected_theme}'.\n{e}", parent=self)
             try: self.theme_combobox.set(self.style.theme_use())
             except tk.TclError: pass

    def update_settings_ui(self):
        self.theme_combobox.set(self.settings_manager.get("theme"))
        self.threads_spinbox_var.set(self.settings_manager.get("num_threads"))
        self.save_path_var.set(self.settings_manager.get("download_dir"))
        self.speed_limit_enabled_var.set(self.settings_manager.get("speed_limit_enabled"))
        self.speed_limit_mbps_var.set(self.settings_manager.get("speed_limit_mbps"))
        self.toggle_speed_limit_entry()
        current_font = self.settings_manager.get("font_family")
        available_fonts = self.font_family_combobox['values']
        if current_font in available_fonts: self.font_family_combobox.set(current_font)
        else:
            default_font = DEFAULT_SETTINGS["font_family"]
            print(f"Warning: Saved font '{current_font}' not available. Using default '{default_font}'.")
            if default_font in available_fonts: self.font_family_combobox.set(default_font)
            elif available_fonts: self.font_family_combobox.set(available_fonts[0])
            else: self.font_family_combobox.set("")
            self.settings_manager.set("font_family", self.font_family_combobox.get())
        self.font_size_var.set(self.settings_manager.get("font_size"))
        self.win_w_var.set(self.settings_manager.get("window_width"))
        self.win_h_var.set(self.settings_manager.get("window_height"))

    def save_settings(self):
        try:
            settings_to_save = self.settings_manager.settings.copy()
            settings_to_save["theme"] = self.theme_combobox.get()
            settings_to_save["num_threads"] = self.threads_spinbox_var.get()
            settings_to_save["download_dir"] = os.path.normpath(self.save_path_var.get())
            limit_enabled = self.speed_limit_enabled_var.get()
            settings_to_save["speed_limit_enabled"] = limit_enabled
            if limit_enabled:
                try:
                    limit_mbps = self.speed_limit_mbps_var.get()
                    if limit_mbps <= 0:
                        messagebox.showwarning("Tốc độ không hợp lệ", "Tốc độ giới hạn phải > 0 MB/s.", parent=self)
                        self.speed_limit_mbps_var.set(self.settings_manager.get("speed_limit_mbps")); return
                    settings_to_save["speed_limit_mbps"] = limit_mbps
                except tk.TclError:
                    messagebox.showerror("Giá trị không hợp lệ", "Nhập giá trị số hợp lệ cho tốc độ.", parent=self)
                    self.speed_limit_mbps_var.set(self.settings_manager.get("speed_limit_mbps")); return
            else:
                 try: settings_to_save["speed_limit_mbps"] = self.speed_limit_mbps_var.get()
                 except tk.TclError: settings_to_save["speed_limit_mbps"] = self.settings_manager.get("speed_limit_mbps")
            settings_to_save["font_family"] = self.font_family_combobox.get()
            settings_to_save["font_size"] = self.font_size_var.get()
            win_w = self.win_w_var.get(); win_h = self.win_h_var.get()
            min_w, min_h = 700, 500
            settings_to_save["window_width"] = max(min_w, win_w)
            settings_to_save["window_height"] = max(min_h, win_h)
            if win_w < min_w or win_h < min_h:
                 messagebox.showwarning("Kích thước không hợp lệ", f"Kích thước cửa sổ tối thiểu là {min_w}x{min_h}.", parent=self)
                 self.win_w_var.set(settings_to_save["window_width"]); self.win_h_var.set(settings_to_save["window_height"])
            settings_to_save["detailed_pane_height"] = self.settings_manager.get("detailed_pane_height")

            self.settings_manager.save_settings(settings_to_save)
            self.apply_speed_limit_to_downloader()
            messagebox.showinfo("Đã Lưu Cài Đặt", "Cài đặt đã lưu.\nLưu ý: Font/Kích thước Cửa sổ cần khởi động lại.", parent=self)
        except ValueError as e: messagebox.showerror("Giá trị không hợp lệ", f"Vui lòng nhập giá trị số hợp lệ.\n{e}", parent=self)
        except tk.TclError as e: messagebox.showerror("Lỗi Lưu Cài Đặt", f"Lỗi Tcl/Tk:\n{e}", parent=self)
        except Exception as e: messagebox.showerror("Lỗi Lưu Cài Đặt", f"Lỗi không mong muốn:\n{e}", parent=self)

    def apply_speed_limit_to_downloader(self):
        enabled = self.settings_manager.get("speed_limit_enabled")
        limit_mbps = self.settings_manager.get("speed_limit_mbps")
        self.downloader.set_speed_limit(enabled, limit_mbps)

    def reset_settings(self):
        if messagebox.askyesno("Đặt lại Cài đặt?", "Đặt lại các cài đặt trên giao diện về mặc định?\n(Chưa lưu, nhấn 'Lưu Cài Đặt' để áp dụng)", parent=self):
             print("Resetting settings UI to defaults (not saved yet).")
             self.theme_combobox.set(DEFAULT_SETTINGS["theme"])
             self.threads_spinbox_var.set(DEFAULT_SETTINGS["num_threads"])
             self.save_path_var.set(DEFAULT_SETTINGS["download_dir"])
             self.speed_limit_enabled_var.set(DEFAULT_SETTINGS["speed_limit_enabled"])
             self.speed_limit_mbps_var.set(DEFAULT_SETTINGS["speed_limit_mbps"])
             self.toggle_speed_limit_entry()
             default_font = DEFAULT_SETTINGS["font_family"]; available_fonts = self.font_family_combobox['values']
             if default_font in available_fonts: self.font_family_combobox.set(default_font)
             elif available_fonts: self.font_family_combobox.set(available_fonts[0])
             else: self.font_family_combobox.set("")
             self.font_size_var.set(DEFAULT_SETTINGS["font_size"])
             self.win_w_var.set(DEFAULT_SETTINGS["window_width"])
             self.win_h_var.set(DEFAULT_SETTINGS["window_height"])

    def format_size(self, size_bytes):
        if size_bytes is None or not isinstance(size_bytes, (int, float)) or size_bytes < 0: return "N/A"
        if size_bytes == 0: return "0 B"
        size_name = ("B", "KB", "MB", "GB", "TB"); i = 0
        try: i = min(len(size_name) - 1, int(math.floor(math.log(max(1, abs(size_bytes)), 1024))))
        except ValueError: pass
        p = math.pow(1024, i); s = size_bytes / p
        precision = 1 if i > 0 else 0
        return f"{s:.{precision}f} {size_name[i]}"

    def format_speed(self, speed_bytes_sec):
        if speed_bytes_sec is None or not isinstance(speed_bytes_sec, (int, float)) or speed_bytes_sec < 0: return "-"
        if speed_bytes_sec < 1: return "0 B/s"
        size_name = ("B/s", "KB/s", "MB/s", "GB/s", "TB/s"); i = 0
        try: i = min(len(size_name) - 1, int(math.floor(math.log(max(1, speed_bytes_sec), 1024))))
        except ValueError: pass
        p = math.pow(1024, i); s = speed_bytes_sec / p
        precision = 1
        return f"{s:.{precision}f} {size_name[i]}"

    def format_time(self, seconds, short=False):
        if seconds is None or not isinstance(seconds, (int, float)) or seconds == float('inf') or seconds < 0: return "-"
        try:
             seconds = int(seconds)
             if seconds < 60: return f"{seconds}s"
             elif seconds < 3600: m, s = divmod(seconds, 60); return f"{m}m{s:01d}s" if short else f"{m:d}m {s:02d}s"
             else: h, remainder = divmod(seconds, 3600); m, s = divmod(remainder, 60); return f"{h}h{m:01d}m" if short else f"{h:d}h {m:02d}m {s:02d}s"
        except (ValueError, TypeError): return "-"

    def load_history(self):
        print(f"Loading history from {HISTORY_FILE}...")
        loaded_count = 0; max_stt = 0
        history_items_to_add = []
        try:
            if not os.path.exists(HISTORY_FILE): print("History file not found. Starting fresh."); return
            with open(HISTORY_FILE, 'r', encoding='utf-8') as f: history_data = json.load(f)
            if not isinstance(history_data, list): print(f"History file format error. Starting fresh."); return
            for task_data in history_data:
                required_keys = ['task_id', 'stt', 'filename', 'total_size', 'output_path', 'status', 'url']
                if not isinstance(task_data, dict) or not all(k in task_data for k in required_keys): continue
                task_id = task_data['task_id']
                if task_id in self.download_tasks: continue
                try:
                    stt = int(task_data['stt']); filename = str(task_data['filename'])
                    total_size = int(task_data['total_size']); output_path = str(task_data['output_path'])
                    status = str(task_data['status']); url = str(task_data['url'])
                    speed_limit_mbps = float(task_data.get('speed_limit_mbps', NO_LIMIT))
                    if speed_limit_mbps <= 0 : speed_limit_mbps = NO_LIMIT
                    if stt <= 0 or total_size < 0 or not filename or not output_path or not status or not url: raise ValueError("Invalid data")
                except (ValueError, TypeError) as e: continue
                values = (stt, filename, '-', self.format_size(total_size), status, '-')
                tag = ()
                if status == 'Lỗi': tag = ('error',)
                elif status in ['Hoàn thành', 'Hoàn thành (kích thước khác!)', 'Đã hủy']: tag = ('completed',)
                history_items_to_add.append({'task_id': task_id, 'values': values, 'tag': tag, 'stt': stt, 'filename': filename, 'total_size': total_size, 'output_path': output_path, 'status': status, 'url': url, 'speed_limit_mbps': speed_limit_mbps})
                max_stt = max(max_stt, stt)

            history_items_to_add.sort(key=lambda x: x['stt'])
            for item_info in history_items_to_add:
                task_id = item_info['task_id']
                try:
                    item_id = self.tree.insert('', 'end', iid=task_id, values=item_info['values'], tags=item_info['tag'])
                    self.download_tasks[task_id] = {'item_id': item_id, 'task_id': task_id, 'stt': item_info['stt'], 'filename': item_info['filename'], 'total_size': item_info['total_size'], 'output_path': item_info['output_path'], 'status': item_info['status'], 'url': item_info['url'], 'speed_limit_mbps': item_info['speed_limit_mbps']}
                    loaded_count += 1
                except tk.TclError as e:
                     print(f"Error inserting history item {task_id}: {e}")
                     if task_id in self.download_tasks: del self.download_tasks[task_id]
            self.task_stt_counter = max_stt
            print(f"Loaded {loaded_count} history items. Next STT: {self.task_stt_counter + 1}")
        except json.JSONDecodeError as e: print(f"Error decoding history file {HISTORY_FILE}: {e}. Starting fresh.")
        except Exception as e: print(f"Error loading history: {e}"); import traceback; traceback.print_exc()

    def save_history(self):
        if not self.download_tasks: print("No tasks to save."); return
        print(f"Saving history to {HISTORY_FILE}...")
        history_to_save = []; saved_count = 0
        tasks_to_consider = sorted(self.download_tasks.values(), key=lambda x: x.get('stt', float('inf')))
        for task_info in tasks_to_consider:
            status = task_info.get('status')
            final_states = ['Hoàn thành', 'Lỗi', 'Đã hủy', 'Hoàn thành (kích thước khác!)']
            if status in final_states:
                required_keys = ['task_id', 'stt', 'filename', 'total_size', 'output_path', 'status', 'url']
                optional_keys = ['speed_limit_mbps']
                if all(key in task_info and task_info[key] is not None for key in required_keys):
                    entry = {key: task_info[key] for key in required_keys}
                    for key in optional_keys:
                        if key in task_info and task_info[key] != NO_LIMIT: entry[key] = task_info[key]
                    history_to_save.append(entry); saved_count += 1
                else:
                    missing = [k for k in required_keys if k not in task_info or task_info[k] is None]
                    print(f"Skipping saving task {task_info.get('task_id','N/A')} due to missing keys: {missing}")
        try:
            with open(HISTORY_FILE, 'w', encoding='utf-8') as f: json.dump(history_to_save, f, indent=4, ensure_ascii=False)
            print(f"Saved {saved_count} history items.")
        except IOError as e: print(f"Error saving history: {e}"); messagebox.showerror("Lỗi Lưu Lịch Sử", f"Không thể lưu lịch sử:\n{e}", parent=self)
        except Exception as e: print(f"Unexpected error saving history: {e}"); messagebox.showerror("Lỗi Lưu Lịch Sử", f"Lỗi không mong muốn:\n{e}", parent=self)

    def on_window_configure(self, event=None):
        if hasattr(self, 'detailed_progress_frame') and self.detailed_progress_frame.winfo_exists() \
           and event and event.widget == self:
            try:
                 detail_height = self.detailed_progress_frame.winfo_height()
                 if detail_height > 30:
                      current_setting = self.settings_manager.get("detailed_pane_height")
                      if abs(detail_height - current_setting) > 5:
                          self.settings_manager.set("detailed_pane_height", detail_height)
            except (tk.TclError, ValueError, AttributeError) as e: pass

    def on_closing(self):
        active_count = len(self.downloader.active_downloads)
        can_close = True
        if active_count > 0:
            msg = f"Có {active_count} download đang chạy/tạm dừng.\nThoát bây giờ sẽ hủy các download này.\n\nBạn chắc chắn muốn thoát?"
            can_close = messagebox.askyesno("Xác nhận Thoát", msg, icon='warning', parent=self)
        if can_close:
            print("Closing application...")
            if hasattr(self, '_queue_processor_after_id') and self._queue_processor_after_id:
                try: self.after_cancel(self._queue_processor_after_id)
                except tk.TclError: pass
                self._queue_processor_after_id = None

            self.on_window_configure(event=None)
            self.settings_manager.save_settings()

            self.downloader.shutdown()
            self.save_history()
            print("Checking for global cache directory cleanup...")
            try:
                download_dir = self.settings_manager.get("download_dir")
                temp_base_dir = os.path.join(download_dir, DEFAULT_TEMP_DIR_NAME)
                if os.path.isdir(temp_base_dir):
                    if not os.listdir(temp_base_dir):
                        try: os.rmdir(temp_base_dir); print(f"Removed empty global cache directory: {temp_base_dir}")
                        except OSError as e: print(f"Could not remove empty global cache directory {temp_base_dir}: {e}")
                    else: print(f"Global cache directory not empty, leaving it: {temp_base_dir}")
                else: print("Global cache directory does not exist.")
            except Exception as e: print(f"Error during global cache cleanup: {e}")
            print("Destroying main window.")
            self.destroy()
        else: print("Close cancelled by user.")

class ToolTip:
    def __init__(self, widget, text):
        self.widget = widget; self.text = text; self.tooltip = None; self.id = None
        self.waittime = 500; self.wraplength = 250
        self.widget.bind("<Enter>", self.enter); self.widget.bind("<Leave>", self.leave); self.widget.bind("<ButtonPress>", self.leave)
    def enter(self, event=None): self.schedule()
    def leave(self, event=None): self.unschedule(); self.hidetip()
    def schedule(self):
        self.unschedule()
        if self.widget.winfo_exists():
            try: self.id = self.widget.after(self.waittime, self.showtip)
            except tk.TclError: pass
    def unschedule(self):
        id_to_cancel = self.id; self.id = None
        if id_to_cancel:
            try:
                if self.widget.winfo_exists(): self.widget.after_cancel(id_to_cancel)
            except tk.TclError: pass
    def showtip(self, event=None):
        if self.tooltip or not self.text: return
        try:
            if not self.widget.winfo_exists(): return
        except tk.TclError: return
        try:
             x, y, cx, cy = self.widget.bbox("insert"); x += self.widget.winfo_rootx() + 25; y += self.widget.winfo_rooty() + 20
        except tk.TclError:
             try: x = self.widget.winfo_rootx() + self.widget.winfo_width() // 2; y = self.widget.winfo_rooty() + self.widget.winfo_height() + 5
             except tk.TclError: return
        try:
            self.tooltip = tk.Toplevel(self.widget); self.tooltip.wm_overrideredirect(True); self.tooltip.wm_geometry(f"+{x}+{y}")
        except tk.TclError: self.tooltip = None; return
        try:
            label = ttk.Label(self.tooltip, text=self.text, justify='left', relief='solid', borderwidth=1, wraplength = self.wraplength, anchor='w', padding=(5,3), style='tooltip.TLabel')
            try:
                 s = ttk.Style(); s.configure('tooltip.TLabel', background="#ffffe0", foreground="black")
            except tk.TclError: label.config(background="#ffffe0", foreground="black")
        except tk.TclError:
             label = tk.Label(self.tooltip, text=self.text, justify='left', background="#ffffe0", foreground="black", relief='solid', borderwidth=1, wraplength = self.wraplength, anchor='w', padx=5, pady=3)
        label.pack(ipadx=1)
    def hidetip(self):
        tooltip_to_destroy = self.tooltip; self.tooltip = None
        if tooltip_to_destroy:
            try:
                if tooltip_to_destroy.winfo_exists(): tooltip_to_destroy.destroy()
            except tk.TclError: pass

if __name__ == "__main__":
    settings_mgr = SettingsManager()
    app = DownloadManagerApp(settings_mgr)
    app.mainloop()