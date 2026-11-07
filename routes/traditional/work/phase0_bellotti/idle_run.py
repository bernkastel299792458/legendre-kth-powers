"""Run a script of this folder at IDLE priority (Windows), e.g.  python idle_run.py v4.py shard 0 4 350 600
(the coordinator asked that every worker runs at idle priority and at most 4 run at once)."""
import sys, os, runpy
if os.name == 'nt':
    import ctypes
    from ctypes import wintypes
    IDLE_PRIORITY_CLASS = 0x40
    k32 = ctypes.WinDLL('kernel32', use_last_error=True)
    k32.GetCurrentProcess.restype = wintypes.HANDLE
    k32.SetPriorityClass.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    k32.SetPriorityClass.restype = wintypes.BOOL
    if not k32.SetPriorityClass(k32.GetCurrentProcess(), IDLE_PRIORITY_CLASS):
        sys.stderr.write(f"idle_run: SetPriorityClass failed ({ctypes.get_last_error()})\n")
target = sys.argv[1]
sys.argv = sys.argv[1:]
sys.path.insert(0, os.path.dirname(os.path.abspath(target)))
runpy.run_path(target, run_name='__main__')
