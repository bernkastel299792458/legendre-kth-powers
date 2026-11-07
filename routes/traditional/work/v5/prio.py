"""Keep this process (and pool workers that import it) polite on the user's machine:
Windows IDLE priority, and pinned to the last NPROC logical CPUs (1/4 of the machine by default).
Pool sizes use NPROC.  Override with the environment variable LEGENDRE_NPROC."""
import os
import sys

NCPU = os.cpu_count() or 4
NPROC = max(1, min(NCPU, int(os.environ.get('LEGENDRE_NPROC', max(1, NCPU // 4)))))

if sys.platform == 'win32':
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.windll.kernel32
        k32.GetCurrentProcess.restype = wintypes.HANDLE
        k32.SetPriorityClass.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        k32.SetPriorityClass.restype = wintypes.BOOL
        k32.SetPriorityClass(k32.GetCurrentProcess(), 0x00000040)
        k32.SetProcessAffinityMask.argtypes = [wintypes.HANDLE, ctypes.c_size_t]
        k32.SetProcessAffinityMask.restype = wintypes.BOOL
        mask = ((1 << NPROC) - 1) << (NCPU - NPROC)
        k32.SetProcessAffinityMask(k32.GetCurrentProcess(), mask)
    except Exception:
        pass
